import type { Diagram, Endpoint, WireId } from '../diagram/diagram'
import type { DiagramIso } from '../diagram/canonical/explore'
import { exploreIso } from '../diagram/canonical/explore'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { IdentityRetarget } from '../rules/iteration'
import { allocationReservation, type ProofAction } from './action'
import { assertProofContext, type ProofContext } from './context'
import { ProofError } from './error'
import {
  applyStepWithReceipt,
  transportBoundary,
  type ProofStep,
} from './step'

export type CompositionBoundaries = {
  readonly target: readonly WireId[]
  readonly source: readonly WireId[]
}

export type CompositionOptions = {
  readonly boundaries?: CompositionBoundaries
  readonly orientation?: 'forward' | 'backward'
}

function mapId<T extends string>(
  map: ReadonlyMap<string, string>,
  id: T,
  what: string,
): T {
  const image = map.get(id)
  if (image === undefined) {
    throw new ProofError(
      `composition cannot map ${what} '${id}': not present at the meet`,
    )
  }
  return image as T
}

function mapSelection(
  iso: DiagramIso,
  selection: SubgraphSelection,
): SubgraphSelection {
  return {
    region: mapId(iso.regions, selection.region, 'region'),
    regions: selection.regions.map((region) =>
      mapId(iso.regions, region, 'region')),
    nodes: selection.nodes.map((node) =>
      mapId(iso.nodes, node, 'node')),
    wires: selection.wires.map((wire) =>
      mapId(iso.wires, wire, 'wire')),
  }
}

function mapEndpoint(iso: DiagramIso, endpoint: Endpoint): Endpoint {
  return {
    node: mapId(iso.nodes, endpoint.node, 'node'),
    port: endpoint.port,
  }
}

function mapRetarget(
  iso: DiagramIso,
  retarget: IdentityRetarget,
): IdentityRetarget {
  return {
    boundary: retarget.boundary,
    identity: mapId(iso.nodes, retarget.identity, 'node'),
    from: mapId(iso.wires, retarget.from, 'wire'),
    to: mapId(iso.wires, retarget.to, 'wire'),
  }
}

function mapOccurrenceCertificate(
  iso: DiagramIso,
  certificate: OccurrenceCertificate,
): OccurrenceCertificate {
  return {
    region: mapId(iso.regions, certificate.region, 'region'),
    regionMap: new Map([...certificate.regionMap].map(([pattern, host]) => [
      pattern,
      mapId(iso.regions, host, 'region'),
    ])),
    nodeMap: new Map([...certificate.nodeMap].map(([pattern, host]) => [
      pattern,
      mapId(iso.nodes, host, 'node'),
    ])),
    wireMap: new Map([...certificate.wireMap].map(([pattern, host]) => [
      pattern,
      mapId(iso.wires, host, 'wire'),
    ])),
    attachments: certificate.attachments.map((wire) =>
      mapId(iso.wires, wire, 'wire')),
  }
}

/** Rewrite every host identifier in one durable proof primitive. */
export function mapStepIds(step: ProofStep, iso: DiagramIso): ProofStep {
  switch (step.rule) {
    case 'refSpawn':
      return {
        ...step,
        region: mapId(iso.regions, step.region, 'region'),
      }
    case 'atomSpawn':
      return {
        ...step,
        region: mapId(iso.regions, step.region, 'region'),
        wire: mapId(iso.wires, step.wire, 'wire'),
      }
    case 'identityInsert':
      return {
        ...step,
        region: mapId(iso.regions, step.region, 'region'),
        wires: step.wires.map((wire) =>
          mapId(iso.wires, wire, 'wire')),
      }
    case 'identityContradiction':
      return {
        ...step,
        enclosingCut: mapId(
          iso.regions,
          step.enclosingCut,
          'region',
        ),
        evidence: {
          equality: mapId(
            iso.nodes,
            step.evidence.equality,
            'node',
          ),
          disequalityCut: mapId(
            iso.regions,
            step.evidence.disequalityCut,
            'region',
          ),
          disequality: mapId(
            iso.nodes,
            step.evidence.disequality,
            'node',
          ),
        },
      }
    case 'wireJoin':
      return {
        ...step,
        a: mapId(iso.wires, step.a, 'wire'),
        b: mapId(iso.wires, step.b, 'wire'),
      }
    case 'erasure':
      return { ...step, sel: mapSelection(iso, step.sel) }
    case 'wireSever':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
        keep: step.keep.map((endpoint) => mapEndpoint(iso, endpoint)),
      }
    case 'iteration':
      return {
        ...step,
        sel: mapSelection(iso, step.sel),
        target: mapId(iso.regions, step.target, 'region'),
        retargets: step.retargets.map((retarget) =>
          mapRetarget(iso, retarget)),
      }
    case 'deiteration':
      return {
        ...step,
        sel: mapSelection(iso, step.sel),
        justifier: mapSelection(iso, step.justifier),
        certificate: mapOccurrenceCertificate(iso, step.certificate),
        retargets: step.retargets.map((retarget) =>
          mapRetarget(iso, retarget)),
      }
    case 'doubleCutIntro':
      return { ...step, sel: mapSelection(iso, step.sel) }
    case 'doubleCutElim':
      return {
        ...step,
        region: mapId(iso.regions, step.region, 'region'),
      }
    case 'theorem':
      return {
        ...step,
        at: {
          sel: mapSelection(iso, step.at.sel),
          args: step.at.args.map((wire) =>
            mapId(iso.wires, wire, 'wire')),
        },
      }
    case 'vacuousIntro':
      return {
        ...step,
        scope: mapId(iso.regions, step.scope, 'region'),
      }
    case 'vacuousElim':
      return {
        ...step,
        wireId: mapId(iso.wires, step.wireId, 'wire'),
      }
    case 'unfold':
      return {
        ...step,
        nodeId: mapId(iso.nodes, step.nodeId, 'node'),
      }
    case 'fold':
      return {
        ...step,
        occurrence: mapSelection(iso, step.occurrence),
        args: step.args.map((wire) =>
          mapId(iso.wires, wire, 'wire')),
      }
  }
}

/**
 * Transplant a recorded tail across an isomorphic meet, re-deriving the
 * identifier isomorphism after every normalized primitive receipt.
 */
export function composeActions(
  meetTarget: Diagram,
  meetSource: Diagram,
  tail: readonly ProofAction[],
  context: ProofContext,
  options: CompositionOptions = {},
): ProofAction[] {
  assertProofContext(context)
  const boundaries = options.boundaries ?? { target: [], source: [] }
  const orientation = options.orientation ?? 'forward'
  if (boundaries.source.length !== boundaries.target.length) {
    throw new ProofError(
      `the two sides do not meet: boundary arity differs `
      + `(source ${boundaries.source.length}, `
      + `target ${boundaries.target.length})`,
    )
  }

  let sourceBoundary = boundaries.source
  let targetBoundary = boundaries.target
  let iso = exploreIso(
    meetSource,
    meetTarget,
    sourceBoundary,
    targetBoundary,
  )
  if (iso === null) {
    throw new ProofError(
      'the two sides do not meet: the diagrams or ordered boundaries '
      + 'are not isomorphic',
    )
  }

  let currentTarget = meetTarget
  let currentSource = meetSource
  const output: ProofAction[] = []
  for (const [actionIndex, action] of tail.entries()) {
    const reservation = allocationReservation(action.allocation)
    const mappedSteps: ProofStep[] = []
    for (const [stepIndex, step] of action.steps.entries()) {
      const mapped = mapStepIds(step, iso)
      mappedSteps.push(mapped)
      try {
        const targetReceipt = applyStepWithReceipt(
          currentTarget,
          mapped,
          context,
          orientation,
          reservation,
        )
        const sourceReceipt = applyStepWithReceipt(
          currentSource,
          step,
          context,
          orientation,
          reservation,
        )
        const nextTargetBoundary = transportBoundary(
          targetReceipt.interface,
          targetBoundary,
        )
        const nextSourceBoundary = transportBoundary(
          sourceReceipt.interface,
          sourceBoundary,
        )
        if (
          nextTargetBoundary === undefined
          || nextSourceBoundary === undefined
        ) {
          const failures: string[] = []
          if (nextTargetBoundary === undefined) {
            const position = targetBoundary.findIndex((wire) =>
              targetReceipt.interface.image(wire) === undefined)
            failures.push(
              `target boundary position ${position} has no semantic image`,
            )
          }
          if (nextSourceBoundary === undefined) {
            const position = sourceBoundary.findIndex((wire) =>
              sourceReceipt.interface.image(wire) === undefined)
            failures.push(
              `source boundary position ${position} has no semantic image`,
            )
          }
          throw new ProofError(failures.join('; '))
        }
        currentTarget = targetReceipt.result
        currentSource = sourceReceipt.result
        targetBoundary = nextTargetBoundary
        sourceBoundary = nextSourceBoundary
      } catch (error) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} `
          + `(${step.rule}) failed: `
          + `${error instanceof Error ? error.message : String(error)}`,
        )
      }

      iso = exploreIso(
        currentSource,
        currentTarget,
        sourceBoundary,
        targetBoundary,
      )
      if (iso === null) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} `
          + `(${step.rule}) diverged: the sides are no longer isomorphic`,
        )
      }
    }
    output.push({
      label: action.label,
      steps: mappedSteps,
      placements: action.placements,
      ...(action.allocation === undefined
        ? {}
        : { allocation: action.allocation }),
    })
  }
  return output
}
