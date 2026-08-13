import type { Diagram, Endpoint, WireId } from '../diagram/diagram'
import type { DiagramIso } from '../diagram/canonical/explore'
import { exploreIso } from '../diagram/canonical/explore'
import type { OccurrenceCertificate } from '../diagram/subgraph/occurrence-certificate'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
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
    case 'wireJoin':
      return {
        ...step,
        input: {
          a: mapId(iso.wires, step.input.a, 'wire'),
          b: mapId(iso.wires, step.input.b, 'wire'),
        },
      }
    case 'erasure':
      return { ...step, sel: mapSelection(iso, step.sel) }
    case 'wireSever':
      return {
        ...step,
        input: {
          ...step.input,
          wire: mapId(iso.wires, step.input.wire, 'wire'),
          keep: step.input.keep.map((endpoint) =>
            mapEndpoint(iso, endpoint)),
          ...(step.input.scope !== undefined
            ? { scope: mapId(iso.regions, step.input.scope, 'region') }
            : {}),
        },
      }
    case 'iteration':
      return {
        ...step,
        sel: mapSelection(iso, step.sel),
        target: mapId(iso.regions, step.target, 'region'),
      }
    case 'deiteration':
      return {
        ...step,
        sel: mapSelection(iso, step.sel),
        justifier: mapSelection(iso, step.justifier),
        certificate: mapOccurrenceCertificate(iso, step.certificate),
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
    case 'vacuity': {
      // Insert-direction node/wire ids are mint labels (absent at the meet)
      // and pass through; delete-direction ids are real and must map.
      const maybeNode = (id: string): string =>
        step.direction === 'delete' ? mapId(iso.nodes, id, 'node') : id
      const maybeWire = (id: string): string =>
        step.direction === 'delete' ? mapId(iso.wires, id, 'wire') : id
      const endpoint = (ep: { node: string; port: Endpoint['port'] }): Endpoint =>
        step.assembly.nodes[ep.node] !== undefined
          ? { node: maybeNode(ep.node), port: ep.port }
          : { node: mapId(iso.nodes, ep.node, 'node'), port: ep.port }
      return {
        ...step,
        assembly: {
          nodes: Object.fromEntries(
            Object.entries(step.assembly.nodes).map(([id, node]) => [
              maybeNode(id),
              { ...node, region: mapId(iso.regions, node.region, 'region') },
            ]),
          ),
          wires: Object.fromEntries(
            Object.entries(step.assembly.wires).map(([id, wire]) => [
              maybeWire(id),
              { sig: wire.sig, endpoints: wire.endpoints.map(endpoint) },
            ]),
          ),
          attachments: Object.fromEntries(
            Object.entries(step.assembly.attachments).map(([id, endpoints]) => [
              mapId(iso.wires, id, 'wire'),
              endpoints.map(endpoint),
            ]),
          ),
        },
      }
    }
    case 'presentation':
      return {
        ...step,
        input: {
          region: mapId(iso.regions, step.input.region, 'region'),
          removeNodes: step.input.removeNodes.map((node) =>
            mapId(iso.nodes, node, 'node')),
          addNodes: Object.fromEntries(
            Object.entries(step.input.addNodes).map(([label, ports]) => [
              label,
              ports.map((wire) => mapId(iso.wires, wire, 'wire')),
            ]),
          ),
        },
      }
    case 'identification':
      return {
        ...step,
        input: step.input.kind === 'collapse'
          ? {
              kind: 'collapse',
              node: mapId(iso.nodes, step.input.node, 'node'),
              survivor: mapId(iso.wires, step.input.survivor, 'wire'),
              absorbed: step.input.absorbed.map((wire) =>
                mapId(iso.wires, wire, 'wire')),
            }
          : {
              kind: 'expose',
              node: mapId(iso.nodes, step.input.node, 'node'),
              survivor: mapId(iso.wires, step.input.survivor, 'wire'),
              freshWire: step.input.freshWire,
              transfer: step.input.transfer.map((endpoint) =>
                mapEndpoint(iso, endpoint)),
            },
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
    case 'cutWrap':
    case 'cutAbsorb':
    case 'parallelSplit':
    case 'endsDelete':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
      }
    case 'parallelFuse':
      return {
        ...step,
        a: mapId(iso.wires, step.a, 'wire'),
        b: mapId(iso.wires, step.b, 'wire'),
      }
    case 'endsSpawn':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
        sites: step.sites.map((site) => ({
          region: mapId(iso.regions, site.region, 'region'),
          args: site.args.map((wire) => mapId(iso.wires, wire, 'wire')),
        })),
      }
    case 'arityShift':
    case 'arityUnshift':
    case 'argPermute':
    case 'argDuplicate':
    case 'argContract':
    case 'argDrop':
    case 'applyFormal':
    case 'identityLeaf':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
      }
    case 'argExtend':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
        attachments: Object.fromEntries(
          Object.entries(step.attachments).map(([node, wire]) => [
            mapId(iso.nodes, node, 'node'),
            mapId(iso.wires, wire, 'wire'),
          ]),
        ),
      }
    case 'abstractFormal':
      return {
        ...step,
        ends: step.ends.map((node) => mapId(iso.nodes, node, 'node')),
        scope: mapId(iso.regions, step.scope, 'region'),
      }
    case 'identityAbstract':
    case 'refAbstract':
      return {
        ...step,
        nodes: step.nodes.map((node) => mapId(iso.nodes, node, 'node')),
        scope: mapId(iso.regions, step.scope, 'region'),
      }
    case 'refLeaf':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
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
