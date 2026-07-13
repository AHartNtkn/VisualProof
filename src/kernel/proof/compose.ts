import type { Diagram, Endpoint, WireId } from '../diagram/diagram'
import type { DiagramIso } from '../diagram/canonical/explore'
import { exploreIso } from '../diagram/canonical/explore'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import type { AbstractionOccurrence } from '../rules/comprehension'
import type { ProofContext, ProofStep } from './step'
import { applyStep } from './step'
import { allocationReservation, type ProofAction } from './action'
import { ProofError } from './error'

function mapId<T extends string>(m: ReadonlyMap<string, string>, id: T, what: string): T {
  const img = m.get(id)
  if (img === undefined) throw new ProofError(`composition cannot map ${what} '${id}': not present at the meet`)
  return img as T
}

function mapSel(iso: DiagramIso, sel: SubgraphSelection): SubgraphSelection {
  return {
    region: mapId(iso.regions, sel.region, 'region'),
    regions: sel.regions.map((r) => mapId(iso.regions, r, 'region')),
    nodes: sel.nodes.map((n) => mapId(iso.nodes, n, 'node')),
    wires: sel.wires.map((w) => mapId(iso.wires, w, 'wire')),
  }
}

function mapEndpoint(iso: DiagramIso, ep: Endpoint): Endpoint {
  return { node: mapId(iso.nodes, ep.node, 'node'), port: ep.port }
}

function mapOccurrence(iso: DiagramIso, occ: AbstractionOccurrence): AbstractionOccurrence {
  return { sel: mapSel(iso, occ.sel), args: occ.args.map((w) => mapId(iso.wires, w, 'wire')) }
}

/**
 * Rewrite one step's HOST ids through an isomorphism. Embedded patterns
 * (DiagramWithBoundary values) are self-contained namespaces and terms are
 * port-name-internal — neither is mapped.
 */
export function mapStepIds(step: ProofStep, iso: DiagramIso): ProofStep {
  switch (step.rule) {
    case 'openTermSpawn':
    case 'relationSpawn':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'boundRelationSpawn':
      return { ...step, region: mapId(iso.regions, step.region, 'region'), binder: mapId(iso.regions, step.binder, 'region') }
    case 'wireJoin':
      return { ...step, a: mapId(iso.wires, step.a, 'wire'), b: mapId(iso.wires, step.b, 'wire') }
    case 'erasure':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'wireSever':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire'), keep: step.keep.map((ep) => mapEndpoint(iso, ep)) }
    case 'iteration':
      return { ...step, sel: mapSel(iso, step.sel), target: mapId(iso.regions, step.target, 'region') }
    case 'deiteration':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'doubleCutIntro':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'doubleCutElim':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'conversion': {
      const attachments: Record<string, WireId> = {}
      for (const [name, w] of Object.entries(step.attachments)) attachments[name] = mapId(iso.wires, w, 'wire')
      return { ...step, node: mapId(iso.nodes, step.node, 'node'), attachments }
    }
    case 'congruenceJoin':
      return { ...step, a: mapId(iso.nodes, step.a, 'node'), b: mapId(iso.nodes, step.b, 'node') }
    case 'anchoredWireSplit':
      return {
        ...step,
        wire: mapId(iso.wires, step.wire, 'wire'),
        witness: mapId(iso.nodes, step.witness, 'node'),
        endpoints: step.endpoints.map((endpoint) => mapEndpoint(iso, endpoint)),
        target: mapId(iso.regions, step.target, 'region'),
      }
    case 'anchoredWireContract':
      return {
        ...step,
        redundant: mapId(iso.nodes, step.redundant, 'node'),
        survivor: mapId(iso.nodes, step.survivor, 'node'),
      }
    case 'headStrip':
      return { ...step, a: mapId(iso.nodes, step.a, 'node'), b: mapId(iso.nodes, step.b, 'node') }
    case 'closedTermIntro':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'fusion':
      return { ...step, wire: mapId(iso.wires, step.wire, 'wire') }
    case 'fission':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'comprehensionInstantiate': {
      const binders: Record<string, string> = {}
      for (const [stub, hb] of Object.entries(step.binders)) binders[stub] = mapId(iso.regions, hb, 'region')
      return {
        ...step,
        bubble: mapId(iso.regions, step.bubble, 'region'),
        attachments: step.attachments.map((w) => mapId(iso.wires, w, 'wire')),
        binders,
      }
    }
    case 'comprehensionAbstract':
      return { ...step, wrap: mapSel(iso, step.wrap), occurrences: step.occurrences.map((o) => mapOccurrence(iso, o)) }
    case 'theorem':
      return { ...step, at: { sel: mapSel(iso, step.at.sel), args: step.at.args.map((w) => mapId(iso.wires, w, 'wire')) } }
    case 'vacuousIntro':
      return { ...step, sel: mapSel(iso, step.sel) }
    case 'vacuousElim':
      return { ...step, region: mapId(iso.regions, step.region, 'region') }
    case 'relUnfold':
      return { ...step, node: mapId(iso.nodes, step.node, 'node') }
    case 'relFold':
      return { ...step, sel: mapSel(iso, step.sel), args: step.args.map((w) => mapId(iso.wires, w, 'wire')) }
  }
}

/**
 * Meet-in-the-middle: transplant a tail of actions recorded against
 * `meetSource` onto the isomorphic `meetTarget`. Fresh ids minted during
 * replay depend on the id environment, so a single up-front rewrite cannot
 * work — instead the isomorphism is re-derived from canonical labelings
 * after every step (appliers are iso-equivariant up to fresh-id choice).
 */
export function composeActions(
  meetTarget: Diagram,
  meetSource: Diagram,
  tail: readonly ProofAction[],
  ctx: ProofContext,
): ProofAction[] {
  let iso = exploreIso(meetSource, meetTarget)
  if (iso === null) throw new ProofError('the two sides do not meet: the diagrams are not isomorphic')
  let curTarget = meetTarget
  let curSource = meetSource
  const out: ProofAction[] = []
  for (const [actionIndex, action] of tail.entries()) {
    const reservation = allocationReservation(action.allocation)
    const mappedSteps: ProofStep[] = []
    for (const [stepIndex, step] of action.steps.entries()) {
      const mapped = mapStepIds(step, iso)
      mappedSteps.push(mapped)
      try {
        curTarget = applyStep(curTarget, mapped, ctx, 'forward', reservation)
        curSource = applyStep(curSource, step, ctx, 'forward', reservation)
      } catch (e) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} (${step.rule}) failed: ${e instanceof Error ? e.message : String(e)}`,
        )
      }
      iso = exploreIso(curSource, curTarget)
      if (iso === null) {
        throw new ProofError(
          `composing action ${actionIndex} step ${stepIndex} (${step.rule}) diverged: the sides are no longer isomorphic`,
        )
      }
    }
    out.push({
      label: action.label,
      steps: mappedSteps,
      placements: action.placements,
      ...(action.allocation === undefined ? {} : { allocation: action.allocation }),
    })
  }
  return out
}
