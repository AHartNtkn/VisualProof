import type { Diagram, NodeId, RegionId, WireId } from '../diagram/diagram'
import { DiagramError } from '../diagram/diagram'
import { derivedScope } from '../diagram/regions'
import type { Sig } from '../diagram/sig'
import { freshId } from '../diagram/subgraph/freshId'
import { applyVacuityDelete, applyVacuityInsert } from '../rules/identity-rules'
import { RuleError } from '../rules/error'
import type { ProofStep } from './step'

type VacuityStep = Extract<ProofStep, { rule: 'vacuity' }>

/**
 * The bare wire — the drawable floating existential ∃x:σ.⊤ — as its
 * primitive vacuity decomposition: a point at `region`, then a stub grown
 * from it. The stub's base names the id the point step will actually mint
 * against `diagram`, so the pair replays as recorded (freshening is
 * deterministic; ids are final). Returns the steps and the wire id the
 * stub will mint.
 */
export function bareWireInsertSteps(
  diagram: Diagram,
  region: RegionId,
  sig: Sig,
  wireLabel: WireId = 'w',
  endLabels: readonly [NodeId, NodeId] = [`${wireLabel}_end0`, `${wireLabel}_end1`],
): { readonly steps: readonly ProofStep[]; readonly wire: WireId } {
  const pointId = freshId(new Set(Object.keys(diagram.nodes)), endLabels[0])
  const wireId = freshId(new Set(Object.keys(diagram.wires)), wireLabel)
  return {
    wire: wireId,
    steps: [
      {
        rule: 'vacuity',
        direction: 'insert',
        instance: { kind: 'point', node: endLabels[0], region, sig },
      },
      {
        rule: 'vacuity',
        direction: 'insert',
        instance: { kind: 'stub', base: pointId, wire: wireLabel, end: endLabels[1], region },
      },
    ],
  }
}

/**
 * Retire a bare (all-pin) wire as its primitive vacuity sequence: shed
 * spare pins from a scope-holding anchor (so no shed is ever
 * load-bearing — anchoring one at the scope first when no pin holds it),
 * retract the last stub, delete the remaining point. The old one-step
 * bare-wire deletion is exactly this composite.
 */
export function bareWireDeletionSteps(
  diagram: Diagram,
  wireId: WireId,
): readonly ProofStep[] {
  const wire = diagram.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  for (const endpoint of wire.endpoints) {
    const node = diagram.nodes[endpoint.node]!
    if (node.kind !== 'identity' || node.arity !== 1) {
      throw new RuleError(
        `wire '${wireId}' is not bare; endpoint '${endpoint.node}' is not a pin`,
      )
    }
  }
  const steps: VacuityStep[] = []
  let d = diagram
  const emit = (step: VacuityStep): void => {
    steps.push(step)
    d = step.direction === 'insert'
      ? applyVacuityInsert(d, step.instance)
      : applyVacuityDelete(d, step.instance)
  }
  const sig = wire.sig
  const scope = derivedScope(d, wireId)
  let anchor = wire.endpoints.find((ep) => d.nodes[ep.node]!.region === scope)?.node
  if (anchor === undefined) {
    // No single pin holds the quantifier (the scope is a strict meet):
    // anchor one there first, so every later shed provably preserves it.
    emit({
      rule: 'vacuity',
      direction: 'insert',
      instance: { kind: 'pin', wire: wireId, node: `retire_${wireId}`, region: scope },
    })
    anchor = d.wires[wireId]!.endpoints
      .find((ep) => d.nodes[ep.node]!.region === scope)!.node
  }
  for (;;) {
    const ends = d.wires[wireId]!.endpoints
    if (ends.length <= 2) break
    const victim = ends.find((ep) => ep.node !== anchor)!
    emit({
      rule: 'vacuity',
      direction: 'delete',
      instance: {
        kind: 'pin',
        wire: wireId,
        node: victim.node,
        region: d.nodes[victim.node]!.region,
      },
    })
  }
  const far = d.wires[wireId]!.endpoints.find((ep) => ep.node !== anchor)!
  emit({
    rule: 'vacuity',
    direction: 'delete',
    instance: {
      kind: 'stub',
      base: anchor,
      wire: wireId,
      end: far.node,
      region: d.nodes[far.node]!.region,
    },
  })
  emit({
    rule: 'vacuity',
    direction: 'delete',
    instance: { kind: 'point', node: anchor, region: scope, sig },
  })
  return steps
}
