import type { Diagram, RegionId } from '../diagram/diagram'
import { deepestCommonAncestor, derivedScope } from '../diagram/regions'
import type { ProofStep } from './step'

/**
 * The next scaffolding pin a vacuity deletion can remove, or null. A pin is
 * removable when losing it changes neither its wire's derived scope nor the
 * two-end floor — it holds nothing, so deleting it is ⊤-idle and keeps
 * diagrams pin-minimal: the canonical shape stated sides are drawn in.
 * Deterministic (sorted wires, then sorted pin nodes), so recorded sweeps
 * replay identically.
 */
export function nextRemovablePinStep(d: Diagram): ProofStep | null {
  for (const wireId of Object.keys(d.wires).sort()) {
    const wire = d.wires[wireId]!
    if (wire.endpoints.length <= 2) continue
    const scope = derivedScope(d, wireId)
    for (const endpoint of [...wire.endpoints].sort((a, b) =>
      a.node < b.node ? -1 : a.node > b.node ? 1 : 0)) {
      const node = d.nodes[endpoint.node]
      if (node === undefined || node.kind !== 'identity' || node.arity !== 1) continue
      const rest = wire.endpoints.filter((candidate) => candidate.node !== endpoint.node)
      if (rest.length < 2) continue
      let dca: RegionId | null = null
      for (const other of rest) {
        const region = d.nodes[other.node]!.region
        dca = dca === null ? region : deepestCommonAncestor(d, dca, region)
      }
      if (dca !== scope) continue
      return {
        rule: 'vacuity',
        direction: 'delete',
        assembly: {
          nodes: { [endpoint.node]: { region: node.region, sig: node.sig, arity: 1 } },
          wires: {},
          attachments: { [wireId]: [endpoint] },
        },
      }
    }
  }
  return null
}
