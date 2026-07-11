import { DiagramBuilder } from '../../kernel/diagram/builder'
import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import { isAncestorOrEqual } from '../../kernel/diagram/regions'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { ProofContext, ProofStep } from '../../kernel/proof/step'
import { applicableActions, type ActionDescriptor } from '../actions'
import { absorbHits, orphanedWires } from '../edit'
import { buildSelection, type Hit } from '../hittest'

export type ProofOrientation = 'forward' | 'backward'

export type ProofDiscovery = {
  readonly sel: SubgraphSelection
  readonly actions: readonly ActionDescriptor[]
}

export function discoverProofActions(
  d: Diagram,
  hits: readonly Hit[],
  ctx: ProofContext,
  orientation: ProofOrientation,
): ProofDiscovery | null {
  if (hits.length === 0) return null
  try {
    const sel = buildSelection(d, absorbHits(d, hits))
    return { sel, actions: applicableActions(d, sel, ctx, orientation === 'backward') }
  } catch {
    return null
  }
}

function erasureSelection(d: Diagram, sel: SubgraphSelection): SubgraphSelection {
  const existing = new Set(sel.wires)
  const riders = orphanedWires(d, new Set(sel.nodes))
    .filter((wire) => !existing.has(wire) && d.wires[wire]!.scope === sel.region)
  return riders.length === 0 ? sel : { ...sel, wires: [...sel.wires, ...riders] }
}

export function contextualDeleteStep(d: Diagram, discovery: ProofDiscovery, fuel: number): ProofStep | null {
  const byKind = (kind: ActionDescriptor['kind']): ActionDescriptor | undefined =>
    discovery.actions.find((action) => action.kind === kind)
  const action = byKind('doubleCutElim') ?? byKind('vacuousElim') ?? byKind('erase') ?? byKind('deiterate')
  if (action === undefined) return null
  switch (action.kind) {
    case 'doubleCutElim': return { rule: 'doubleCutElim', region: discovery.sel.regions[0]! }
    case 'vacuousElim': return { rule: 'vacuousElim', region: discovery.sel.regions[0]! }
    case 'erase': return { rule: 'erasure', sel: erasureSelection(d, discovery.sel) }
    case 'deiterate': return { rule: 'deiteration', sel: discovery.sel, fuel }
    default: throw new Error(`'${action.kind}' is not a contextual deletion`)
  }
}

export function iterationTargets(d: Diagram, sel: SubgraphSelection): readonly RegionId[] {
  const insideSelection = (region: RegionId): boolean => {
    let current = region
    for (;;) {
      if (sel.regions.includes(current)) return true
      const value = d.regions[current]!
      if (value.kind === 'sheet') return false
      current = value.parent
    }
  }
  return Object.keys(d.regions)
    .filter((region) => isAncestorOrEqual(d, sel.region, region) && !insideSelection(region))
}

export function foldedComprehension(ctx: ProofContext, name: string): DiagramWithBoundary {
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown relation '${name}'`)
  const arity = relation.boundary.length
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, arity)
  const boundary: WireId[] = []
  for (let index = 0; index < arity; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }]))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}
