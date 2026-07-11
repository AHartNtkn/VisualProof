import type { Diagram, NodeId, WireId } from '../kernel/diagram/diagram'

export type ChangeFocus =
  | { readonly kind: 'items'; readonly nodes: readonly NodeId[]; readonly wires: readonly WireId[] }
  | { readonly kind: 'diagram' }

export type PreviewTransition = {
  readonly before: Diagram
  readonly after: Diagram
  readonly focus: ChangeFocus
}

const structurallyEqual = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)

export function deriveChangeFocus(before: Diagram, after: Diagram): ChangeFocus {
  const nodes = new Set<NodeId>()
  const wires = new Set<WireId>()

  for (const [id, node] of Object.entries(after.nodes)) {
    const prior = before.nodes[id]
    if (prior === undefined || !structurallyEqual(prior, node)) nodes.add(id)
  }
  for (const [id, wire] of Object.entries(after.wires)) {
    const prior = before.wires[id]
    if (prior === undefined || !structurallyEqual(prior, wire)) wires.add(id)
  }

  const removedNodes = new Set(Object.keys(before.nodes).filter((id) => after.nodes[id] === undefined))
  for (const [id, wire] of Object.entries(before.wires)) {
    const removedWire = after.wires[id] === undefined
    const touchesRemovedNode = wire.endpoints.some((endpoint) => removedNodes.has(endpoint.node))
    if (!removedWire && !touchesRemovedNode) continue
    for (const endpoint of wire.endpoints) {
      if (after.nodes[endpoint.node] !== undefined) nodes.add(endpoint.node)
    }
  }

  if (nodes.size === 0 && wires.size === 0) return { kind: 'diagram' }
  return { kind: 'items', nodes: [...nodes].sort(), wires: [...wires].sort() }
}

export function previewTransition(states: readonly Diagram[], cursor: number): PreviewTransition {
  if (states.length === 0) throw new Error('cannot preview an empty timeline')
  const bounded = Math.max(0, Math.min(states.length - 1, cursor))
  const beforeIndex = bounded === 0 ? 0 : bounded - 1
  const afterIndex = states.length === 1 ? 0 : bounded === 0 ? 1 : bounded
  const before = states[beforeIndex]!
  const after = states[afterIndex]!
  return { before, after, focus: deriveChangeFocus(before, after) }
}
