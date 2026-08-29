import type { Diagram } from '../../kernel/diagram/diagram'
import { cutDepth } from '../../kernel/diagram'
import { sigKey } from '../../kernel/diagram/sig'
import { serializeTerm } from '../../kernel/term/serialize'

/**
 * Iso-invariant bucketing digest: multisets of region depths, node
 * kind/arity/sig at region depth, and wire sig with endpoint count — all
 * preserved by any diagram isomorphism. Two isomorphic diagrams always get
 * equal digests; unequal diagrams may collide, which is why the memo
 * confirms bucket membership with sameDiagram before pruning.
 */
export function diagramDigest(diagram: Diagram): string {
  const regionDepths = Object.keys(diagram.regions).map((id) => cutDepth(diagram, id)).sort((a, b) => a - b)
  const nodeKeys = Object.values(diagram.nodes)
    .map((node) => {
      const content = node.kind === 'term'
        ? `${serializeTerm(node.term)}:${node.freeArity}`
        : `${node.kind === 'identity' ? node.arity : ''}:${sigKey(node.sig)}`
      return `${node.kind}:${content}@${cutDepth(diagram, node.region)}`
    })
    .sort()
  const wireKeys = Object.values(diagram.wires)
    .map((wire) => `${sigKey(wire.sig)}#${wire.endpoints.length}`)
    .sort()
  return `${regionDepths.join(',')}|${nodeKeys.join(',')}|${wireKeys.join(',')}`
}
