import type {
  Diagram,
  DiagramNode,
  NodeId,
  Port,
  Wire,
  WireId,
} from '../../diagram/diagram'
import { DiagramError, mkDiagram } from '../../diagram/diagram'
import { IOTA } from '../../diagram/sig'
import { free } from '../../term/term'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'

export type FreeVariableIdentityAction =
  | { readonly direction: 'toIdentity'; readonly node: NodeId }
  | { readonly direction: 'toTerm'; readonly node: NodeId; readonly outputPort: 0 | 1 }

function replaceNode(
  diagram: Diagram,
  node: NodeId,
  replacement: DiagramNode,
  replacePort: (port: Port) => Port,
): Diagram {
  const wires: Record<WireId, Wire> = Object.fromEntries(
    Object.entries(diagram.wires).map(([wireId, wire]) => [
      wireId,
      {
        sig: wire.sig,
        endpoints: wire.endpoints.map((endpoint) => endpoint.node === node
          ? { node, port: replacePort(endpoint.port) }
          : endpoint),
      },
    ]),
  )
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes: { ...diagram.nodes, [node]: replacement },
    wires,
  })
}

/** Exact bridge between free(0) and a binary individual identity incidence. */
export function applyFreeVariableIdentity(
  diagram: Diagram,
  action: FreeVariableIdentityAction,
): Diagram {
  if (action.direction === 'toIdentity') {
    const node = termNodeAt(diagram, action.node)
    if (
      node.freeArity !== 1
      || node.term.kind !== 'free'
      || node.term.slot !== 0
    ) {
      throw new RuleError(
        `free-variable identity requires a term containing exactly free slot 0`,
      )
    }
    wireAt(diagram, action.node, { kind: 'output' })
    wireAt(diagram, action.node, { kind: 'free', index: 0 })
    return replaceNode(
      diagram,
      action.node,
      { kind: 'identity', region: node.region, sig: IOTA, arity: 2 },
      (port) => {
        if (port.kind === 'output') return { kind: 'identity', index: 0 }
        if (port.kind === 'free' && port.index === 0) {
          return { kind: 'identity', index: 1 }
        }
        throw new DiagramError(
          `term node '${action.node}' has unexpected port '${port.kind}'`,
        )
      },
    )
  }

  const node = diagram.nodes[action.node]
  if (node === undefined) throw new DiagramError(`unknown node '${action.node}'`)
  if (node.kind !== 'identity') {
    throw new RuleError(
      `free-variable identity reverse requires an identity node; `
      + `'${action.node}' has kind '${node.kind}'`,
    )
  }
  if (node.sig.kind !== 'iota') {
    throw new RuleError(`free-variable identity reverse requires an IOTA identity`)
  }
  if (node.arity !== 2) {
    throw new RuleError(`free-variable identity reverse requires a binary identity`)
  }
  wireAt(diagram, action.node, { kind: 'identity', index: 0 })
  wireAt(diagram, action.node, { kind: 'identity', index: 1 })
  return replaceNode(
    diagram,
    action.node,
    { kind: 'term', region: node.region, term: free(0), freeArity: 1 },
    (port) => {
      if (port.kind !== 'identity') {
        throw new DiagramError(
          `identity node '${action.node}' has unexpected port '${port.kind}'`,
        )
      }
      return port.index === action.outputPort
        ? { kind: 'output' }
        : { kind: 'free', index: 0 }
    },
  )
}
