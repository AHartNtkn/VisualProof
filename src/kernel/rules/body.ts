import type { Diagram, DiagramNode, NodeId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { isAncestorOrEqual, polarity } from '../diagram/regions'
import type { RelSig } from '../diagram/sig'
import { sigEquals, sigKey } from '../diagram/sig'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'

/**
 * Attaching a body to a relational wire IS quantifier instantiation: it is the
 * relational analogue of pinning a term wire with a term node. A relational
 * wire is an existentially scoped relation variable; a body node witnesses it
 * with a concrete comprehension `λx⃗. ψ(x⃗, b⃗)` — its `content` boundary is
 * `sig.args.length` argument stubs followed by `params.length` parameter wires
 * `b⃗` (spec §2.2, comprehension-as-equation). The output port lands on the
 * quantified wire and each parameter freeVar port `pj` lands on the host line
 * that supplies `b⃗`.
 *
 * The parameter scope gate is AT-OR-OUTSIDE the target wire's scope, not the
 * strictly-outside gate of the term-graph instantiation: a parameter sharing
 * the target region is admitted because the two same-polarity quantifiers
 * (the relation wire and the parameter wire) commute, so a witness may draw on
 * a parameter introduced in the very same region. The polarity gate is the
 * comprehension gate: a forward instantiation replaces `∃R. φ(R)` by `φ(G)` at
 * a NEGATIVE scope; backward is the same code path with the polarity boolean
 * flipped (POSITIVE). One wire carries at most one body.
 */
export function applyBodyAttach(
  d: Diagram,
  wireId: WireId,
  content: DiagramWithBoundary,
  params: readonly WireId[],
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  const need = orientation === 'forward' ? 'negative' : 'positive'
  const have = polarity(d, wire.scope)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}body attach requires a ${need} scope; wire '${wireId}' scope '${wire.scope}' is ${have}`,
    )
  }
  return attachBodyCore(d, wireId, content, params, reservation)
}

/**
 * The polarity-FREE core of body attachment: the signature, boundary-arithmetic,
 * parameter, and single-body gates plus the node+endpoint construction —
 * everything `applyBodyAttach` does except its polarity gate. Shared with bodied
 * vacuous introduction (the comprehension axiom `∃R. R=G`), which attaches a
 * body to a freshly minted wire at ANY polarity: introducing the tautology
 * `∃R. R=G ≡ ⊤` is valid everywhere, so no polarity gate belongs in the core.
 */
export function attachBodyCore(
  d: Diagram,
  wireId: WireId,
  content: DiagramWithBoundary,
  params: readonly WireId[],
  reservation?: IdReservation,
): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wire.sig.kind !== 'rel') {
    throw new RuleError(`wire '${wireId}' sig '${sigKey(wire.sig)}' is not a relation signature; only relational wires carry bodies`)
  }
  const sig: RelSig = wire.sig
  const argCount = sig.args.length
  if (content.boundary.length !== argCount + params.length) {
    throw new RuleError(
      `boundary arithmetic: content has ${content.boundary.length} boundary wires but wire '${wireId}' has arity ${argCount} and ${params.length} parameters were given`,
    )
  }

  for (let j = 0; j < params.length; j++) {
    const pid = params[j]!
    const pw = d.wires[pid]
    if (pw === undefined) throw new RuleError(`parameter wire '${pid}' does not exist`)
    const bWid = content.boundary[argCount + j]!
    const bWire = content.diagram.wires[bWid]
    if (bWire === undefined) {
      throw new DiagramError(`content boundary parameter wire '${bWid}' is missing from content`)
    }
    if (!sigEquals(pw.sig, bWire.sig)) {
      throw new RuleError(
        `parameter wire '${pid}' sig '${sigKey(pw.sig)}' does not match content boundary parameter sig '${sigKey(bWire.sig)}'`,
      )
    }
    if (!isAncestorOrEqual(d, pw.scope, wire.scope)) {
      throw new RuleError(
        `parameter wire '${pid}' (scope '${pw.scope}') must be at or outside the target wire's scope '${wire.scope}'`,
      )
    }
  }

  for (const ep of wire.endpoints) {
    if (ep.port.kind === 'output' && d.nodes[ep.node]?.kind === 'body') {
      throw new RuleError(`wire '${wireId}' already carries a body (node '${ep.node}')`)
    }
  }

  const takenNodeIds = new Set(Object.keys(d.nodes))
  const bodyId = freshId(takenNodeIds, 'body', reservation?.nodes)
  const bodyNode: DiagramNode = { kind: 'body', region: wire.scope, sig, content }

  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) wires[id] = w
  const target = wires[wireId]!
  wires[wireId] = {
    scope: target.scope,
    sig: target.sig,
    endpoints: [...target.endpoints, { node: bodyId, port: { kind: 'output' } }],
  }
  for (let j = 0; j < params.length; j++) {
    const pid = params[j]!
    const pw = wires[pid]!
    wires[pid] = {
      scope: pw.scope,
      sig: pw.sig,
      endpoints: [...pw.endpoints, { node: bodyId, port: { kind: 'freeVar', name: `p${j}` } }],
    }
  }

  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes, [bodyId]: bodyNode },
    wires,
  })
}

/** Remove one node, trimming its endpoints off every wire. */
function dropNode(d: Diagram, nodeId: NodeId): Diagram {
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id !== nodeId) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = { scope: w.scope, sig: w.sig, endpoints: w.endpoints.filter((ep) => ep.node !== nodeId) }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Detach a body node: the inverse of `applyBodyAttach`. Removing a witnessed
 * assertion is erasure, so the forward gate is POSITIVE (the polarity of the
 * body's region); backward is the same code path with the boolean flipped
 * (NEGATIVE). The wire and its parameters are left untouched — only the body
 * node and its endpoints are removed.
 */
export function applyBodyDetach(d: Diagram, bodyNodeId: NodeId, orientation: 'forward' | 'backward' = 'forward'): Diagram {
  const node = d.nodes[bodyNodeId]
  if (node === undefined) throw new DiagramError(`unknown node '${bodyNodeId}'`)
  if (node.kind !== 'body') throw new RuleError(`this rule applies to body nodes; '${bodyNodeId}' has kind '${node.kind}'`)

  const need = orientation === 'forward' ? 'positive' : 'negative'
  const have = polarity(d, node.region)
  if (have !== need) {
    throw new RuleError(
      `${orientation === 'backward' ? 'backward ' : ''}body detach requires a ${need} scope; body '${bodyNodeId}' region '${node.region}' is ${have}`,
    )
  }

  return dropNode(d, bodyNodeId)
}
