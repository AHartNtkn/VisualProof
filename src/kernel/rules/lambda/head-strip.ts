import type { Diagram, DiagramNode, NodeId, Wire, WireId } from '../../diagram/diagram'
import { mkDiagram } from '../../diagram/diagram'
import { derivedScope } from '../../diagram/regions'
import { IOTA } from '../../diagram/sig'
import { freshId, type IdReservation } from '../../diagram/subgraph/freshId'
import { headSpine, type HeadSpine } from '../../term/hnf'
import { application, free, lambda, termEq, type Term } from '../../term/term'
import { termNodeAt, wireAt } from '../access'
import { RuleError } from '../error'
import { completeWireEnds, type PartsInProgress } from '../wire-ends'
import {
  mapTermToCommonCarrier,
  validateSlotCorrespondence,
  validateSlotCorrespondenceWires,
  type SlotCorrespondence,
} from './correspondence'

function mapSlots(term: Term, mapping: readonly number[]): Term {
  switch (term.kind) {
    case 'bound': return term
    case 'free': return free(mapping[term.slot]!)
    case 'lambda': return lambda(mapSlots(term.body, mapping))
    case 'application':
      return application(mapSlots(term.fn, mapping), mapSlots(term.argument, mapping))
  }
}

function compactClosure(
  diagram: Diagram,
  source: NodeId,
  sourceArity: number,
  term: Term,
): { readonly term: Term; readonly wires: readonly WireId[] } {
  const used: number[] = []
  const seenSlots = new Set<number>()
  const visit = (current: Term): void => {
    switch (current.kind) {
      case 'bound': return
      case 'free':
        if (!seenSlots.has(current.slot)) {
          seenSlots.add(current.slot)
          used.push(current.slot)
        }
        return
      case 'lambda':
        visit(current.body)
        return
      case 'application':
        visit(current.fn)
        visit(current.argument)
    }
  }
  visit(term)
  const mapping: number[] = Array.from({ length: sourceArity })
  const wires: WireId[] = []
  const byWire = new Map<WireId, number>()
  for (const native of used) {
    const wire = wireAt(diagram, source, { kind: 'free', index: native })
    let compact = byWire.get(wire)
    if (compact === undefined) {
      compact = wires.length
      byWire.set(wire, compact)
      wires.push(wire)
    }
    mapping[native] = compact
  }
  return { term: mapSlots(term, mapping), wires }
}

/** Replace a rigid-head binary equation with pairwise argument equations. */
export function applyLambdaHeadStrip(
  diagram: Diagram,
  a: NodeId,
  b: NodeId,
  correspondence: SlotCorrespondence,
  reservation?: IdReservation,
): Diagram {
  if (a === b) {
    throw new RuleError(`head strip needs two distinct nodes; got '${a}' twice`)
  }
  const left = termNodeAt(diagram, a)
  const right = termNodeAt(diagram, b)
  if (left.region !== right.region) {
    throw new RuleError(
      `head strip requires both nodes in one region; `
      + `'${a}' is in '${left.region}', '${b}' in '${right.region}'`,
    )
  }
  const region = left.region
  validateSlotCorrespondence(
    correspondence,
    left.freeArity,
    right.freeArity,
  )

  const outputA = wireAt(diagram, a, { kind: 'output' })
  const outputB = wireAt(diagram, b, { kind: 'output' })
  if (outputA !== outputB) {
    throw new RuleError(
      `head strip requires the outputs of '${a}' and '${b}' to share one wire; `
      + `found '${outputA}' and '${outputB}'`,
    )
  }
  const equation = diagram.wires[outputA]!
  if (equation.endpoints.length !== 2) {
    throw new RuleError(
      `head strip requires a binary equation wire; '${outputA}' has extra endpoints`,
    )
  }
  if (derivedScope(diagram, outputA) !== region) {
    throw new RuleError(
      `head strip requires a local binary equation in '${region}'`,
    )
  }

  const normalHead = (
    node: NodeId,
    spine: HeadSpine,
  ): Exclude<HeadSpine['head'], { readonly kind: 'redex' }> => {
    if (spine.head.kind === 'redex') {
      throw new RuleError(`'${node}' is not in head-normal form`)
    }
    return spine.head
  }
  const leftSpine = headSpine(left.term)
  const rightSpine = headSpine(right.term)
  const leftHead = normalHead(a, leftSpine)
  const rightHead = normalHead(b, rightSpine)
  if (leftSpine.binders !== rightSpine.binders) {
    throw new RuleError(
      `head strip requires aligned spines; binder counts differ: `
      + `${leftSpine.binders} vs ${rightSpine.binders}`,
    )
  }
  if (leftSpine.args.length !== rightSpine.args.length) {
    throw new RuleError(
      `head strip requires aligned spines; argument counts differ: `
      + `${leftSpine.args.length} vs ${rightSpine.args.length}`,
    )
  }
  if (leftHead.kind !== 'bound' || rightHead.kind !== 'bound') {
    throw new RuleError('head strip requires bound rigid heads; free heads are not injective')
  }
  if (leftHead.index !== rightHead.index) {
    throw new RuleError(
      `heads do not correspond: bound indices differ `
      + `(${leftHead.index} vs ${rightHead.index})`,
    )
  }

  validateSlotCorrespondenceWires(diagram, a, b, correspondence)

  const close = (term: Term): Term => {
    let result = term
    for (let index = 0; index < leftSpine.binders; index++) result = lambda(result)
    return result
  }
  const pairs: Array<{
    readonly left: ReturnType<typeof compactClosure>
    readonly right: ReturnType<typeof compactClosure>
  }> = []
  for (let index = 0; index < leftSpine.args.length; index++) {
    const leftClosure = close(leftSpine.args[index]!)
    const rightClosure = close(rightSpine.args[index]!)
    if (termEq(
      mapTermToCommonCarrier(leftClosure, correspondence.left),
      mapTermToCommonCarrier(rightClosure, correspondence.right),
    )) continue
    pairs.push({
      left: compactClosure(diagram, a, left.freeArity, leftClosure),
      right: compactClosure(diagram, b, right.freeArity, rightClosure),
    })
  }

  const touched = new Set<WireId>()
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wireId === outputA) continue
    if (wire.endpoints.some((endpoint) => endpoint.node === a || endpoint.node === b)) {
      touched.add(wireId)
    }
  }
  const oldScopes = new Map([...touched].map((wire) => [wire, derivedScope(diagram, wire)]))
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [nodeId, node] of Object.entries(diagram.nodes)) {
    if (nodeId !== a && nodeId !== b) nodes[nodeId] = node
  }
  const wires: Record<WireId, Wire> = {}
  for (const [wireId, wire] of Object.entries(diagram.wires)) {
    if (wireId === outputA) continue
    wires[wireId] = {
      sig: wire.sig,
      endpoints: wire.endpoints.filter((endpoint) =>
        endpoint.node !== a && endpoint.node !== b),
    }
  }
  const takenNodes = new Set(Object.keys(diagram.nodes))
  const takenWires = new Set(Object.keys(diagram.wires))
  const attach = (wireId: WireId, node: NodeId, slot: number): void => {
    const wire = wires[wireId]!
    wires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node, port: { kind: 'free', index: slot } }],
    }
  }
  for (const pair of pairs) {
    const madeA = freshId(takenNodes, `${a}_hs`, reservation?.nodes)
    takenNodes.add(madeA)
    const madeB = freshId(takenNodes, `${b}_hs`, reservation?.nodes)
    takenNodes.add(madeB)
    nodes[madeA] = {
      kind: 'term', region, term: pair.left.term, freeArity: pair.left.wires.length,
    }
    nodes[madeB] = {
      kind: 'term', region, term: pair.right.term, freeArity: pair.right.wires.length,
    }
    pair.left.wires.forEach((wire, slot) => attach(wire, madeA, slot))
    pair.right.wires.forEach((wire, slot) => attach(wire, madeB, slot))
    const output = freshId(takenWires, `${a}_${b}_hs`, reservation?.wires)
    takenWires.add(output)
    wires[output] = {
      sig: IOTA,
      endpoints: [
        { node: madeA, port: { kind: 'output' } },
        { node: madeB, port: { kind: 'output' } },
      ],
    }
  }
  const parts: PartsInProgress = {
    regions: { ...diagram.regions },
    nodes,
    wires,
  }
  for (const [wire, scope] of oldScopes) {
    completeWireEnds(parts, wire, scope, 'Lambda head strip', reservation?.nodes)
  }
  return mkDiagram({ root: diagram.root, ...parts })
}
