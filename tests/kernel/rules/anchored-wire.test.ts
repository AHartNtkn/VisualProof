import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, Endpoint, NodeId, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { bvar, lam, port, termEq } from '../../../src/kernel/term/term'
import { portKey } from '../../../src/kernel/diagram/diagram'
import {
  anchorAvailability,
  applyAnchoredWireContract,
  applyAnchoredWireSplit,
} from '../../../src/kernel/rules/anchored-wire'

const CLOSED = lam(bvar(0))
const OTHER_CLOSED = lam(lam(bvar(1)))
const EMPTY_CERT = { leftSteps: [], rightSteps: [] }

const sameEndpoint = (left: Endpoint, right: Endpoint): boolean =>
  left.node === right.node && portKey(left.port) === portKey(right.port)

function outputWire(d: Diagram, node: NodeId): WireId {
  const found = Object.entries(d.wires).find(([, wire]) =>
    wire.endpoints.some((endpoint) => sameEndpoint(endpoint, { node, port: { kind: 'output' } })))
  if (found === undefined) throw new Error(`no output wire for '${node}'`)
  return found[0]
}

function splitFixture({ inCut = false }: { inCut?: boolean } = {}) {
  const b = new DiagramBuilder()
  const base = inCut ? b.cut(b.root) : b.root
  const target = b.bubble(base, 1)
  const internal = b.bubble(target, 1)
  const outerCut = b.cut(target)
  const innerCut = b.cut(outerCut)
  const witness = b.termNode(internal, CLOSED)
  const firstNode = b.termNode(outerCut, port('s0'))
  const secondNode = b.termNode(innerCut, port('s0'))
  const first = { node: firstNode, port: { kind: 'freeVar' as const, name: 's0' } }
  const second = { node: secondNode, port: { kind: 'freeVar' as const, name: 's0' } }
  const wire = b.wire(target, [
    { node: witness, port: { kind: 'output' } },
    first,
    second,
  ])
  return { d: b.build(), wire, witness, first, second, target }
}

function contractFixture({
  shieldRedundant = false,
  survivorBehindCut = false,
  movedAtRoot = false,
  redundantTerm = CLOSED,
  survivorTerm = CLOSED,
  certificate = EMPTY_CERT,
}: {
  shieldRedundant?: boolean
  survivorBehindCut?: boolean
  movedAtRoot?: boolean
  redundantTerm?: ReturnType<typeof lam> | ReturnType<typeof port>
  survivorTerm?: ReturnType<typeof lam>
  certificate?: typeof EMPTY_CERT
} = {}) {
  const b = new DiagramBuilder()
  const survivorRegion = survivorBehindCut ? b.cut(b.root) : b.bubble(b.root, 1)
  const redundantRegion = shieldRedundant ? b.cut(b.root) : b.root
  const movedRegion = movedAtRoot ? b.root : b.cut(b.root)
  const redundant = b.termNode(redundantRegion, redundantTerm)
  const survivor = b.termNode(survivorRegion, survivorTerm)
  const movedNode = b.termNode(movedRegion, port('s0'))
  const moved = { node: movedNode, port: { kind: 'freeVar' as const, name: 's0' } }
  const redundantWire = b.wire(b.root, [
    { node: redundant, port: { kind: 'output' } },
    moved,
  ])
  const survivorWire = b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
  return {
    d: b.build(), redundant, survivor, moved, redundantWire, survivorWire,
    survivorScope: b.root, certificate,
  }
}

function shieldedFixture() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const witness = b.termNode(cut, CLOSED)
  const rootConsumer = b.termNode(b.root, port('s0'))
  const insideConsumer = b.termNode(cut, port('s0'))
  const wire = b.wire(b.root, [
    { node: witness, port: { kind: 'output' } },
    { node: rootConsumer, port: { kind: 'freeVar', name: 's0' } },
    { node: insideConsumer, port: { kind: 'freeVar', name: 's0' } },
  ])
  return {
    d: b.build(), cut, witness, rootConsumer, insideConsumer, wire,
    rootEndpoint: { node: rootConsumer, port: { kind: 'freeVar' as const, name: 's0' } },
    insideEndpoint: { node: insideConsumer, port: { kind: 'freeVar' as const, name: 's0' } },
  }
}

function sharedAnchorFixture() {
  const b = new DiagramBuilder()
  const a = b.termNode(b.root, CLOSED)
  const bNode = b.termNode(b.root, CLOSED)
  b.wire(b.root, [
    { node: a, port: { kind: 'output' } },
    { node: bNode, port: { kind: 'output' } },
  ])
  return { d: b.build(), a, b: bNode }
}

function newClosedWitness(after: Diagram, before: Diagram, target: string): NodeId {
  const found = Object.entries(after.nodes).find(([id, node]) =>
    before.nodes[id] === undefined && node.kind === 'term' && node.region === target && termEq(node.term, CLOSED))
  if (found === undefined) throw new Error('no new closed witness')
  return found[0]
}

describe('anchorAvailability', () => {
  it('crosses bubbles to the witness wire scope', () => {
    const b = new DiagramBuilder()
    const outer = b.bubble(b.root, 1)
    const inner = b.bubble(outer, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(b.root)
  })

  it('stops inside the first enclosing cut', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const bubble = b.bubble(cut, 1)
    const witness = b.termNode(bubble, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(cut)
  })

  it('never walks above the output wire scope', () => {
    const b = new DiagramBuilder()
    const scope = b.bubble(b.root, 1)
    const inner = b.bubble(scope, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(scope, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(scope)
  })

  it('refuses open and non-term witnesses', () => {
    const b = new DiagramBuilder()
    const open = b.termNode(b.root, port('x'))
    const ref = b.ref(b.root, 'R', 0)
    b.wire(b.root, [{ node: open, port: { kind: 'output' } }])
    expect(() => anchorAvailability(b.build(), open)).toThrow(/closed witness/)
    expect(() => anchorAvailability(b.build(), ref)).toThrow(/term nodes/)
  })
})

describe('anchored wire split and contraction', () => {
  it('splits an arbitrary endpoint group onto a target-scoped duplicate anchor', () => {
    const s = splitFixture()
    const out = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first, s.second], s.target)
    const duplicate = Object.entries(out.nodes).find(([id, node]) =>
      id !== s.witness && node.kind === 'term' && node.region === s.target && termEq(node.term, CLOSED))![0]
    const fresh = outputWire(out, duplicate)
    expect(out.wires[fresh]!.scope).toBe(s.target)
    expect(out.wires[fresh]!.endpoints).toEqual(expect.arrayContaining([
      { node: duplicate, port: { kind: 'output' } }, s.first, s.second,
    ]))
    expect(out.wires[s.wire]!.endpoints).not.toEqual(expect.arrayContaining([s.first, s.second]))
  })

  it('contracts an unshielded redundant anchor into a locally available survivor', () => {
    const s = contractFixture()
    const out = applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate)
    expect(out.nodes[s.redundant]).toBeUndefined()
    expect(out.wires[s.redundantWire]).toBeUndefined()
    expect(out.wires[s.survivorWire]!.scope).toBe(s.survivorScope)
    expect(out.wires[s.survivorWire]!.endpoints).toContainEqual(s.moved)
  })

  it('split then contract returns the exact canonical starting diagram', () => {
    const s = splitFixture()
    const split = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first], s.target)
    const duplicate = newClosedWitness(split, s.d, s.target)
    const back = applyAnchoredWireContract(split, duplicate, s.witness, EMPTY_CERT)
    expect(exploreForm(back)).toBe(exploreForm(s.d))
  })

  it('refuses a split target outside witness availability', () => {
    const s = shieldedFixture()
    expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.rootEndpoint], s.d.root))
      .toThrow(/outside witness .* availability/)
  })

  it('refuses a moved endpoint whose node is outside the split target', () => {
    const s = shieldedFixture()
    expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.rootEndpoint], s.cut))
      .toThrow(/endpoint .* outside target/)
  })

  it('refuses moving the selected witness output', () => {
    const s = splitFixture()
    expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [
      { node: s.witness, port: { kind: 'output' } },
    ], s.target)).toThrow(/cannot move witness .* output/)
  })

  it('refuses duplicate and unknown split endpoints', () => {
    const s = splitFixture()
    expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first, s.first], s.target))
      .toThrow(/selected more than once/)
    expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [
      { node: s.first.node, port: { kind: 'freeVar', name: 'missing' } },
    ], s.target)).toThrow(/is not on wire/)
  })

  it('refuses contraction of a cut-shielded redundant witness', () => {
    const s = contractFixture({ shieldRedundant: true })
    expect(() => applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate))
      .toThrow(/redundant witness .* shielded/)
  })

  it('refuses contraction when one moved endpoint lies just outside survivor availability', () => {
    const s = contractFixture({ survivorBehindCut: true, movedAtRoot: true })
    expect(() => applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate))
      .toThrow(/outside survivor .* availability/)
  })

  it('refuses open witnesses and a rejected conversion certificate', () => {
    const open = contractFixture({ redundantTerm: port('x') })
    expect(() => applyAnchoredWireContract(open.d, open.redundant, open.survivor, open.certificate))
      .toThrow(/closed witness/)
    const unequal = contractFixture({ survivorTerm: OTHER_CLOSED, certificate: EMPTY_CERT })
    expect(() => applyAnchoredWireContract(unequal.d, unequal.redundant, unequal.survivor, unequal.certificate))
      .toThrow(/certificate rejected/)
  })

  it('refuses identical witnesses and witnesses already on one wire', () => {
    const s = contractFixture()
    expect(() => applyAnchoredWireContract(s.d, s.redundant, s.redundant, s.certificate))
      .toThrow(/two distinct witnesses/)
    const shared = sharedAnchorFixture()
    expect(() => applyAnchoredWireContract(shared.d, shared.a, shared.b, EMPTY_CERT))
      .toThrow(/already share wire/)
  })

  it('is polarity-blind inside positive and negative regions', () => {
    for (const inCut of [false, true]) {
      const s = splitFixture({ inCut })
      const split = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first], s.target)
      const duplicate = newClosedWitness(split, s.d, s.target)
      expect(() => applyAnchoredWireContract(split, duplicate, s.witness, EMPTY_CERT)).not.toThrow()
    }
  })
})
