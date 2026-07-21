import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { app, bvar, lam, port, termEq } from '../../../src/kernel/term/term'
import type { ConversionCertificate } from '../../../src/kernel/term/certificate'
import { portKey } from '../../../src/kernel/diagram/diagram'
import {
  anchorAvailability,
  applyAnchoredWireContract,
  applyAnchoredWireSplit,
} from '../../../src/kernel/rules/anchored-wire'

const CLOSED = lam(bvar(0))
const OTHER_CLOSED = lam(lam(bvar(1)))
const EMPTY_CERT: ConversionCertificate = { leftSteps: [], rightSteps: [] }

const sameEndpoint = (left: Endpoint, right: Endpoint): boolean =>
  left.node === right.node && portKey(left.port) === portKey(right.port)

function outputWire(d: Diagram, node: NodeId): WireId {
  const found = Object.entries(d.wires).find(([, wire]) =>
    wire.endpoints.some((endpoint) => sameEndpoint(endpoint, { node, port: { kind: 'output' } })))
  if (found === undefined) throw new Error(`no output wire for '${node}'`)
  return found[0]
}

function redistribute(
  d: Diagram,
  sourceWitness: NodeId,
  targetWitness: NodeId,
  endpoints: readonly Endpoint[],
  target: RegionId,
  certificate: ConversionCertificate = EMPTY_CERT,
): Diagram {
  const wire = outputWire(d, sourceWitness)
  const split = applyAnchoredWireSplit(d, wire, sourceWitness, endpoints, target)
  const duplicate = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
  return applyAnchoredWireContract(split, duplicate, targetWitness, certificate)
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

function redistributionFixture({ inCut = false, consumerInside = false }: {
  inCut?: boolean
  consumerInside?: boolean
} = {}) {
  const b = new DiagramBuilder()
  const evidenceRegion = inCut ? b.cut(b.root) : b.root
  const consumerRegion = consumerInside ? b.cut(evidenceRegion) : evidenceRegion
  const a = b.termNode(evidenceRegion, CLOSED)
  const bNode = b.termNode(evidenceRegion, CLOSED)
  const firstNode = b.termNode(consumerRegion, port('s0'))
  const secondNode = b.termNode(consumerRegion, port('s0'))
  const first = { node: firstNode, port: { kind: 'freeVar' as const, name: 's0' } }
  const second = { node: secondNode, port: { kind: 'freeVar' as const, name: 's0' } }
  const aWire = b.wire(evidenceRegion, [
    { node: a, port: { kind: 'output' } },
    first,
    second,
  ])
  const bWire = b.wire(evidenceRegion, [{ node: bNode, port: { kind: 'output' } }])
  return { d: b.build(), evidenceRegion, a, b: bNode, first, second, aWire, bWire }
}

function shieldedRedistributionFixture() {
  const b = new DiagramBuilder()
  const evidenceRegion = b.cut(b.root)
  const a = b.termNode(evidenceRegion, CLOSED)
  const bNode = b.termNode(evidenceRegion, CLOSED)
  const consumer = b.termNode(evidenceRegion, port('s0'))
  const endpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 's0' } }
  const aWire = b.wire(b.root, [{ node: a, port: { kind: 'output' } }, endpoint])
  const bWire = b.wire(b.root, [{ node: bNode, port: { kind: 'output' } }])
  return {
    d: b.build(), evidenceRegion, a, b: bNode, endpoint, aWire, bWire,
    certificate: EMPTY_CERT,
  }
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

describe('anchored redistribution capability', () => {
  it.each([
    ['positive', false],
    ['negative', true],
  ] as const)('moves an endpoint between equivalent witnesses in %s polarity', (_name, inCut) => {
    const s = redistributionFixture({ inCut })
    const out = redistribute(s.d, s.a, s.b, [s.first], s.evidenceRegion)
    expect(out.wires[s.aWire]!.endpoints).not.toContainEqual(s.first)
    expect(out.wires[s.bWire]!.endpoints).toContainEqual(s.first)
  })

  it('uses a real beta conversion certificate between distinct closed witnesses', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, app(lam(bvar(0)), CLOSED))
    const survivor = b.termNode(b.root, CLOSED)
    const consumer = b.termNode(b.root, port('s0'))
    const endpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 's0' } }
    const aWire = b.wire(b.root, [{ node: a, port: { kind: 'output' } }, endpoint])
    const survivorWire = b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
    const d = b.build()
    const certificate = { leftSteps: [{ kind: 'beta' as const, path: [] }], rightSteps: [] }
    const out = redistribute(d, a, survivor, [endpoint], d.root, certificate)
    expect(out.wires[aWire]!.endpoints).not.toContainEqual(endpoint)
    expect(out.wires[survivorWire]!.endpoints).toContainEqual(endpoint)
  })

  it('preserves every node, region, wire id, and original wire scope while moving endpoints', () => {
    const s = redistributionFixture()
    const out = redistribute(s.d, s.a, s.b, [s.first], s.evidenceRegion)
    expect(out.nodes).toEqual(s.d.nodes)
    expect(out.regions).toEqual(s.d.regions)
    expect(Object.keys(out.wires).sort()).toEqual(Object.keys(s.d.wires).sort())
    for (const id of Object.keys(s.d.wires)) {
      expect(out.wires[id]!.scope).toBe(s.d.wires[id]!.scope)
    }
  })

  it('moves one endpoint or many endpoints as a single derived operation', () => {
    const one = redistributionFixture()
    const oneOut = redistribute(one.d, one.a, one.b, [one.first], one.evidenceRegion)
    expect(oneOut.wires[one.bWire]!.endpoints).toContainEqual(one.first)
    expect(oneOut.wires[one.aWire]!.endpoints).toContainEqual(one.second)

    const many = redistributionFixture()
    const manyOut = redistribute(many.d, many.a, many.b, [many.first, many.second], many.evidenceRegion)
    expect(manyOut.wires[many.aWire]!.endpoints).not.toEqual(expect.arrayContaining([many.first, many.second]))
    expect(manyOut.wires[many.bWire]!.endpoints).toEqual(expect.arrayContaining([many.first, many.second]))
  })

  it('allows a consumer strictly inside the evidence region', () => {
    const s = redistributionFixture({ consumerInside: true })
    const out = redistribute(s.d, s.a, s.b, [s.first], s.evidenceRegion)
    expect(out.wires[s.bWire]!.endpoints).toContainEqual(s.first)
  })

  it.each([
    ['outside', (b: DiagramBuilder) => b.root],
    ['sibling', (b: DiagramBuilder) => b.cut(b.root)],
  ] as const)('refuses a consumer %s the evidence region', (_name, consumerRegion) => {
    const b = new DiagramBuilder()
    const evidence = b.cut(b.root)
    const a = b.termNode(evidence, CLOSED)
    const survivor = b.termNode(evidence, CLOSED)
    const consumer = b.termNode(consumerRegion(b), port('s0'))
    const endpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 's0' } }
    const aWire = b.wire(b.root, [{ node: a, port: { kind: 'output' } }, endpoint])
    b.wire(evidence, [{ node: survivor, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => redistribute(d, a, survivor, [endpoint], evidence))
      .toThrow(/endpoint .* outside target/)
    expect(d.wires[aWire]!.endpoints).toContainEqual(endpoint)
  })

  it('refuses open evidence', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, port('x'))
    const survivor = b.termNode(b.root, port('x'))
    const consumer = b.termNode(b.root, port('s0'))
    const endpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 's0' } }
    b.wire(b.root, [{ node: a, port: { kind: 'output' } }, endpoint])
    b.wire(b.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: survivor, port: { kind: 'freeVar', name: 'x' } },
    ])
    b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => redistribute(d, a, survivor, [endpoint], d.root)).toThrow(/closed witness/)
  })

  it('refuses a rejected conversion certificate', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, CLOSED)
    const survivor = b.termNode(b.root, OTHER_CLOSED)
    const consumer = b.termNode(b.root, port('s0'))
    const endpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 's0' } }
    b.wire(b.root, [{ node: a, port: { kind: 'output' } }, endpoint])
    b.wire(b.root, [{ node: survivor, port: { kind: 'output' } }])
    const d = b.build()
    expect(() => redistribute(d, a, survivor, [endpoint], d.root, EMPTY_CERT))
      .toThrow(/certificate rejected/)
  })

  it('derives shielded local redistribution with root-scoped original wires', () => {
    const s = shieldedRedistributionFixture()
    const out = redistribute(s.d, s.a, s.b, [s.endpoint], s.evidenceRegion, s.certificate)
    expect(out.wires[s.aWire]!.scope).toBe(s.d.root)
    expect(out.wires[s.bWire]!.scope).toBe(s.d.root)
    expect(out.wires[s.aWire]!.endpoints).not.toContainEqual(s.endpoint)
    expect(out.wires[s.bWire]!.endpoints).toContainEqual(s.endpoint)
  })
})
