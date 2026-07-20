import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError, mkDiagram, type Diagram, type NodeId, type RegionId } from '../../../src/kernel/diagram/diagram'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { NormalSeparationCertificate } from '../../../src/kernel/term/certificate'
import { RuleError } from '../../../src/kernel/rules/error'
import {
  applyInconsistentCutElim,
  findInconsistentCutEvidence,
  hasInconsistentCutCandidate,
} from '../../../src/kernel/rules/inconsistent-cut'

const p = (source: string) => parseTerm(source)
const I = p('\\x. x')
const K = p('\\x. \\y. x')
const OMEGA = p('(\\x. x x) (\\x. x x)')
const emptyCertificate: NormalSeparationCertificate = { firstSteps: [], secondSteps: [] }

function closedPair(
  firstTerm = I,
  secondTerm = K,
  enclosingCut = false,
): { diagram: Diagram; cut: RegionId; first: NodeId; second: NodeId } {
  const builder = new DiagramBuilder()
  const parent = enclosingCut ? builder.cut(builder.root) : builder.root
  const cut = builder.cut(parent)
  const first = builder.termNode(cut, firstTerm)
  const second = builder.termNode(cut, secondTerm)
  builder.wire(cut, [
    { node: first, port: { kind: 'output' } },
    { node: second, port: { kind: 'output' } },
  ])
  return { diagram: builder.build(), cut, first, second }
}

describe('inconsistent-cut candidate discovery', () => {
  it('recognizes a real cut with two directly contained closed terms on one output wire without reducing them', () => {
    const { diagram, cut } = closedPair(OMEGA, I)

    expect(hasInconsistentCutCandidate(diagram, cut)).toBe(true)
  })

  it('rejects non-cut, non-direct, open-interface, and different-output structural lookalikes', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const child = builder.cut(cut)
    const direct = builder.termNode(cut, I)
    const descendant = builder.termNode(child, K)
    builder.wire(cut, [
      { node: direct, port: { kind: 'output' } },
      { node: descendant, port: { kind: 'output' } },
    ])
    const openFirst = builder.termNode(cut, I, ['unused'])
    const openSecond = builder.termNode(cut, K)
    builder.wire(cut, [
      { node: openFirst, port: { kind: 'output' } },
      { node: openSecond, port: { kind: 'output' } },
    ])
    builder.termNode(cut, I)
    builder.termNode(cut, K)
    const rootFirst = builder.termNode(builder.root, I)
    const rootSecond = builder.termNode(builder.root, K)
    builder.wire(builder.root, [
      { node: rootFirst, port: { kind: 'output' } },
      { node: rootSecond, port: { kind: 'output' } },
    ])
    const diagram = builder.build()

    expect(hasInconsistentCutCandidate(diagram, cut)).toBe(false)
    expect(hasInconsistentCutCandidate(diagram, builder.root)).toBe(false)
    expect(hasInconsistentCutCandidate(diagram, 'missing')).toBe(false)
  })

  it('returns an empty-path certificate for already separated normal forms', () => {
    const { diagram, cut, first, second } = closedPair()

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toEqual({
      status: 'certified',
      first,
      second,
      certificate: emptyCertificate,
    })
  })

  it('returns nonempty replay paths for reducible separated terms', () => {
    const { diagram, cut, first, second } = closedPair(
      p('(\\x. x) (\\z. z)'),
      p('\\x. (\\a. \\b. a) x'),
    )

    const result = findInconsistentCutEvidence(diagram, cut, 2)

    expect(result).toEqual({
      status: 'certified',
      first,
      second,
      certificate: {
        firstSteps: [{ kind: 'beta', path: [] }],
        secondSteps: [{ kind: 'beta', path: ['body'] }],
      },
    })
  })

  it('chooses the first certifying pair in lexical node-ID order', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const n0 = builder.termNode(cut, I)
    const n1 = builder.termNode(cut, K)
    const n2 = builder.termNode(cut, p('\\x. \\y. y'))
    builder.wire(cut, [n2, n1, n0].map((node) => ({ node, port: { kind: 'output' as const } })))
    const diagram = builder.build()

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toMatchObject({
      status: 'certified', first: n0, second: n1,
    })
  })

  it('continues after an equal-normal pair to a later separated pair', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const n0 = builder.termNode(cut, p('\\x. x'))
    const n1 = builder.termNode(cut, p('\\renamed. renamed'))
    const n2 = builder.termNode(cut, K)
    builder.wire(cut, [n0, n1, n2].map((node) => ({ node, port: { kind: 'output' as const } })))
    const diagram = builder.build()

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toMatchObject({
      status: 'certified', first: n0, second: n2,
    })
  })

  it('continues after exhausted pairs to a later certifying pair', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diverging = builder.termNode(cut, OMEGA)
    const first = builder.termNode(cut, I)
    const second = builder.termNode(cut, K)
    builder.wire(cut, [diverging, first, second].map((node) => ({ node, port: { kind: 'output' as const } })))
    const diagram = builder.build()

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toMatchObject({
      status: 'certified', first, second,
    })
  })

  it('returns undecided only after every pair fails to certify and at least one exhausts', () => {
    const { diagram, cut } = closedPair(OMEGA, I)

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toEqual({ status: 'undecided' })
  })

  it('returns absent when no pair exhausts and none has unequal normal forms', () => {
    const { diagram, cut } = closedPair(p('\\x. x'), p('\\renamed. renamed'))

    expect(findInconsistentCutEvidence(diagram, cut, 1)).toEqual({ status: 'absent' })
    expect(findInconsistentCutEvidence(diagram, diagram.root, 1)).toEqual({ status: 'absent' })
  })
})

describe('applyInconsistentCutElim', () => {
  it.each([
    ['a cut directly under the sheet', false],
    ['a cut nested under another cut', true],
  ])('accepts empty-path separation in %s', (_label, enclosingCut) => {
    const { diagram, cut, first, second } = closedPair(I, K, enclosingCut)

    const result = applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate)

    expect(result.regions[cut]).toBeUndefined()
    expect(result.nodes[first]).toBeUndefined()
    expect(result.nodes[second]).toBeUndefined()
  })

  it('accepts replayed nonempty reduction paths', () => {
    const { diagram, cut, first, second } = closedPair(
      p('(\\x. x) (\\z. z)'),
      p('\\x. (\\a. \\b. a) x'),
    )

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, {
      firstSteps: [{ kind: 'beta', path: [] }],
      secondSteps: [{ kind: 'eta', path: [] }],
    })).not.toThrow()
  })

  it('atomically removes arbitrary cut contents and descendants while preserving unrelated content', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const descendant = builder.cut(cut)
    const unrelatedRegion = builder.cut(builder.root)
    const first = builder.termNode(cut, I)
    const second = builder.termNode(cut, K)
    const extra = builder.ref(cut, 'arbitrary', 0)
    const descendantNode = builder.termNode(descendant, I)
    const outside = builder.termNode(builder.root, I)
    const unrelatedNode = builder.termNode(unrelatedRegion, K)
    const shared = builder.wire(builder.root, [
      { node: first, port: { kind: 'output' } },
      { node: second, port: { kind: 'output' } },
      { node: outside, port: { kind: 'output' } },
    ])
    const descendantWire = builder.wire(descendant, [
      { node: descendantNode, port: { kind: 'output' } },
    ])
    const cutScopedWire = builder.wire(cut, [])
    const unrelatedWire = builder.wire(unrelatedRegion, [
      { node: unrelatedNode, port: { kind: 'output' } },
    ])
    const diagram = builder.build()
    const before = {
      root: diagram.regions[diagram.root],
      unrelatedRegion: diagram.regions[unrelatedRegion],
      outside: diagram.nodes[outside],
      unrelatedNode: diagram.nodes[unrelatedNode],
      unrelatedWire: diagram.wires[unrelatedWire],
    }

    const result = applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate)

    expect(result.regions[cut]).toBeUndefined()
    expect(result.regions[descendant]).toBeUndefined()
    expect(result.nodes[first]).toBeUndefined()
    expect(result.nodes[second]).toBeUndefined()
    expect(result.nodes[extra]).toBeUndefined()
    expect(result.nodes[descendantNode]).toBeUndefined()
    expect(result.wires[descendantWire]).toBeUndefined()
    expect(result.wires[cutScopedWire]).toBeUndefined()
    expect(result.wires[shared]).toEqual({
      scope: diagram.root,
      endpoints: [{ node: outside, port: { kind: 'output' } }],
    })
    expect(result.regions[result.root]).toBe(before.root)
    expect(result.regions[unrelatedRegion]).toBe(before.unrelatedRegion)
    expect(result.nodes[outside]).toBe(before.outside)
    expect(result.nodes[unrelatedNode]).toBe(before.unrelatedNode)
    expect(result.wires[unrelatedWire]).toEqual(before.unrelatedWire)
    expect(result).toEqual(mkDiagram({
      root: result.root,
      regions: { ...result.regions },
      nodes: { ...result.nodes },
      wires: { ...result.wires },
    }))
  })

  it('rejects unknown and non-cut regions with structural and rule error vocabularies', () => {
    const { diagram, first, second } = closedPair()

    expect(() => applyInconsistentCutElim(diagram, 'missing', first, second, emptyCertificate))
      .toThrowError(DiagramError)
    expect(() => applyInconsistentCutElim(diagram, diagram.root, first, second, emptyCertificate))
      .toThrowError(RuleError)
  })

  it('rejects repeated node IDs', () => {
    const { diagram, cut, first } = closedPair()

    expect(() => applyInconsistentCutElim(diagram, cut, first, first, emptyCertificate))
      .toThrowError(/two distinct term nodes/)
  })

  it('rejects an open term-node interface', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.termNode(cut, I, ['unused'])
    const second = builder.termNode(cut, K)
    builder.wire(cut, [
      { node: first, port: { kind: 'output' } },
      { node: second, port: { kind: 'output' } },
    ])
    const diagram = builder.build()

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate))
      .toThrowError(/requires closed terms/)
  })

  it('rejects a descendant term node', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const descendant = builder.cut(cut)
    const first = builder.termNode(cut, I)
    const second = builder.termNode(descendant, K)
    builder.wire(cut, [
      { node: first, port: { kind: 'output' } },
      { node: second, port: { kind: 'output' } },
    ])
    const diagram = builder.build()

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate))
      .toThrowError(/directly contained/)
  })

  it('rejects term outputs on different wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.termNode(cut, I)
    const second = builder.termNode(cut, K)
    const diagram = builder.build()

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate))
      .toThrowError(/outputs must share one wire/)
  })

  it('rejects equal normal forms', () => {
    const { diagram, cut, first, second } = closedPair(p('\\x. x'), p('\\renamed. renamed'))

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate))
      .toThrowError(/same normal form/)
  })

  it('rejects invalid replay paths', () => {
    const { diagram, cut, first, second } = closedPair()

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, {
      firstSteps: [{ kind: 'beta', path: [] }],
      secondSteps: [],
    })).toThrowError(/first step 0 is invalid/)
  })

  it('rejects a replay path ending at a non-normal endpoint', () => {
    const { diagram, cut, first, second } = closedPair(p('(\\x. x) (\\z. z)'), K)

    expect(() => applyInconsistentCutElim(diagram, cut, first, second, emptyCertificate))
      .toThrowError(/first reduction path does not end in beta-eta normal form/)
  })
})
