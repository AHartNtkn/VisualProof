import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { termEq } from '../../src/kernel/term/term'
import type { ProofContext } from '../../src/kernel/proof/step'
import { replayProof } from '../../src/kernel/proof/step'
import { addTermNode, emptyDiagram } from '../../src/app/edit'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../../src/app/tactics'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const pc = (s: string) => parseTerm(s, new Set(['PLUS']))

const ctx: ProofContext = { definitions: {}, theorems: new Map() }

const diagramWith = (s: string, parser: (x: string) => ReturnType<typeof p> = p) => {
  const d0 = emptyDiagram()
  return addTermNode(d0, d0.root, parser(s))
}

describe('convertToHeadNormal', () => {
  it('rewrites (\\u. u) y to y and the step replays through replayProof', () => {
    const { diagram: d, node } = diagramWith('(\\u. u) y')
    const res = convertToHeadNormal(d, node, 100)
    const after = res.diagram.nodes[node]
    expect(after?.kind).toBe('term')
    expect(after?.kind === 'term' && termEq(after.term, p('y'))).toBe(true)
    expect(res.step.rule).toBe('conversion')
    const replayed = replayProof(d, [res.step], ctx)
    expect(replayed).toEqual(res.diagram)
  })

  it('descends under the binder prefix: \\x. (\\u. u) x becomes \\x. x', () => {
    const { diagram: d, node } = diagramWith('\\x. (\\u. u) x')
    const res = convertToHeadNormal(d, node, 100)
    const after = res.diagram.nodes[node]
    expect(after?.kind === 'term' && termEq(after.term, p('\\x. x'))).toBe(true)
    const replayed = replayProof(d, [res.step], ctx)
    expect(replayed).toEqual(res.diagram)
  })

  it('refuses a constant head, naming the constant and directing to unfold', () => {
    const { diagram: d, node } = diagramWith('PLUS a b', pc)
    expect(() => convertToHeadNormal(d, node, 100)).toThrowError(/PLUS/)
    expect(() => convertToHeadNormal(d, node, 100)).toThrowError(/unfold/i)
  })

  it('refuses a constant head even when head reduction recorded steps before hitting it', () => {
    const { diagram: d, node } = diagramWith('(\\u. PLUS u) a', pc)
    expect(() => convertToHeadNormal(d, node, 100)).toThrowError(/PLUS/)
    expect(() => convertToHeadNormal(d, node, 100)).toThrowError(/unfold/i)
  })

  it('refuses an already-head-normal node rather than emitting a no-op step', () => {
    const { diagram: d, node } = diagramWith('f y')
    expect(() => convertToHeadNormal(d, node, 100)).toThrowError(/already in head-normal form/i)
  })

  it('propagates fuel exhaustion on a divergent head, naming the fuel', () => {
    const { diagram: d, node } = diagramWith('(\\x. x x) (\\x. x x)')
    expect(() => convertToHeadNormal(d, node, 25)).toThrowError(/fuel/i)
    expect(() => convertToHeadNormal(d, node, 25)).toThrowError(/25/)
  })
})

describe('convertToWeakHeadNormal', () => {
  it('reduces a top-level redex until a lambda is exposed, then stops; the step replays', () => {
    const { diagram: d, node } = diagramWith('(\\u. u) (\\x. (\\v. v) x)')
    const res = convertToWeakHeadNormal(d, node, 100)
    const after = res.diagram.nodes[node]
    expect(after?.kind === 'term' && termEq(after.term, p('\\x. (\\v. v) x'))).toBe(true)
    const replayed = replayProof(d, [res.step], ctx)
    expect(replayed).toEqual(res.diagram)
  })

  it('refuses a node already in weak head-normal form rather than emitting a no-op step', () => {
    const { diagram: d, node } = diagramWith('\\x. (\\u. u) x')
    expect(() => convertToWeakHeadNormal(d, node, 100)).toThrowError(/already in weak head-normal form/i)
  })

  it('treats a top-level lambda over a constant head as already weak head-normal, not a constant-head refusal', () => {
    const { diagram: d, node } = diagramWith('\\x. PLUS x', pc)
    expect(() => convertToWeakHeadNormal(d, node, 100)).toThrowError(/already in weak head-normal form/i)
  })

  it('refuses a constant head that blocked head reduction, naming the constant and directing to unfold', () => {
    const { diagram: d, node } = diagramWith('(\\u. u) (PLUS a)', pc)
    expect(() => convertToWeakHeadNormal(d, node, 100)).toThrowError(/PLUS/)
    expect(() => convertToWeakHeadNormal(d, node, 100)).toThrowError(/unfold/i)
  })
})
