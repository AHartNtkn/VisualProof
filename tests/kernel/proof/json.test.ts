import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import type { ProofStep } from '../../../src/kernel/proof/step'
import { stepToJson, stepFromJson, theoremToJson, theoremFromJson } from '../../../src/kernel/proof/json'
import type { Theorem } from '../../../src/kernel/proof/theorem'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function roundTrip(s: ProofStep): void {
  const j = JSON.parse(JSON.stringify(stepToJson(s)))
  expect(stepFromJson(j)).toEqual(s)
}

describe('step round-trips through JSON', () => {
  it('covers every step kind', () => {
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const pat = mkDiagramWithBoundary(b.build(), [bw])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { certificate } = applyConversion(d, n, p('y'), 10)

    const sel = { region: 'r0', regions: ['r1'], nodes: ['n0'], wires: ['w0'] }
    const steps: ProofStep[] = [
      { rule: 'insertion', region: 'r1', pattern: pat, attachments: ['w0'] },
      { rule: 'wireJoin', a: 'w0', b: 'w1' },
      { rule: 'erasure', sel },
      { rule: 'wireSever', wire: 'w0', keep: [{ node: 'n0', port: { kind: 'freeVar', name: 'y' } }] },
      { rule: 'iteration', sel, target: 'r1' },
      { rule: 'deiteration', sel, fuel: 50 },
      { rule: 'doubleCutIntro', sel },
      { rule: 'doubleCutElim', region: 'r1' },
      { rule: 'conversion', node: 'n0', term: p('y'), certificate, attachments: { z: 'w0' } },
      { rule: 'fusion', wire: 'w0' },
      { rule: 'fission', node: 'n0', path: ['fn', 'arg'] },
      { rule: 'unfold', node: 'n0', path: [] },
      { rule: 'fold', node: 'n0', path: ['body'], constId: 'I' },
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat },
      { rule: 'comprehensionAbstract', wrap: sel, comp: pat, occurrences: [{ sel, args: ['w0'] }] },
      { rule: 'theorem', name: 'dropQ', at: { sel, args: ['w0'] }, direction: 'reverse' },
    ]
    for (const s of steps) roundTrip(s)
  })

  it('rejects malformed steps loudly', () => {
    expect(() => stepFromJson({ rule: 'nonsense' })).toThrowError(/malformed proof JSON/)
    expect(() => stepFromJson({ rule: 'erasure', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, extra: 1 }))
      .toThrowError(/unknown field 'extra'/)
    expect(() => stepFromJson({ rule: 'fission', node: 'n0', path: ['sideways'] }))
      .toThrowError(/path segment/)
    expect(() => stepFromJson({ rule: 'deiteration', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, fuel: -1 }))
      .toThrowError(/fuel/)
  })
})

describe('theorem round-trips through JSON', () => {
  it('preserves sides, boundary order, and steps', () => {
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lb = l.wire(l.root, [{ node: lp, port: { kind: 'output' } }])
    const side = mkDiagramWithBoundary(l.build(), [lb])
    const t: Theorem = {
      name: 'noop', lhs: side, rhs: side,
      steps: [{ rule: 'doubleCutIntro', sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] } },
              { rule: 'doubleCutElim', region: 'dc' }],
    }
    const j = JSON.parse(JSON.stringify(theoremToJson(t)))
    const back = theoremFromJson(j)
    expect(back.name).toBe('noop')
    expect(back.lhs.boundary).toEqual([lb])
    expect(back.steps).toEqual(t.steps)
  })
})
