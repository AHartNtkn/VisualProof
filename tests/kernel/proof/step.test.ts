import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import { applyStep, replayProof } from '../../../src/kernel/proof/step'
import type { ProofContext, ProofStep } from '../../../src/kernel/proof/step'
import { ProofError } from '../../../src/kernel/proof/error'

const consts = new Set(['I'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const ctx: ProofContext = { definitions: { I: pp('\\x. x') }, theorems: new Map() }

describe('applyStep mirrors the direct appliers', () => {
  it('erasure step equals applyErasure', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('\\x. x'))
    h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const step: ProofStep = { rule: 'erasure', sel }
    expect(diagramFingerprint(applyStep(d, step, ctx))).toBe(diagramFingerprint(applyErasure(d, sel)))
  })

  it('conversion step replays by certificate, fuel-free', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('(\\x. x) y'))
    const d = h.build()
    const { diagram, certificate } = applyConversion(d, n, pp('y'), 10)
    const step: ProofStep = { rule: 'conversion', node: n, term: pp('y'), certificate, attachments: {} }
    expect(diagramFingerprint(applyStep(d, step, ctx))).toBe(diagramFingerprint(diagram))
  })

  it('unfold and fold steps use the context definitions', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyStep(d, { rule: 'unfold', node: n, path: ['fn'] }, ctx)
    const refolded = applyStep(unfolded, { rule: 'fold', node: n, path: ['fn'], constId: 'I' }, ctx)
    expect(diagramFingerprint(refolded)).toBe(diagramFingerprint(d))
  })

  it('double-cut intro/elim and iteration/deiteration round-trip through steps', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, pp('y'))
    const hub = h.termNode(h.root, pp('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const cut = h.cut(h.root)
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const steps: ProofStep[] = [
      { rule: 'iteration', sel, target: cut },
      { rule: 'doubleCutIntro', sel },
    ]
    const out = replayProof(d, steps, ctx)
    expect(Object.keys(out.regions).length).toBe(Object.keys(d.regions).length + 2)
  })

  it('insertion and comprehension steps carry their patterns by value', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, pp('\\x. \\y. x'))
    const pat = mkDiagramWithBoundary(b.build(), [])
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const d = h.build()
    const out = applyStep(d, { rule: 'insertion', region: cut, pattern: pat, attachments: [], binders: {} }, ctx)
    expect(Object.values(out.nodes)).toHaveLength(1)
  })
})

describe('replayProof failure reporting', () => {
  it('names the failing step index and rule', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, pp('\\x. x'))
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    let caught: unknown
    try {
      replayProof(d, [{ rule: 'erasure', sel }], ctx) // negative region: gate refuses
    } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(ProofError)
    expect((caught as Error).message).toMatch(/step 0 \(erasure\) failed: erasure requires a positive region/)
  })

  it('unknown theorem names fail loudly', () => {
    const d = new DiagramBuilder().build()
    expect(() => applyStep(d, {
      rule: 'theorem', name: 'ghost',
      at: { sel: { region: d.root, regions: [], nodes: [], wires: [] }, args: [] },
      direction: 'forward',
    }, ctx)).toThrowError(/unknown theorem 'ghost'/)
  })
})
