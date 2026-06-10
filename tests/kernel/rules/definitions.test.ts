import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyUnfold, applyFold, assertWellFormedDefinitions } from '../../../src/kernel/rules/definitions'
import type { Definitions } from '../../../src/kernel/rules/definitions'

const consts = new Set(['I', 'K'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = { I: pp('\\x. x'), K: pp('\\x. \\y. x') }

describe('assertWellFormedDefinitions', () => {
  it('accepts closed bodies and rejects port-bearing or bvar-open ones, by name', () => {
    expect(() => assertWellFormedDefinitions(defs)).not.toThrow()
    expect(() => assertWellFormedDefinitions({ bad: pp('y') }))
      .toThrowError(/free ports/)
    let caught: unknown
    try { assertWellFormedDefinitions({ bad: { kind: 'bvar', index: 0 } }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })
})

describe('applyUnfold / applyFold', () => {
  it('unfold replaces a constant by its body; fold inverts it (fingerprint)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyUnfold(d, defs, n, ['fn'])
    const un = unfolded.nodes[n]
    expect(un?.kind === 'term' && printTerm(un.term)).toBe(printTerm(p('(\\x. x) y')))
    const refolded = applyFold(unfolded, defs, n, ['fn'], 'I')
    expect(diagramFingerprint(refolded)).toBe(diagramFingerprint(d))
  })

  it('unfold works under binders (closed bodies need no shifting)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\z. K z'))
    const d = h.build()
    const out = applyUnfold(d, defs, n, ['body', 'fn'])
    const on = out.nodes[n]
    expect(on?.kind === 'term' && printTerm(on.term)).toBe(printTerm(p('\\z. (\\x. \\y. x) z')))
  })

  it('unfold rejects non-constants and unknown definitions, by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    expect(() => applyUnfold(d, defs, n, ['arg'])).toThrowError(/expects a constant/)
    expect(() => applyUnfold(d, { K: defs['K']! }, n, ['fn'])).toThrowError(/no definition for constant 'I'/)
  })

  it('fold demands syntactic equality, pointing at conversion otherwise', () => {
    // NOTE: `\a. a` would NOT do here — de Bruijn terms are α-canonical, so it
    // IS termEq to the definition `\x. x`. Use a term that is merely
    // βη-convertible to it: `\a. (\b. b) a` (β-reduces to the identity).
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\a. (\\b. b) a) y'))
    const d = h.build()
    expect(() => applyFold(d, defs, n, ['fn'], 'I'))
      .toThrowError(/not syntactically the definition/)
  })

  it('fold works inside nested regions, leaving wires untouched', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('(\\x. x) y'))
    const d = h.build()
    const out = applyFold(d, defs, n, ['fn'], 'I')
    const on = out.nodes[n]
    expect(on?.kind === 'term' && printTerm(on.term)).toBe(printTerm(p('I y')))
    expect(Object.keys(out.wires).sort()).toEqual(Object.keys(d.wires).sort())
  })
})
