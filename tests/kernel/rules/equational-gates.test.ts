import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import {
  applyConversion, applyFusion, applyFission, applyUnfold, applyFold,
  applyComprehensionInstantiate, applyComprehensionAbstract,
} from '../../../src/kernel/rules/index'
import type { Definitions } from '../../../src/kernel/rules/index'

const consts = new Set(['I'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)
const defs: Definitions = { I: pp('\\x. x') }

function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, pp('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('equational rules are polarity-free at depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    it(`depth ${depth}: conversion, fission/fusion, unfold/fold all apply`, () => {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, p('I ((\\x. x) y)'))
      const d = h.build()

      expect(() => applyUnfold(d, defs, n, ['fn'])).not.toThrow()
      expect(() => applyFold(applyUnfold(d, defs, n, ['fn']), defs, n, ['fn'], 'I')).not.toThrow()
      // the node's source free 'y' is canonical s0 after construction
      expect(() => applyConversion(d, n, p('I s0'), 10)).not.toThrow()

      const split = applyFission(d, n, ['arg'])
      const newWire = Object.keys(split.wires).find(
        (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
      )!
      expect(diagramFingerprint(applyFusion(split, newWire))).toBe(diagramFingerprint(d))
    })
  }
})

describe('comprehension gates mirror insertion/erasure parity', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0
    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): abstract ${positive ? 'allowed' : 'rejected'}, instantiate ${positive ? 'rejected' : 'allowed'}`, () => {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, pp('\\x. x'))
      const bub = h.bubble(region, 1)
      const d = h.build()
      const w = Object.entries(d.wires).find(([, wv]) => wv.endpoints.some((ep) => ep.node === n))![0]
      const wrap = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const occ = { sel: mkSelection(d, { region, regions: [], nodes: [n], wires: [] }), args: [w] }
      if (positive) {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ])).not.toThrow()
        expect(() => applyComprehensionInstantiate(d, bub, identityComp()))
          .toThrowError(/requires a negative bubble/)
      } else {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ]))
          .toThrowError(/requires a positive region/)
        expect(() => applyComprehensionInstantiate(d, bub, identityComp())).not.toThrow()
      }
    })
  }
})

describe('cross-rule composition', () => {
  it('unfold → convert → fold normalizes through a definition', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyUnfold(d, defs, n, ['fn'])
    // the node's source free 'y' is canonical s0 after construction
    const { diagram: converted } = applyConversion(unfolded, n, p('s0'), 10)
    const back = applyConversion(converted, n, p('(\\x. x) s0'), 10).diagram
    expect(diagramFingerprint(applyFold(back, defs, n, ['fn'], 'I'))).toBe(diagramFingerprint(d))
  })
})
