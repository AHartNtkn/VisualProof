import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import {
  applyConversion, applyFusion, applyFission,
  applyComprehensionInstantiate, applyComprehensionAbstract,
} from '../../../src/kernel/rules/index'

const p = (s: string) => parseTerm(s)

function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('equational rules are polarity-free at depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    it(`depth ${depth}: conversion, fission/fusion all apply`, () => {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, p('f ((\\x. x) y)'))
      const d = h.build()

      // the node's free ports f, y are positional s0, s1; conversion contracts
      // the inner redex, leaving f y
      expect(() => applyConversion(d, n, p('s0 s1'), 10)).not.toThrow()

      const split = applyFission(d, n, ['arg'])
      const newWire = Object.keys(split.wires).find(
        (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
      )!
      expect(exploreForm(applyFusion(split, newWire))).toBe(exploreForm(d))
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
      const n = h.termNode(region, p('\\x. x'))
      const bub = h.bubble(region, 1)
      const d = h.build()
      const w = Object.entries(d.wires).find(([, wv]) => wv.endpoints.some((ep) => ep.node === n))![0]
      const wrap = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const occ = { sel: mkSelection(d, { region, regions: [], nodes: [n], wires: [] }), args: [w] }
      if (positive) {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ])).not.toThrow()
        expect(() => applyComprehensionInstantiate(d, bub, identityComp(), []))
          .toThrowError(/requires a negative bubble/)
      } else {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ]))
          .toThrowError(/requires a positive region/)
        expect(() => applyComprehensionInstantiate(d, bub, identityComp(), [])).not.toThrow()
      }
    })
  }
})
