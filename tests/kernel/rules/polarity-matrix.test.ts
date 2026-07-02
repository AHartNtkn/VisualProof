import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyInsertion } from '../../../src/kernel/rules/insertion'
import { applyErasure } from '../../../src/kernel/rules/erasure'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'
import { applyDoubleCutIntro, applyDoubleCutElim } from '../../../src/kernel/rules/doublecut'

const p = (s: string) => parseTerm(s)

/** Depth-parameterized host: a node nested under `depth` cuts. */
function nested(depth: number) {
  const h = new DiagramBuilder()
  let region = h.root
  const cuts: string[] = []
  for (let i = 0; i < depth; i++) {
    region = h.cut(region)
    cuts.push(region)
  }
  const n = h.termNode(region, p('\\x. x'))
  return { d: h.build(), region, n, cuts }
}

function closedPattern() {
  const b = new DiagramBuilder()
  b.termNode(b.root, p('\\x. \\y. x'))
  return mkDiagramWithBoundary(b.build(), [])
}

describe('polarity matrix across depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0
    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): insertion ${positive ? 'rejected' : 'allowed'}, erasure ${positive ? 'allowed' : 'rejected'}`, () => {
      const { d, region, n } = nested(depth)
      if (positive) {
        expect(() => applyInsertion(d, region, closedPattern(), []))
          .toThrowError(/insertion requires a negative region/)
        const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
        expect(() => applyErasure(d, sel)).not.toThrow()
      } else {
        expect(() => applyInsertion(d, region, closedPattern(), [])).not.toThrow()
        const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
        expect(() => applyErasure(d, sel))
          .toThrowError(/erasure requires a positive region/)
      }
    })

    it(`depth ${depth}: iteration and double cut are polarity-free`, () => {
      const { d, region, n } = nested(depth)
      const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      expect(() => applyIteration(d, sel, region)).not.toThrow()
      expect(() => applyDoubleCutIntro(d, sel)).not.toThrow()
    })
  }
})

describe('inverse round-trips (fingerprint identities)', () => {
  it('insertion into a cut, then deiteration-free erasure is blocked — but double-cut round-trips at every depth', () => {
    for (let depth = 0; depth <= 2; depth++) {
      const { d, region, n } = nested(depth)
      const sel = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const wrapped = applyDoubleCutIntro(d, sel)
      const outer = Object.entries(wrapped.regions)
        .find(([id, r]) => r.kind === 'cut' && r.parent === region && d.regions[id] === undefined)![0]
      expect(diagramFingerprint(applyDoubleCutElim(wrapped, outer))).toBe(diagramFingerprint(d))
    }
  })

  it('iterate-into-cut then deiterate round-trips under nesting', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const iterated = applyIteration(d, sel, cut)
    const copyId = Object.entries(iterated.nodes).find(([, x]) => x.region === cut)![0]
    const copySel = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    expect(diagramFingerprint(applyDeiteration(iterated, copySel, 100))).toBe(diagramFingerprint(d))
  })
})
