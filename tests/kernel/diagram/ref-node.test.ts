import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram, requiredPorts } from '../../../src/kernel/diagram/diagram'
import { diagramToJson, diagramFromJson } from '../../../src/kernel/diagram/json'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { spliceSubgraph } from '../../../src/kernel/diagram/subgraph/splice'
import { findOccurrences } from '../../../src/kernel/diagram/subgraph/match'
import { applyIteration, applyDeiteration } from '../../../src/kernel/rules/iteration'
import { parseTerm } from '../../../src/kernel/term/parse'

const p = (s: string) => parseTerm(s)

/** A single ℕ(a)-shaped reference: one ref node of the given arity, its arg
 *  wires auto-attached as singleton bare wires. */
function loneRef(defId: string, arity: number) {
  const b = new DiagramBuilder()
  const node = b.ref(b.root, defId, arity)
  return { d: b.build(), node }
}

describe('ref node — construction and required ports', () => {
  it('has arg ports 0..arity-1 and NO output', () => {
    const { d, node } = loneRef('Nat', 2)
    const n = d.nodes[node]!
    expect(n.kind).toBe('ref')
    const keys = requiredPorts(d, n).map((q) => (q.kind === 'arg' ? `a${q.index}` : q.kind)).sort()
    expect(keys).toEqual(['a0', 'a1'])
  })

  it('arity 0 ref has no ports at all', () => {
    const { d, node } = loneRef('Zero', 0)
    expect(requiredPorts(d, d.nodes[node]!)).toEqual([])
  })
})

describe('ref node — mkDiagram validation', () => {
  it('rejects a ref with negative arity', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: -1 } },
      wires: {},
    })).toThrow(/arity/)
  })

  it('rejects a ref with a non-integer arity', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: 1.5 } },
      wires: {},
    })).toThrow(/arity/)
  })

  it('rejects an endpoint on an arg index >= arity', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: 1 } },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'arg', index: 0 } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'arg', index: 1 } }] },
      },
    })).toThrow(/non-existent port 'a:1'/)
  })

  it('rejects an output endpoint on a ref (refs have no output)', () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: 0 } },
      wires: { w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })).toThrow(/non-existent port 'out'/)
  })
})

describe('ref node — JSON', () => {
  it('round-trips through JSON preserving defId and arity', () => {
    const { d } = loneRef('Nat', 2)
    const back = diagramFromJson(JSON.parse(JSON.stringify(diagramToJson(d))))
    expect(exploreForm(back)).toBe(exploreForm(d))
    const n = Object.values(back.nodes)[0]!
    expect(n).toMatchObject({ kind: 'ref', defId: 'Nat', arity: 2 })
  })

  it('rejects an unknown field on a ref node (strict keys)', () => {
    expect(() => diagramFromJson({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: 0, extra: 1 } },
      wires: {},
    })).toThrow(/unknown field 'extra'/)
  })

  it('rejects a ref whose arity is not a non-negative integer', () => {
    expect(() => diagramFromJson({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: -1 } },
      wires: {},
    })).toThrow()
    expect(() => diagramFromJson({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', defId: 'Nat', arity: 1.5 } },
      wires: {},
    })).toThrow()
  })

  it('rejects a ref missing defId', () => {
    expect(() => diagramFromJson({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'ref', region: 'r0', arity: 0 } },
      wires: {},
    })).toThrow()
  })
})

describe('ref node — canonical fingerprint (soundness pin)', () => {
  it('two refs identical in defId/arity/wiring have EQUAL fingerprints', () => {
    expect(exploreForm(loneRef('Nat', 1).d)).toBe(exploreForm(loneRef('Nat', 1).d))
  })

  it('two refs identical except defId have DIFFERENT fingerprints', () => {
    // The survey soundness case: an atom-blind content key would collapse these.
    expect(exploreForm(loneRef('Nat', 1).d)).not.toBe(exploreForm(loneRef('Fin', 1).d))
  })

  it('a ref and an atom of the same arity have DIFFERENT fingerprints', () => {
    const atomD = (() => {
      const b = new DiagramBuilder()
      const bub = b.bubble(b.root, 1)
      b.atom(bub, bub)
      return b.build()
    })()
    expect(exploreForm(loneRef('Nat', 1).d)).not.toBe(exploreForm(atomD))
  })
})

/** Pattern: a single ref node of arity 1 with its arg wire as the boundary. */
function refPattern(defId: string) {
  const b = new DiagramBuilder()
  const node = b.ref(b.root, defId, 1)
  const stub = b.wire(b.root, [{ node, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(b.build(), [stub])
}

describe('ref node — matcher', () => {
  it('ref matches ref of the same defId with the arg wire aligned', () => {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, 'Nat', 1)
    const carrier = b.termNode(b.root, p('y'))
    const wire = b.wire(b.root, [
      { node, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'y' } },
    ])
    const host = b.build()
    const r = findOccurrences(host, refPattern('Nat'), { fuel: 100 })
    expect(r.matches).toHaveLength(1)
    expect(r.matches[0]?.nodeMap.get('n0')).toBe(node)
    expect(r.matches[0]?.attachments).toEqual([wire])
  })

  it('ref does not match a ref of a different defId', () => {
    const b = new DiagramBuilder()
    b.ref(b.root, 'Fin', 1)
    const host = b.build()
    expect(findOccurrences(host, refPattern('Nat'), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('ref never matches an atom of the same arity', () => {
    const b = new DiagramBuilder()
    const bub = b.bubble(b.root, 1)
    b.atom(bub, bub)
    const host = b.build()
    expect(findOccurrences(host, refPattern('Nat'), { fuel: 100 }).matches).toHaveLength(0)
  })

  it('ref never matches a term node', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('y'))
    const host = b.build()
    expect(findOccurrences(host, refPattern('Nat'), { fuel: 100 }).matches).toHaveLength(0)
  })
})

describe('ref node — iteration round-trip', () => {
  it('iterates a ref-containing subgraph into a cut and deiterates it back', () => {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, 'Nat', 1)
    const carrier = b.termNode(b.root, p('y'))
    b.wire(b.root, [
      { node, port: { kind: 'arg', index: 0 } },
      { node: carrier, port: { kind: 'freeVar', name: 'y' } },
    ])
    const cut = b.cut(b.root)
    const d0 = b.build()
    const sel = mkSelection(d0, { region: d0.root, regions: [], nodes: [node], wires: [] })
    const iterated = applyIteration(d0, sel, cut)
    // a copied ref now lives inside the cut
    const inCut = Object.values(iterated.nodes).filter((n) => n.kind === 'ref' && n.region === cut)
    expect(inCut).toHaveLength(1)
    expect(inCut[0]).toMatchObject({ kind: 'ref', defId: 'Nat', arity: 1 })
    // deiterate the copy back out
    const copyId = Object.entries(iterated.nodes).find(([, n]) => n.kind === 'ref' && n.region === cut)![0]
    const selCopy = mkSelection(iterated, { region: cut, regions: [], nodes: [copyId], wires: [] })
    const back = applyDeiteration(iterated, selCopy, 100)
    expect(exploreForm(back)).toBe(exploreForm(d0))
  })
})

describe('ref node — extract/splice preserve defId and arity', () => {
  it('extract carries defId/arity verbatim; splice back restores the diagram', () => {
    const b = new DiagramBuilder()
    const node = b.ref(b.root, 'Nat', 2)
    const carrierA = b.termNode(b.root, p('y'))
    const carrierB = b.termNode(b.root, p('z'))
    b.wire(b.root, [
      { node, port: { kind: 'arg', index: 0 } },
      { node: carrierA, port: { kind: 'freeVar', name: 'y' } },
    ])
    b.wire(b.root, [
      { node, port: { kind: 'arg', index: 1 } },
      { node: carrierB, port: { kind: 'freeVar', name: 'z' } },
    ])
    const d0 = b.build()
    const sel = mkSelection(d0, { region: d0.root, regions: [], nodes: [node], wires: [] })
    const { pattern, attachments } = extractSubgraph(d0, sel)
    const extractedRef = Object.values(pattern.diagram.nodes).find((n) => n.kind === 'ref')!
    expect(extractedRef).toMatchObject({ kind: 'ref', defId: 'Nat', arity: 2 })
    // Splice the extracted copy into a fresh cut and confirm the payload lands intact.
    const withCut = mkDiagram({
      root: d0.root,
      regions: { ...d0.regions, cutX: { kind: 'cut', parent: d0.root } },
      nodes: { ...d0.nodes },
      wires: { ...d0.wires },
    })
    const spliced = spliceSubgraph(withCut, 'cutX', pattern, attachments)
    const inCut = Object.values(spliced.nodes).filter((n) => n.kind === 'ref' && n.region === 'cutX')
    expect(inCut[0]).toMatchObject({ kind: 'ref', defId: 'Nat', arity: 2 })
  })
})
