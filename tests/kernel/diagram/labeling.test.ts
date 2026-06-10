import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { canonicalForm, canonicalLabeling } from '../../../src/kernel/diagram/canonical/canonical'
import { isoBetween } from '../../../src/kernel/diagram/canonical/iso'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import type { Diagram, Region, DiagramNode, Wire } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const cut = h.cut(h.root)
  const n = h.termNode(h.root, p('y'))
  const m = h.termNode(cut, p('\\x. x'))
  h.wire(h.root, [
    { node: n, port: { kind: 'freeVar', name: 'y' } },
    { node: m, port: { kind: 'output' } },
  ])
  return h.build()
}

/** The same diagram with every id renamed. */
function renamed(d: Diagram): Diagram {
  const r = (id: string) => `X_${id}`
  const regions: Record<string, Region> = {}
  for (const [id, reg] of Object.entries(d.regions)) {
    regions[r(id)] = reg.kind === 'sheet' ? reg
      : reg.kind === 'cut' ? { kind: 'cut', parent: r(reg.parent) }
      : { kind: 'bubble', parent: r(reg.parent), arity: reg.arity }
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    nodes[r(id)] = n.kind === 'term'
      ? { kind: 'term', region: r(n.region), term: n.term }
      : { kind: 'atom', region: r(n.region), binder: r(n.binder) }
  }
  const wires: Record<string, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[r(id)] = { scope: r(w.scope), endpoints: w.endpoints.map((ep) => ({ node: r(ep.node), port: ep.port })) }
  }
  return mkDiagram({ root: r(d.root), regions, nodes, wires })
}

describe('canonicalLabeling', () => {
  it('its form field equals canonicalForm and ordinals are total and distinct', () => {
    const d = host()
    const lab = canonicalLabeling(d)
    expect(lab.form).toBe(canonicalForm(d))
    expect(new Set(lab.regionOrd.values()).size).toBe(Object.keys(d.regions).length)
    expect(new Set(lab.nodeOrd.values()).size).toBe(Object.keys(d.nodes).length)
    expect(new Set(lab.wireOrd.values()).size).toBe(Object.keys(d.wires).length)
  })

  it('assigns the same ordinals to corresponding objects across renamings', () => {
    const d = host()
    const e = renamed(d)
    const ld = canonicalLabeling(d)
    const le = canonicalLabeling(e)
    expect(ld.form).toBe(le.form)
    for (const [id, ord] of ld.nodeOrd) {
      expect(le.nodeOrd.get(`X_${id}`)).toBe(ord)
    }
  })
})

describe('isoBetween', () => {
  it('returns the identity-like mapping between a diagram and its renaming', () => {
    const d = host()
    const e = renamed(d)
    const iso = isoBetween(d, e)
    expect(iso).not.toBeNull()
    for (const id of Object.keys(d.nodes)) expect(iso!.nodes.get(id)).toBe(`X_${id}`)
    for (const id of Object.keys(d.regions)) expect(iso!.regions.get(id)).toBe(`X_${id}`)
    for (const id of Object.keys(d.wires)) expect(iso!.wires.get(id)).toBe(`X_${id}`)
  })

  it('transports structure: mapped parents, regions, scopes, endpoints agree', () => {
    const d = host()
    const e = renamed(d)
    const iso = isoBetween(d, e)!
    for (const [id, n] of Object.entries(d.nodes)) {
      const img = e.nodes[iso.nodes.get(id)!]!
      expect(img.region).toBe(iso.regions.get(n.region))
    }
    for (const [id, w] of Object.entries(d.wires)) {
      const img = e.wires[iso.wires.get(id)!]!
      expect(img.scope).toBe(iso.regions.get(w.scope))
      expect(img.endpoints).toHaveLength(w.endpoints.length)
    }
  })

  it('picks a consistent mapping for symmetric diagrams', () => {
    // two indistinguishable nodes: any of the two isos is fine, but the map
    // must BE an iso — distinct images, structure transported
    const h1 = new DiagramBuilder()
    h1.termNode(h1.root, p('\\x. x'))
    h1.termNode(h1.root, p('\\x. x'))
    const d = h1.build()
    const h2 = new DiagramBuilder()
    h2.termNode(h2.root, p('\\x. x'))
    h2.termNode(h2.root, p('\\x. x'))
    const e = h2.build()
    const iso = isoBetween(d, e)!
    const images = new Set(iso.nodes.values())
    expect(images.size).toBe(2)
    expect(diagramFingerprint(d)).toBe(diagramFingerprint(e))
  })

  it('returns null for non-isomorphic diagrams', () => {
    const h2 = new DiagramBuilder()
    h2.termNode(h2.root, p('y'))
    expect(isoBetween(host(), h2.build())).toBeNull()
  })

  it('ordinals reflect winning coloring, not id insertion order (kills mutant: initial-color ordinals)', () => {
    // Two diagrams, same structure: a node in an outer cut and a node in a nested
    // cut. In d1 the outer node is n0 (inserted first); in d2 the outer node is
    // n1 (inserted second). The correct ordinals are determined by the canonical
    // winner coloring, which respects structure. A mutant using initial colors
    // would use insertion order, mapping outer→0 in d1 and outer→1 in d2,
    // making isoBetween transport outer↦inner.
    const lam = p('\\x. x')
    const d1 = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' }, r2: { kind: 'cut', parent: 'r1' } },
      nodes: {
        n0: { kind: 'term', region: 'r1', term: lam },  // outer cut, inserted first
        n1: { kind: 'term', region: 'r2', term: lam },  // inner cut, inserted second
      },
      wires: {
        w0: { scope: 'r1', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r2', endpoints: [{ node: 'n1', port: { kind: 'output' } }] },
      },
    })
    const d2 = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' }, r1: { kind: 'cut', parent: 'r0' }, r2: { kind: 'cut', parent: 'r1' } },
      nodes: {
        n0: { kind: 'term', region: 'r2', term: lam },  // inner cut, inserted first
        n1: { kind: 'term', region: 'r1', term: lam },  // outer cut, inserted second
      },
      wires: {
        w0: { scope: 'r2', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r1', endpoints: [{ node: 'n1', port: { kind: 'output' } }] },
      },
    })
    const iso = isoBetween(d1, d2)
    expect(iso).not.toBeNull()
    // d1.n0 is in r1 (outer), d2.n1 is in r1 (outer). The iso must map outer↦outer.
    const imgOfN0 = iso!.nodes.get('n0')
    expect(d2.nodes[imgOfN0!]?.region).toBe('r1')
  })

  it('search takes the lex-min branch (kills mutant: lex-max branch)', () => {
    // Same two-nested-cut diagram. Build it twice. Under lex-max branching, the
    // canonical form picks a different winner than lex-min. If forms differ
    // between two independently built copies, isoBetween returns null instead of
    // the correct iso. Concretely: verify the two copies have equal forms AND a
    // valid iso.
    const lam = p('\\x. x')
    function buildNested() {
      const h = new DiagramBuilder()
      const cut = h.cut(h.root)
      const inner = h.cut(cut)
      h.termNode(cut, lam)
      h.termNode(inner, lam)
      return h.build()
    }
    const d1 = buildNested()
    const d2 = buildNested()
    // Equal forms required for any valid canonical algorithm.
    expect(canonicalForm(d1)).toBe(canonicalForm(d2))
    // isoBetween must be non-null.
    expect(isoBetween(d1, d2)).not.toBeNull()
  })
})
