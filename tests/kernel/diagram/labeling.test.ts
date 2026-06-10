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
})
