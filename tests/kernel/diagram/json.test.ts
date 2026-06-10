import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson, diagramFromJson } from '../../../src/kernel/diagram/json'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function sample() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const bub = b.bubble(cut, 2)
  const t = b.termNode(bub, p('\\x. y x'))
  const a = b.atom(bub, bub)
  b.wire(bub, [
    { node: t, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 0 } },
    { node: a, port: { kind: 'arg', index: 1 } },
  ])
  return b.build()
}

describe('diagram JSON', () => {
  it('round-trips structurally: toJson ∘ fromJson ∘ toJson is the identity on JSON', () => {
    const d = sample()
    const j1 = diagramToJson(d)
    const d2 = diagramFromJson(j1)
    const j2 = diagramToJson(d2)
    expect(JSON.stringify(j2)).toBe(JSON.stringify(j1))
  })

  it('serializes terms via the injective term serialization', () => {
    const d = sample()
    const j = diagramToJson(d) as { nodes: Record<string, { kind: string; term?: string }> }
    expect(j.nodes['n0']?.term).toBe('L(A(P("y"),#0))')
  })

  it('rejects malformed JSON loudly: bad shape, bad port key, bad term', () => {
    expect(() => diagramFromJson(null)).toThrowError(/malformed diagram/i)
    expect(() => diagramFromJson({ root: 'r0' })).toThrowError(/malformed diagram/i)
    const d = sample()
    const good = JSON.parse(JSON.stringify(diagramToJson(d))) as Record<string, unknown>
    const badPort = JSON.parse(JSON.stringify(good)) as { wires: Record<string, { endpoints: { port: string }[] }> }
    badPort.wires['w0']!.endpoints[0]!.port = 'zzz'
    expect(() => diagramFromJson(badPort)).toThrowError(/malformed diagram.*port key 'zzz'/i)
    const badTerm = JSON.parse(JSON.stringify(good)) as { nodes: Record<string, { term?: string }> }
    badTerm.nodes['n0']!.term = 'garbage'
    expect(() => diagramFromJson(badTerm)).toThrowError(/malformed diagram JSON.*node 'n0'/i)
  })

  it('rejects unknown fields anywhere (no layout smuggling into semantic files)', () => {
    const base = JSON.parse(JSON.stringify(diagramToJson(sample()))) as Record<string, unknown>
    const withRegionField = JSON.parse(JSON.stringify(base)) as { regions: Record<string, Record<string, unknown>> }
    withRegionField.regions['r1']!['color'] = 'red'
    expect(() => diagramFromJson(withRegionField)).toThrowError(/unknown field 'color'/)

    const withNodeField = JSON.parse(JSON.stringify(base)) as { nodes: Record<string, Record<string, unknown>> }
    withNodeField.nodes['n0']!['x'] = 12
    expect(() => diagramFromJson(withNodeField)).toThrowError(/unknown field 'x'/)

    const withWireField = JSON.parse(JSON.stringify(base)) as { wires: Record<string, Record<string, unknown>> }
    withWireField.wires['w0']!['bend'] = 0.5
    expect(() => diagramFromJson(withWireField)).toThrowError(/unknown field 'bend'/)

    const topLevel = JSON.parse(JSON.stringify(base)) as Record<string, unknown>
    topLevel['layout'] = {}
    expect(() => diagramFromJson(topLevel)).toThrowError(/unknown field 'layout'/)
  })

  it('rejects non-canonical arg port keys', () => {
    const bad = JSON.parse(JSON.stringify(diagramToJson(sample()))) as { wires: Record<string, { endpoints: { port: string }[] }> }
    bad.wires['w0']!.endpoints[1]!.port = 'a:1e2'
    expect(() => diagramFromJson(bad)).toThrowError(/port key 'a:1e2'/)
  })

  it('re-validates: structurally well-shaped JSON encoding an invalid diagram is rejected', () => {
    const d = sample()
    const j = JSON.parse(JSON.stringify(diagramToJson(d))) as { nodes: Record<string, { region: string }> }
    j.nodes['n0']!.region = 'ghost'
    expect(() => diagramFromJson(j)).toThrowError(/missing region 'ghost'/)
  })

  it('requires all four top-level keys as objects (no null, no absence)', () => {
    const base = JSON.parse(JSON.stringify(diagramToJson(sample()))) as Record<string, unknown>
    const noNodes = JSON.parse(JSON.stringify(base)) as Record<string, unknown>
    delete noNodes['nodes']
    expect(() => diagramFromJson(noNodes)).toThrowError(/malformed diagram/)
    const nullWires = JSON.parse(JSON.stringify(base)) as Record<string, unknown>
    nullWires['wires'] = null
    expect(() => diagramFromJson(nullWires)).toThrowError(/malformed diagram/)
  })
})
