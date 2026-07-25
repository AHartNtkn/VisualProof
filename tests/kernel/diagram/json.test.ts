import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramToJson, diagramFromJson, sigFromJson, sigToJson } from '../../../src/kernel/diagram/json'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { relSig, IOTA } from '../../../src/kernel/diagram/sig'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'

const p = (s: string) => parseTerm(s)

/** Content for a nullary-parameter body: one iota arg stub fed by `\z. z`. */
function bodyContent() {
  const cb = new DiagramBuilder()
  const inner = cb.termNode(cb.root, p('\\z. z'))
  const argWire = cb.wire(cb.root, [{ node: inner, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(cb.build(), [argWire])
}

/** A cut holding a depth-2 atom (sig `((t),(t),t)`), a term node sharing its
 * iota argument, and a body node — exercises sig, body content, and recursion. */
function sample() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const t = b.termNode(cut, p('\\x. y x'))                        // n0
  const a = b.atom(cut, relSig([relSig([IOTA]), relSig([IOTA]), IOTA]))  // n1
  b.wire(cut, [
    { node: t, port: { kind: 'output' } },
    { node: a, port: { kind: 'arg', index: 2 } },
  ])                                                              // w0
  b.body(cut, relSig([IOTA]), bodyContent())                     // n2
  return b.build()
}

describe('diagram JSON', () => {
  it('serializes iota and rejects the legacy term signature', () => {
    expect(sigToJson(IOTA)).toEqual({ kind: 'iota' })
    expect(() => sigFromJson({ kind: 'term' }, 'wire')).toThrow(/kind.*iota.*rel/)
  })

  it('round-trips an unused declared term port and requires the declaration in strict JSON', () => {
    const b = new DiagramBuilder()
    const nodeId = b.termNode(b.root, p('used'), ['unused', 'used'])
    const d = b.build()
    const encoded = diagramToJson(d) as {
      nodes: Record<string, { freePorts?: string[] }>
    }
    expect(encoded.nodes[nodeId]!.freePorts).toEqual(['s0', 's1'])
    const decoded = diagramFromJson(encoded)
    const node = decoded.nodes[nodeId]
    expect(node?.kind).toBe('term')
    if (node?.kind !== 'term') throw new Error('test setup requires a term node')
    expect(node.freePorts).toEqual(['s0', 's1'])

    const missing = JSON.parse(JSON.stringify(encoded)) as {
      nodes: Record<string, Record<string, unknown>>
    }
    delete missing.nodes[nodeId]!['freePorts']
    expect(() => diagramFromJson(missing)).toThrowError(/node.*unrecognized shape/i)
  })

  it('round-trips structurally: toJson ∘ fromJson ∘ toJson is the identity on JSON', () => {
    const d = sample()
    const j1 = diagramToJson(d)
    const d2 = diagramFromJson(j1)
    const j2 = diagramToJson(d2)
    expect(JSON.stringify(j2)).toBe(JSON.stringify(j1))
  })

  it('round-trips a depth-2 atom and a body node by deep equality and fingerprint', () => {
    const d = sample()
    const decoded = diagramFromJson(JSON.parse(JSON.stringify(diagramToJson(d))))
    expect(decoded).toEqual(d)
    expect(exploreForm(decoded)).toBe(exploreForm(d))
  })

  it('decodes signatures recursively and rejects malformed ones loudly', () => {
    const d = sample()
    const good = JSON.parse(JSON.stringify(diagramToJson(d))) as {
      nodes: Record<string, { sig?: unknown }>
      wires: Record<string, { sig?: unknown }>
    }
    // n1 is the depth-2 atom
    expect(good.nodes['n1']!.sig).toEqual({
      kind: 'rel',
      args: [{ kind: 'rel', args: [{ kind: 'iota' }] }, { kind: 'rel', args: [{ kind: 'iota' }] }, { kind: 'iota' }],
    })
    const badKind = JSON.parse(JSON.stringify(good)) as { nodes: Record<string, { sig: { kind: string } }> }
    badKind.nodes['n1']!.sig.kind = 'bubble'
    expect(() => diagramFromJson(badKind)).toThrowError(/malformed diagram JSON.*"kind" must be "iota" or "rel"/)
    const extraKey = JSON.parse(JSON.stringify(good)) as { wires: Record<string, { sig: Record<string, unknown> }> }
    const someWire = Object.keys(extraKey.wires)[0]!
    extraKey.wires[someWire]!.sig['smuggled'] = 1
    expect(() => diagramFromJson(extraKey)).toThrowError(/carries extra fields/)
  })

  it('rejects bubble/binder vocabulary from the old model as unknown', () => {
    const d = sample()
    const withBubble = JSON.parse(JSON.stringify(diagramToJson(d))) as { regions: Record<string, unknown> }
    withBubble.regions['rb'] = { kind: 'bubble', parent: 'r0', arity: 2 }
    expect(() => diagramFromJson(withBubble)).toThrowError(/region 'rb' has unrecognized shape/)
    const withBinder = JSON.parse(JSON.stringify(diagramToJson(d))) as { nodes: Record<string, unknown> }
    withBinder.nodes['n1'] = { kind: 'atom', region: 'r1', binder: 'rb' }
    expect(() => diagramFromJson(withBinder)).toThrowError(/node 'n1' has unrecognized shape/)
  })

  it('serializes terms via the injective term serialization (canonical port names)', () => {
    const d = sample()
    const j = diagramToJson(d) as { nodes: Record<string, { kind: string; term?: string }> }
    expect(j.nodes['n0']?.term).toBe('L(A(P("s0"),#0))')
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
