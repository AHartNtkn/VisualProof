import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { requiredPorts } from '../../src/kernel/diagram/diagram'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine, carryOver, worldAnchor, portNormal, pkey, DISC_R } from '../../src/view/engine'
import { emptyDiagram } from '../../src/app/edit'

const p = (s: string) => parseTerm(s)

const nat = () => {
  const b = buildFregeTheory().relations.nat!
  return { d: b.diagram, boundary: b.boundary }
}

/** How many DISTINCT legs touch a given (body, port key). */
function legsAt(legs: readonly { from: { body: string; key: string | null }; to: { body: string; key: string | null } }[], body: string, key: string): number {
  return legs.filter((l) => (l.from.body === body && l.from.key === key) || (l.to.body === body && l.to.key === key)).length
}

describe('mkEngine', () => {
  it('creates exactly one body per diagram node', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.ref(h.root, 'Nat', 1)
    const d = h.build()
    const e = mkEngine(d, [])
    const nodeBodies = [...e.bodies.values()].filter((b) => b.kind !== 'junction')
    expect(nodeBodies).toHaveLength(2)
    expect(new Set(nodeBodies.map((b) => b.id))).toEqual(new Set(Object.keys(d.nodes)))
  })

  it('ref discs use the single standard disc size (uniform-disc law)', () => {
    const h = new DiagramBuilder()
    h.ref(h.root, 'Nat', 1)
    h.ref(h.root, 'ReallyLongRelationName', 3)
    const d = h.build()
    const e = mkEngine(d, [])
    const refs = [...e.bodies.values()].filter((b) => b.kind === 'ref')
    expect(refs).toHaveLength(2)
    for (const r of refs) expect(r.discR).toBeCloseTo(DISC_R + 1.5, 10)
  })

  it('law 4: every ref/atom port has exactly one connection (leg XOR boundary exit)', () => {
    const { d, boundary } = nat()
    const e = mkEngine(d, boundary)
    // ports reached by a boundary exit rather than a leg
    const boundaryPorts = new Set<string>()
    for (const [wid, body] of e.boundaryOf) {
      const w = d.wires[wid]!
      const ep = w.endpoints.find((x) => x.node === body)
      if (ep !== undefined) boundaryPorts.add(`${body}|${pkey(ep.port)}`)
    }
    for (const [id, node] of Object.entries(d.nodes)) {
      if (node.kind === 'term') continue // term outputs may exit; law 4 is about refs/atoms
      for (const port of requiredPorts(d, node)) {
        const key = `${id}|${pkey(port)}`
        const connections = legsAt(e.legs, id, pkey(port)) + (boundaryPorts.has(key) ? 1 : 0)
        expect(connections, `port ${key}`).toBe(1)
      }
    }
  })

  it('worldAnchor rotates the local anchor about the body centre by theta', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const e = mkEngine(d, [])
    const b = e.bodies.get(n)!
    b.pos = { x: 10, y: -3 }
    b.theta = 0
    const a0 = worldAnchor(b, 'out')
    b.theta = Math.PI / 2
    const a1 = worldAnchor(b, 'out')
    // rotating the frame by +90° maps a local (lx,ly) to (-ly, lx) around pos
    const lx = a0.x - 10, ly = a0.y - -3
    expect(a1.x).toBeCloseTo(10 - ly, 9)
    expect(a1.y).toBeCloseTo(-3 + lx, 9)
    // the port normal tracks theta too
    expect(portNormal(b, 'out', { x: 100, y: -3 })).toBeCloseTo(Math.atan2(0, 1) + Math.PI / 2, 9)
  })
})

describe('carryOver', () => {
  it('shared body ids inherit pos/vel/theta from the previous engine', () => {
    const { d, boundary } = nat()
    const prev = mkEngine(d, boundary)
    // perturb prev so the carried state is unmistakably NOT a fresh seed
    let t = 0
    for (const b of prev.bodies.values()) {
      b.pos = { x: 42 + t, y: -7 - t }
      b.vel = { x: 1 + t, y: 2 }
      b.theta = 0.5 + t
      t++
    }
    const next = mkEngine(d, boundary) // same diagram → identical id set
    carryOver(prev, next)
    expect(next.bodies.size).toBe(prev.bodies.size)
    for (const [id, nb] of next.bodies) {
      const pb = prev.bodies.get(id)!
      expect(nb.pos).toEqual(pb.pos)
      expect(nb.vel).toEqual(pb.vel)
      expect(nb.theta).toBe(pb.theta)
    }
  })

  it('bodies absent from the previous engine keep their deterministic seed (new ids do not crash)', () => {
    const { d, boundary } = nat()
    const empty = mkEngine(emptyDiagram(), []) // zero bodies → nothing to carry
    const next = mkEngine(d, boundary)
    const reference = mkEngine(d, boundary) // mkEngine is deterministic: identical seeds
    expect(() => carryOver(empty, next)).not.toThrow()
    for (const [id, nb] of next.bodies) {
      const rb = reference.bodies.get(id)!
      expect(nb.pos).toEqual(rb.pos)
      expect(nb.vel).toEqual(rb.vel)
      expect(nb.theta).toBe(rb.theta)
    }
  })
})
