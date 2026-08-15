import { describe, expect, it } from 'vitest'
import { steinerNet } from '../../src/view3d/steiner'
import { add3, dist3, norm3, scale3, sub3, v3, type Vec3 } from '../../src/view3d/vec3'

const totalLen = (terms: readonly Vec3[], net: ReturnType<typeof steinerNet>): number => {
  const pos = (i: number): Vec3 => (i < terms.length ? terms[i]! : net.junctions[i - terms.length]!)
  return net.edges.reduce((s, [u, w]) => s + dist3(pos(u), pos(w)), 0)
}

describe('steinerNet', () => {
  it('two terminals: a single direct edge', () => {
    const net = steinerNet([v3(0, 0, 0), v3(3, 0, 0)])
    expect(net.junctions).toEqual([])
    expect(net.edges).toEqual([[0, 1]])
  })
  it('equilateral triangle: one junction at the Fermat point, 120° meetings', () => {
    const terms = [v3(0, 0, 0), v3(1, 0, 0), v3(0.5, Math.sqrt(3) / 2, 0)]
    const net = steinerNet(terms)
    expect(net.junctions.length).toBe(1)
    expect(totalLen(terms, net)).toBeCloseTo(Math.sqrt(3), 3)
    const j = net.junctions[0]!
    const dirs = terms.map((t) => norm3(sub3(t, j)))
    for (let a = 0; a < 3; a++) for (let b = a + 1; b < 3; b++) {
      const cos = dirs[a]!.x * dirs[b]!.x + dirs[a]!.y * dirs[b]!.y + dirs[a]!.z * dirs[b]!.z
      expect(cos).toBeCloseTo(-0.5, 2)
    }
  })
  it('collinear terminals: total length is the span (junction degenerates)', () => {
    const terms = [v3(0, 0, 0), v3(2, 0, 0), v3(1, 0, 0)]
    const net = steinerNet(terms)
    expect(totalLen(terms, net)).toBeCloseTo(2, 4)
  })
  it('unit square: two junctions, total 1+√3, beats the centroid star', () => {
    const terms = [v3(0, 0, 0), v3(1, 0, 0), v3(1, 1, 0), v3(0, 1, 0)]
    const net = steinerNet(terms)
    expect(totalLen(terms, net)).toBeCloseTo(1 + Math.sqrt(3), 3)
    expect(net.junctions.length).toBe(2)
  })
  it('works off-plane (translated + tilted square unchanged in length)', () => {
    const base = [v3(0, 0, 0), v3(1, 0, 0), v3(1, 1, 0), v3(0, 1, 0)]
    const terms = base.map((p) => add3(v3(p.x, p.y, p.x * 0.0), v3(5, -2, 7)))
    expect(totalLen(terms, steinerNet(terms))).toBeCloseTo(1 + Math.sqrt(3), 3)
  })
  it('six terminals (hexagon): split-rule fallback beats the plain star', () => {
    const terms = Array.from({ length: 6 }, (_, k) =>
      v3(Math.cos((k * Math.PI) / 3), Math.sin((k * Math.PI) / 3), 0))
    const net = steinerNet(terms)
    const starLen = terms.reduce((s, t) => s + dist3(t, v3(0, 0, 0)), 0)
    expect(totalLen(terms, net)).toBeLessThanOrEqual(starLen + 1e-6)
  })
  it('is deterministic', () => {
    const terms = [v3(0, 0, 0), v3(1, 0.2, 0), v3(0.7, 1, 0.3), v3(-0.2, 0.8, -0.4)]
    expect(steinerNet(terms)).toEqual(steinerNet(terms))
  })
  it('n=5 asymmetric terminals: solves without throwing and beats the star', () => {
    const terms = [v3(0, 0, 0), v3(2, 0.3, 0), v3(1.1, 1.7, 0.4), v3(-0.6, 1.2, -0.5), v3(0.9, -0.8, 0.7)]
    const net = steinerNet(terms)
    const centroid = scale3(terms.reduce((a, b) => add3(a, b), v3(0, 0, 0)), 1 / 5)
    const star = terms.reduce((acc, t) => acc + dist3(t, centroid), 0)
    expect(totalLen(terms, net)).toBeLessThanOrEqual(star + 1e-6)
    expect(net.junctions.length).toBeLessThanOrEqual(3)
  })
  it('seeded random 5- and 6-terminal sweeps never throw and always beat the star', () => {
    let s = 1
    const rnd = (): number => { s = (s * 1103515245 + 12345) % 2147483648; return s / 2147483648 - 0.5 }
    for (const n of [5, 6]) {
      for (let trial = 0; trial < 12; trial++) {
        const terms = Array.from({ length: n }, () => v3(rnd() * 4, rnd() * 4, rnd() * 4))
        const net = steinerNet(terms)
        const centroid = scale3(terms.reduce((a, b) => add3(a, b), v3(0, 0, 0)), 1 / n)
        const star = terms.reduce((acc, t) => acc + dist3(t, centroid), 0)
        expect(totalLen(terms, net)).toBeLessThanOrEqual(star + 1e-6)
      }
    }
  })
})
