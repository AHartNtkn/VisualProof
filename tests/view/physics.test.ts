import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { initialState, step, settle, settled, DEFAULT_PARAMS } from '../../src/view/physics'
import { buildScene } from '../../src/view/scene'
import { length, sub } from '../../src/view/vec'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

function host() {
  const h = new DiagramBuilder()
  const a = h.termNode(h.root, p('y'))
  const b = h.termNode(h.root, p('\\x. x'))
  h.wire(h.root, [
    { node: a, port: { kind: 'freeVar', name: 'y' } },
    { node: b, port: { kind: 'output' } },
  ])
  const cut1 = h.cut(h.root)
  const c = h.termNode(cut1, p('\\x. x'))
  const cut2 = h.cut(h.root)
  const e = h.termNode(cut2, p('\\x. \\y. x'))
  void c
  void e
  return h.build()
}

describe('physics', () => {
  it('seeds deterministically: every node gets a distinct position', () => {
    const d = host()
    const s1 = initialState(d)
    const s2 = initialState(d)
    expect([...s1.positions.entries()]).toEqual([...s2.positions.entries()])
    const seen = new Set([...s1.positions.values()].map((v) => `${v.x},${v.y}`))
    expect(seen.size).toBe(Object.keys(d.nodes).length)
  })

  it('stepping is deterministic', () => {
    const d = host()
    let a = initialState(d)
    let b = initialState(d)
    for (let i = 0; i < 50; i++) {
      a = step(d, a, DEFAULT_PARAMS)
      b = step(d, b, DEFAULT_PARAMS)
    }
    expect([...a.positions.entries()]).toEqual([...b.positions.entries()])
  })

  it('settles within the tick budget and reports settlement', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    expect(settled(s, DEFAULT_PARAMS)).toBe(true)
  })

  it('after settling, sibling region circles do not overlap', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const scene = buildScene(d, s.positions)
    const cuts = scene.regions.filter((r) => r.kind === 'cut')
    expect(cuts).toHaveLength(2)
    const [r1, r2] = cuts
    expect(length(sub(r1!.center, r2!.center))).toBeGreaterThanOrEqual(r1!.radius + r2!.radius - 1e-6)
  })

  it('after settling, no two nodes coincide', () => {
    const d = host()
    const s = settle(d, initialState(d), DEFAULT_PARAMS, 20000)
    const ps = [...s.positions.values()]
    for (let i = 0; i < ps.length; i++) {
      for (let j = i + 1; j < ps.length; j++) {
        expect(length(sub(ps[i]!, ps[j]!))).toBeGreaterThan(1)
      }
    }
  })

  it('fails loudly when the tick budget is exhausted', () => {
    const d = host()
    expect(() => settle(d, initialState(d), DEFAULT_PARAMS, 1))
      .toThrowError(/did not settle within 1 ticks/)
  })
})
