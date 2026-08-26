import { describe, expect, it } from 'vitest'
import {
  atomGeometry,
  identityGeometry,
  refGeometry,
  termGeometry,
  type NodeGeometry,
} from '../../src/view/bend'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkGeomMorph } from '../../src/view/morph'

const finiteGeometry = (geometry: NodeGeometry): boolean =>
  Number.isFinite(geometry.outerRadius)
  && geometry.arcs.every((arc) =>
    [arc.r, arc.a0, arc.a1].every(Number.isFinite))
  && Object.values(geometry.portAnchors).every((anchor) =>
    Number.isFinite(anchor.x) && Number.isFinite(anchor.y))

describe('whole-node geometry morphing', () => {
  it('returns the exact atom/ref/identity endpoint geometries', () => {
    const cases = [
      [atomGeometry(3), atomGeometry(1)],
      [refGeometry(1), refGeometry(4)],
      [identityGeometry(2), identityGeometry(7)],
    ] as const

    for (const [from, to] of cases) {
      const morph = mkGeomMorph(from, to)
      expect(morph(0)).toEqual(from)
      expect(morph(1)).toEqual(to)
    }
  })

  it('keeps surviving exact port anchors continuous and on finite geometry', () => {
    const from = identityGeometry(3)
    const to = identityGeometry(6)
    const morph = mkGeomMorph(from, to)
    let previous = morph(0).portAnchors['i:0']!

    for (let step = 1; step <= 100; step++) {
      const geometry = morph(step / 100)
      const anchor = geometry.portAnchors['i:0']!
      expect(finiteGeometry(geometry)).toBe(true)
      expect(Math.hypot(anchor.x - previous.x, anchor.y - previous.y)).toBeLessThan(0.2)
      previous = anchor
    }
  })

  it('interpolates term radials and exits without exposing ambiguous occurrence targets', () => {
    const from = termGeometry(parseTerm('\\x. x free').term)
    const to = termGeometry(parseTerm('\\x. x').term)
    const geometry = mkGeomMorph(from, to)(0.5)

    expect(geometry.radials.length).toBeGreaterThan(0)
    expect(geometry.exitArc).not.toBeNull()
    expect(geometry.exitLine).not.toBeNull()
    expect(geometry.occurrences).toEqual([])
  })
})
