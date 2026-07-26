import { describe, expect, it } from 'vitest'
import {
  atomGeometry,
  identityGeometry,
  refGeometry,
} from '../../src/view/bend'

const angle = (point: { readonly x: number; readonly y: number }): number =>
  Math.atan2(point.y, point.x)

const positiveTurn = (from: number, to: number): number => {
  const turn = to - from
  return turn < 0 ? turn + 2 * Math.PI : turn
}

describe('atom/ref/identity geometry', () => {
  it('retains atom head and argument geometry', () => {
    const geometry = atomGeometry(3)

    expect(geometry.arcs).toHaveLength(1)
    expect(geometry.headAnchor).not.toBeNull()
    expect(Object.keys(geometry.portAnchors)).toEqual(['a:0', 'a:1', 'a:2'])
    expect(geometry.portAnchors['a:0']).toEqual({ x: 0, y: 2 })
    expect(geometry.headAnchor).not.toEqual(geometry.portAnchors['a:0'])
  })

  it('retains ref argument geometry without fabricating a head', () => {
    const geometry = refGeometry(2)

    expect(geometry.arcs).toHaveLength(1)
    expect(geometry.headAnchor).toBeNull()
    expect(Object.keys(geometry.portAnchors)).toEqual(['a:0', 'a:1'])
    expect(geometry.portAnchors['a:0']).toEqual({ x: 0, y: 2 })
  })

  it('gives an n-ary identity n evenly spaced rim anchors keyed by storage index', () => {
    const geometry = identityGeometry(5)
    const anchors = Array.from(
      { length: 5 },
      (_, index) => geometry.portAnchors[`i:${index}`],
    )

    expect(Object.keys(geometry.portAnchors)).toEqual([
      'i:0',
      'i:1',
      'i:2',
      'i:3',
      'i:4',
    ])
    expect(anchors.every((anchor) => anchor !== undefined)).toBe(true)
    const radii = anchors.map((anchor) => Math.hypot(anchor!.x, anchor!.y))
    expect(new Set(radii.map((radius) => radius.toFixed(10)))).toHaveProperty('size', 1)
    const angles = anchors.map((anchor) => angle(anchor!))
    for (let index = 0; index < angles.length; index++) {
      const turn = positiveTurn(angles[index]!, angles[(index + 1) % angles.length]!)
      expect(turn).toBeCloseTo(2 * Math.PI / angles.length, 10)
    }
  })

  it('contains no lambda output, body, occurrence, or fission geometry fields', () => {
    for (const geometry of [atomGeometry(2), refGeometry(2), identityGeometry(4)]) {
      expect(geometry).not.toHaveProperty('outputAnchor')
      expect(geometry).not.toHaveProperty('exitArc')
      expect(geometry).not.toHaveProperty('exitLine')
      expect(geometry).not.toHaveProperty('occurrences')
    }
  })

  it('keeps the canonical body radius independent of identity arity', () => {
    expect(identityGeometry(2).outerRadius).toBe(identityGeometry(9).outerRadius)
  })
})
