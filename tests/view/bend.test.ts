import { describe, expect, it } from 'vitest'
import {
  atomGeometry,
  identityGeometry,
  refGeometry,
} from '../../src/view/bend'

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
    expect(geometry.arcs[0]!.a1 - geometry.arcs[0]!.a0).toBeCloseTo(2 * Math.PI, 10)
    expect(geometry.headAnchor).toBeNull()
    expect(Object.keys(geometry.portAnchors)).toEqual(['a:0', 'a:1'])
    expect(geometry.portAnchors['a:0']).toEqual({ x: 0, y: 2 })
  })

  it('collapses every n-ary identity to a centered point with no drawn rail', () => {
    const geometry = identityGeometry(5)

    expect(geometry.arcs).toHaveLength(0)
    expect(geometry.outerRadius).toBe(0)
    expect(geometry.headAnchor).toBeNull()
    expect(Object.keys(geometry.portAnchors)).toEqual([
      'i:0',
      'i:1',
      'i:2',
      'i:3',
      'i:4',
    ])
    for (const anchor of Object.values(geometry.portAnchors)) {
      expect(anchor).toEqual({ x: 0, y: 0 })
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
