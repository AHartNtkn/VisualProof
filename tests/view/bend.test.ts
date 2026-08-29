import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import {
  atomGeometry,
  bendGrid,
  GAP_ANGLE,
  identityGeometry,
  refGeometry,
  termGeometry,
} from '../../src/view/bend'
import { trompGrid } from '../../src/view/tromp'
import { length } from '../../src/view/vec'

const p = (source: string) => parseTerm(source).term

describe('bent Tromp geometry', () => {
  it('maps outer binders to larger circular arcs', () => {
    const geometry = bendGrid(trompGrid(p('\\x. \\y. x')))
    const binderArcs = geometry.arcs.filter((arc) => arc.kind === 'lam')
    expect(binderArcs).toHaveLength(2)
    expect(binderArcs.find((arc) => arc.hueRow === 0)!.r)
      .toBeGreaterThan(binderArcs.find((arc) => arc.hueRow === 1)!.r)
  })

  it('pads a one-column lambda bar into a visible circular arc', () => {
    const binder = termGeometry(p('\\x. x')).arcs.find((arc) => arc.kind === 'lam')!

    expect(binder.a1 - binder.a0).toBeCloseTo(Math.PI / 6, 12)
    expect(binder.r * (binder.a1 - binder.a0)).toBeGreaterThan(1)
  })

  it('keeps all internal strokes outside the output gap', () => {
    const geometry = termGeometry(p('\\f. \\x. f (f x)'))
    const low = GAP_ANGLE / 2
    const high = 2 * Math.PI - GAP_ANGLE / 2
    for (const arc of geometry.arcs) {
      expect(arc.a0).toBeGreaterThanOrEqual(low)
      expect(arc.a1).toBeLessThanOrEqual(high)
    }
    for (const radial of geometry.radials) {
      expect(radial.angle).toBeGreaterThanOrEqual(low)
      expect(radial.angle).toBeLessThanOrEqual(high)
    }
  })

  it('uses diagram storage keys for output and numeric free-slot anchors', () => {
    const geometry = termGeometry(p('y (z y)'))
    expect(Object.keys(geometry.portAnchors)).toEqual(['f:0', 'f:1', 'out'])
    const maxArcRadius = Math.max(...geometry.arcs.map((arc) => arc.r))
    expect(length(geometry.portAnchors['f:0']!)).toBeGreaterThan(maxArcRadius)
    expect(length(geometry.portAnchors['f:1']!)).toBeGreaterThan(maxArcRadius)
    expect(geometry.portAnchors.out!.y).toBeCloseTo(0, 10)
    expect(geometry.portAnchors.out!.x).toBeGreaterThan(0)
  })

  it('includes the output arc and straight exit owned by the root occurrence', () => {
    const geometry = termGeometry(p('\\x. x'))
    expect(geometry.exitArc).not.toBeNull()
    expect(geometry.exitLine).not.toBeNull()
    expect(geometry.exitLine).toHaveLength(2)
    expect(geometry.occurrences[0]).toMatchObject({ path: [], includeExit: true, hit: { kind: 'exit' } })
  })

  it('maps every syntax occurrence to painted anatomy primitives and a hit trace', () => {
    const geometry = termGeometry(p('a ((\\x. x) b)'))
    expect(geometry.occurrences.map((occurrence) => occurrence.path)).toEqual([
      [], ['fn'], ['argument'], ['argument', 'fn'], ['argument', 'fn', 'body'], ['argument', 'argument'],
    ])
    for (const occurrence of geometry.occurrences) {
      expect(
        occurrence.arcIndices.length + occurrence.radialIndices.length + Number(occurrence.includeExit),
        `painted carrier for [${occurrence.path.join(',')}]`,
      ).toBeGreaterThan(0)
    }
  })

  it('gives lambda leaf bodies a painted carrier', () => {
    for (const source of ['\\x. a', '\\x. x']) {
      const body = termGeometry(p(source)).occurrences.find((occurrence) => occurrence.path.join('/') === 'body')!
      expect(body.arcIndices.length + body.radialIndices.length).toBeGreaterThan(0)
    }
  })

  it('produces exactly equal circular geometry for alpha-equivalent inputs', () => {
    expect(termGeometry(p('\\x. x free'))).toEqual(termGeometry(p('\\renamed. renamed other')))
  })
})

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

  it('does not fabricate term exits or occurrences', () => {
    for (const geometry of [atomGeometry(2), refGeometry(2), identityGeometry(4)]) {
      expect(geometry.exitArc).toBeNull()
      expect(geometry.exitLine).toBeNull()
      expect(geometry.occurrences).toEqual([])
    }
  })

  it('keeps the canonical body radius independent of identity arity', () => {
    expect(identityGeometry(2).outerRadius).toBe(identityGeometry(9).outerRadius)
  })
})
