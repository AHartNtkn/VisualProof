import { describe, expect, it } from 'vitest'
import { entityColor, type EntityPalette } from '../../src/view3d/entity-style'
import type { Entity } from '../../src/view3d/scene'

const palette: EntityPalette = {
  line: '#ffffff',
  lineAlt: '#777777',
  baseWire: '#00ffff',
}

describe('3D entity authored colors', () => {
  it('colors branches by their semantic polarity', () => {
    const even: Extract<Entity, { kind: 'branch' }> = {
      kind: 'branch', key: 'drawing-even', region: 'semantic-even', polarity: 0, pts: [],
    }
    const odd: Extract<Entity, { kind: 'branch' }> = {
      kind: 'branch', key: 'drawing-odd', region: 'semantic-odd', polarity: 1, pts: [],
    }

    expect(entityColor(even, new Map(), palette)).toBe(palette.line)
    expect(entityColor(odd, new Map(), palette)).toBe(palette.lineAlt)
  })

  it('uses authored wire hues for every wire-owned entity', () => {
    const hues = new Map([['wire-a', '#123456']])
    const entities: Entity[] = [
      { kind: 'strand', key: 'strand', wire: 'wire-a', pts: [] },
      { kind: 'ring', key: 'ring', node: 'node', headWire: 'wire-a', pts: [] },
      { kind: 'pip', key: 'pip', node: 'node', ownerWire: 'wire-a', pos: { x: 0, y: 0, z: 0 } },
    ]

    for (const entity of entities) expect(entityColor(entity, hues, palette)).toBe('#123456')
  })

  it('falls back to the palette for missing or absent wire hues', () => {
    const entities: Entity[] = [
      { kind: 'strand', key: 'strand', wire: 'missing', pts: [] },
      { kind: 'ring', key: 'ring', node: 'node', headWire: null, pts: [] },
      { kind: 'pip', key: 'pip', node: 'node', ownerWire: null, pos: { x: 0, y: 0, z: 0 } },
      { kind: 'label', key: 'label', node: 'node', text: 'N', pos: { x: 0, y: 0, z: 0 } },
    ]

    expect(entityColor(entities[0]!, new Map(), palette)).toBe(palette.baseWire)
    for (const entity of entities.slice(1)) expect(entityColor(entity, new Map(), palette)).toBe(palette.line)
  })
})
