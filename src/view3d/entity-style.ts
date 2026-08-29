import type { WireId } from '../kernel/diagram/diagram'
import type { Entity } from './scene'

export type EntityPalette = {
  readonly line: string
  readonly lineAlt: string
  readonly baseWire: string
}

export function entityColor(
  entity: Entity,
  hues: ReadonlyMap<WireId, string>,
  palette: EntityPalette,
): string {
  if (entity.kind === 'strand') return hues.get(entity.wire) ?? palette.baseWire
  if (entity.kind === 'ring' && entity.headWire !== null) {
    return hues.get(entity.headWire) ?? palette.baseWire
  }
  if (entity.kind === 'pip' && entity.ownerWire !== null) {
    return hues.get(entity.ownerWire) ?? palette.baseWire
  }
  if (entity.kind === 'branch' && entity.polarity === 1) return palette.lineAlt
  return palette.line
}
