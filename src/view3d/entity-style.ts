import type { WireId } from '../kernel/diagram/diagram'
import type { Entity } from './scene'

export type EntityPalette = {
  readonly line: string
  readonly lineAlt: string
  readonly baseWire: string
  readonly hues: ReadonlyMap<WireId, string>
}

export function entityColor(
  entity: Entity,
  palette: EntityPalette,
): string {
  if (entity.kind === 'lambda') return entity.color ?? palette.baseWire
  if (entity.kind === 'strand') return palette.hues.get(entity.wire) ?? palette.baseWire
  if (entity.kind === 'ring' && entity.headWire !== null) {
    return palette.hues.get(entity.headWire) ?? palette.baseWire
  }
  if (entity.kind === 'pip' && entity.ownerWire !== null) {
    return palette.hues.get(entity.ownerWire) ?? palette.baseWire
  }
  if (entity.kind === 'branch' && entity.polarity === 1) return palette.lineAlt
  return palette.line
}
