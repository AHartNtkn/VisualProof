import type { GameCatalog } from '../catalog'
import type { PuzzleId } from '../types'

export const EMPTY_ARCHIVE_SUBSTRATE_SEED = 'cursebreaker:archive:empty'

export type SubstratePresentation = {
  readonly positionX: number
  readonly positionY: number
  readonly rotationDegrees: number
  readonly hueDegrees: number
  readonly saturation: number
  readonly brightness: number
  readonly scale: number
}

const hash = (seed: string, salt: number): number => {
  let value = (0x811c9dc5 ^ salt) >>> 0
  for (let index = 0; index < seed.length; index += 1) {
    value ^= seed.charCodeAt(index)
    value = Math.imul(value, 0x01000193) >>> 0
  }
  value ^= value >>> 16
  value = Math.imul(value, 0x7feb352d) >>> 0
  value ^= value >>> 15
  return value >>> 0
}

const channel = (seed: string, salt: number): number => hash(seed, salt) / 0xffffffff
const range = (seed: string, salt: number, minimum: number, maximum: number): number =>
  minimum + channel(seed, salt) * (maximum - minimum)
const rounded = (value: number): number => Math.round(value * 10_000) / 10_000

export const puzzleSubstrateSeed = (catalog: GameCatalog, puzzle: PuzzleId): string =>
  `cursebreaker:puzzle:${puzzle}:${catalog.puzzleFingerprint(puzzle)}`

export function substratePresentation(seed: string): SubstratePresentation {
  return {
    positionX: rounded(range(seed, 1, 43, 57)),
    positionY: rounded(range(seed, 2, 43, 57)),
    rotationDegrees: rounded(range(seed, 3, -0.9, 0.9)),
    hueDegrees: rounded(range(seed, 4, -5, 5)),
    saturation: rounded(range(seed, 5, 0.94, 1.06)),
    brightness: rounded(range(seed, 6, 0.96, 1.035)),
    scale: rounded(range(seed, 7, 1.06, 1.14)),
  }
}
