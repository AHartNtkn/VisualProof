import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { buildCatalog } from '../../src/game/catalog'
import {
  cultureId,
  puzzleId,
  type GameCatalogSource,
  type PuzzleDefinition,
} from '../../src/game/types'
import { minimalPuzzle, minimalSource } from './catalog-fixture'

export const FIRST = puzzleId('first-artifact')
export const SECOND = puzzleId('second-artifact')
export const FIRST_CULTURE = cultureId('oldest-tradition')
export const SECOND_CULTURE = cultureId('second-tradition')
export const SHARED_TEACHER_ID = 'shared-opening'

function longPuzzle(
  id: typeof FIRST | typeof SECOND,
  culture: typeof FIRST_CULTURE | typeof SECOND_CULTURE,
): PuzzleDefinition {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const second = builder.cut(outer)
  const third = builder.cut(second)
  const fourth = builder.cut(third)
  const fifth = builder.cut(fourth)
  builder.cut(fifth)
  return minimalPuzzle({
    id,
    culture,
    name: { professional: `${id} professional name` },
    goal: mkDiagramWithBoundary(builder.build(), []),
    witness: [
      { rule: 'doubleCutElim', region: fifth },
      { rule: 'doubleCutElim', region: third },
      { rule: 'doubleCutElim', region: outer },
    ],
    teacher: [{
      id: SHARED_TEACHER_ID,
      trigger: { kind: 'opening' },
      pages: [`Opening instruction for ${id}.`, `Second instruction for ${id}.`],
      repeat: 'once',
    }],
  })
}

export function controllerSource(): GameCatalogSource {
  const base = minimalSource()
  const first = longPuzzle(FIRST, FIRST_CULTURE)
  const second = longPuzzle(SECOND, SECOND_CULTURE)
  return {
    ...base,
    cultures: [
      { ...base.cultures[0]!, gateway: FIRST },
      {
        ...base.cultures[0]!,
        id: SECOND_CULTURE,
        name: 'Second tradition',
        relativeAge: 1,
        gateway: SECOND,
      },
    ],
    puzzles: [first, second],
  }
}

export const controllerCatalog = () => buildCatalog(controllerSource())
