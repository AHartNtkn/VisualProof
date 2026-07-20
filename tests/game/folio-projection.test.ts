import { describe, expect, it } from 'vitest'
import { diagramToJson } from '../../src/kernel/diagram/json'
import { createInitialGameState } from '../../src/game/controller-state'
import { projectFolio } from '../../src/game/interface/folio-projection'
import { cultureId, puzzleId } from '../../src/game/types'
import { buildTestCatalog, minimalPuzzle, minimalSource, type TestCatalogSource } from './catalog-fixture'

const FIELD = cultureId('field-culture')
const VAULT = cultureId('vault-culture')

function largeSource(): TestCatalogSource {
  const base = minimalSource()
  const fieldPuzzles = Array.from({ length: 18 }, (_, index) => minimalPuzzle({
    id: puzzleId(`field-record-${index}`),
    culture: FIELD,
    name: { professional: `Field record ${index}` },
    prerequisites: index === 0 ? [] : [puzzleId(`field-record-${index - 1}`)],
  }))
  const vaultPuzzles = Array.from({ length: 18 }, (_, index) => minimalPuzzle({
    id: puzzleId(`vault-record-${index}`),
    culture: VAULT,
    name: { professional: `Vault record ${index}` },
    prerequisites: index === 0 ? [] : [puzzleId(`vault-record-${index - 1}`)],
  }))
  return {
    ...base,
    cultures: [
      {
        ...base.cultures[0]!, id: FIELD, name: 'Field culture', gateway: fieldPuzzles.at(-1)!.id,
      },
      {
        ...base.cultures[0]!, id: VAULT, name: 'Vault culture', relativeAge: 1,
        unlocksAfter: [fieldPuzzles.at(-1)!.id], gateway: vaultPuzzles.at(-1)!.id,
      },
    ],
    puzzles: [...fieldPuzzles, ...vaultPuzzles],
  }
}

describe('production excavation folio projection', () => {
  it('keeps dozens of cultures and records in catalog order with real progress statuses', () => {
    const catalog = buildTestCatalog(largeSource())
    const initial = createInitialGameState(catalog, { reducedMotion: false })
    const completed = new Set(catalog.puzzleIds.slice(0, 6))
    const state = {
      ...initial,
      completed,
      scrollByCulture: new Map([
        [FIELD, 312],
        [VAULT, 47],
      ]),
    }

    const archive = projectFolio(catalog, state, 'archive')
    expect(archive.cultures.map(({ id }) => id)).toEqual([FIELD, VAULT])
    expect(archive.cultures[0]!.records.map(({ id }) => id)).toEqual(
      catalog.puzzleIds.slice(0, 18),
    )
    expect(archive.cultures[0]!.records.map(({ levelNumber }) => levelNumber)).toEqual(
      Array.from({ length: 18 }, (_, index) => index + 1),
    )
    expect(archive.cultures[1]!.records.map(({ levelNumber }) => levelNumber)).toEqual(
      Array.from({ length: 18 }, (_, index) => index + 1),
    )
    const first = catalog.puzzleIds[0]!
    const fingerprint = catalog.puzzleFingerprint(first)
    expect(archive.cultures[0]!.records[0]!.preview).toEqual({
      key: `cursebreaker-thumbnail:dark-slate-v1:${fingerprint}:640x400`,
      fingerprint,
      diagram: diagramToJson(catalog.puzzle(first).diagram),
      width: 640,
      height: 400,
    })
    expect(archive.cultures[0]!.records.map(({ status }) => status)).toEqual([
      ...Array.from({ length: 6 }, () => 'completed'),
      'unlocked',
      ...Array.from({ length: 11 }, () => 'locked'),
    ])
    expect(archive.cultures[0]!.records.map(({ affordance }) => affordance)).toEqual([
      ...Array.from({ length: 7 }, () => 'select'),
      ...Array.from({ length: 11 }, () => 'resist'),
    ])
    expect(archive.cultures[1]!.unlocked).toBe(false)
    expect(archive.cultures[0]!.records.some(({ restrictedPacket }) => restrictedPacket))
      .toBe(false)
    expect(archive.cultures[1]!.records.filter(({ restrictedPacket }) => restrictedPacket))
      .toEqual([expect.objectContaining({
        id: catalog.culture(catalog.cultureIds[1]!).gateway,
        status: 'locked',
      })])
    expect(archive.selectedCulture).toBe(FIELD)
    expect(archive.selectedScroll).toBe(312)
  })

  it('keeps restricted packet identity stable across its locked-to-unlocked transition', () => {
    const catalog = buildTestCatalog(largeSource())
    const initial = createInitialGameState(catalog, { reducedMotion: false })
    const packet = catalog.culture(catalog.cultureIds[1]!).gateway
    const sealed = projectFolio(catalog, initial, 'archive').cultures[1]!.records
      .find(({ restrictedPacket }) => restrictedPacket)
    const released = projectFolio(catalog, {
      ...initial,
      completed: new Set(catalog.puzzleIds),
    }, 'archive').cultures[1]!.records.find(({ restrictedPacket }) => restrictedPacket)

    expect(sealed).toMatchObject({ id: packet, restrictedPacket: true, status: 'locked' })
    expect(released).toMatchObject({ id: packet, restrictedPacket: true, status: 'completed' })
    expect(released?.levelNumber).toBe(sealed?.levelNumber)
    expect(released?.preview).toEqual(sealed?.preview)
  })

  it('allows theorem dragging only from completed records while a puzzle is active', () => {
    const catalog = buildTestCatalog(largeSource())
    const initial = createInitialGameState(catalog, { reducedMotion: false })
    const completed = new Set(catalog.puzzleIds.slice(0, 3))
    const projection = projectFolio(catalog, { ...initial, completed }, 'puzzle')

    expect(projection.cultures[0]!.records.slice(0, 5).map(({ affordance }) => affordance))
      .toEqual(['drag-theorem', 'drag-theorem', 'drag-theorem', 'inert', 'inert'])
    expect(projection.cultures[1]!.records.every(({ affordance }) => affordance === 'inert'))
      .toBe(true)
  })

  it('preserves catalog order and progress while making completion records inert', () => {
    const catalog = buildTestCatalog(largeSource())
    const initial = createInitialGameState(catalog, { reducedMotion: false })
    const completed = new Set(catalog.puzzleIds.slice(0, 6))
    const projection = projectFolio(catalog, { ...initial, completed }, 'completion')

    expect(projection.mode).toBe('completion')
    expect(projection.cultures[0]!.records.map(({ id }) => id)).toEqual(
      catalog.puzzleIds.slice(0, 18),
    )
    expect(projection.cultures[0]!.records.slice(0, 7).map(({ status }) => status)).toEqual([
      ...Array.from({ length: 6 }, () => 'completed'),
      'unlocked',
    ])
    expect(projection.cultures.flatMap(({ records }) => records)
      .every(({ affordance }) => affordance === 'inert')).toBe(true)
  })
})
