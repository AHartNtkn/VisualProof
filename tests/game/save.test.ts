import { describe, expect, it } from 'vitest'
import { actionToJson } from '../../src/kernel/proof/json'
import { singleStepAction } from '../../src/kernel/proof/action'
import type { GameCatalog } from '../../src/game/catalog'
import { createInitialGameState, type GameControllerState } from '../../src/game/controller-state'
import { reduceGame, type GameAction } from '../../src/game/controller'
import { decodeGameSave, encodeGameSave, startGame } from '../../src/game/save'
import {
  controllerCatalog,
  controllerPuzzle,
  controllerSource,
  FIRST,
  FIRST_CULTURE,
  SECOND,
  SECOND_CULTURE,
  SHARED_TEACHER_ID,
} from './controller-fixture'
import { buildTestCatalog } from './catalog-fixture'

const catalog = controllerCatalog()

const fresh = (authority: GameCatalog = catalog): GameControllerState =>
  createInitialGameState(authority, { reducedMotion: false })

const act = (
  state: GameControllerState,
  action: GameAction,
  authority: GameCatalog = catalog,
): GameControllerState => reduceGame(authority, state, action).state

const select = (state: GameControllerState, puzzle: typeof FIRST | typeof SECOND) =>
  act(state, { kind: 'selectPuzzle', puzzle })

const move = (
  state: GameControllerState,
  puzzle: typeof FIRST | typeof SECOND,
  index: number,
) => act(state, {
  kind: 'applyProofAction',
  action: singleStepAction(
    controllerPuzzle(puzzle).witness[index]!.rule,
    controllerPuzzle(puzzle).witness[index]!,
  ),
})

const plain = <T>(value: T): T => JSON.parse(JSON.stringify(value)) as T

function richPuzzleState(): GameControllerState {
  let state = select(fresh(), FIRST)
  state = move(state, FIRST, 0)
  state = move(state, FIRST, 1)
  state = move(state, FIRST, 2)
  state = act(state, { kind: 'levelSelection' })
  state = select(state, FIRST)
  state = move(state, FIRST, 0)
  state = act(state, { kind: 'levelSelection' })
  state = select(state, SECOND)
  state = move(state, SECOND, 0)
  state = move(state, SECOND, 1)
  state = act(state, { kind: 'moveTimeline', cursor: 0 })
  state = act(state, { kind: 'setCultureScroll', culture: FIRST_CULTURE, scroll: 19.5 })
  state = act(state, { kind: 'selectCulture', culture: SECOND_CULTURE })
  state = act(state, { kind: 'setCultureScroll', culture: SECOND_CULTURE, scroll: 83 })
  state = act(state, { kind: 'setReducedMotion', value: true })
  state = act(state, { kind: 'setFullscreen', value: false })
  return act(state, { kind: 'setTextSize', value: 'large' })
}

describe('strict per-puzzle game save', () => {
  it('round-trips every timeline and cursor plus controller mode, culture, scroll, guidance delivery, and settings', () => {
    const state = richPuzzleState()
    const encoded = encodeGameSave(catalog, state)
    const loaded = decodeGameSave(catalog, plain(encoded))

    expect(loaded.mode).toBe('puzzle')
    expect(loaded.activePuzzle).toBe(SECOND)
    expect(loaded.completedArtifacts).toEqual(state.completedArtifacts)
    expect(loaded.firstAttempts).toEqual(state.firstAttempts)
    expect(loaded.firstAttempts.get(SECOND)?.timeline).toMatchObject({
      cursor: 0,
      states: expect.any(Array),
      actions: expect.any(Array),
    })
    expect(loaded.firstAttempts.get(SECOND)?.timeline.states).toHaveLength(3)
    expect(loaded.firstAttempts.get(SECOND)?.timeline.actions).toHaveLength(2)
    expect(loaded.replays).toEqual(state.replays)
    expect(loaded.replays.get(FIRST)?.timeline.cursor).toBe(1)
    expect(loaded.deliveredGuidance).toEqual(state.deliveredGuidance)
    expect(loaded.guidance).toEqual(state.guidance)
    expect(loaded.selectedCulture).toBe(SECOND_CULTURE)
    expect(loaded.scrollByCulture).toEqual(state.scrollByCulture)
    expect(loaded.settings).toEqual(state.settings)
  })

  it('round-trips shared local intervention ids as independent puzzle-qualified deliveries', () => {
    let state = select(fresh(), SECOND)
    state = act(state, { kind: 'levelSelection' })
    state = select(state, FIRST)

    const encoded = encodeGameSave(catalog, state)
    expect(encoded.deliveredGuidance).toEqual([
      { puzzle: SECOND, intervention: SHARED_TEACHER_ID },
      { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
    ])
    const loaded = decodeGameSave(catalog, plain(encoded))
    expect(loaded.deliveredGuidance).toEqual(state.deliveredGuidance)
  })

  it('rejects malformed and duplicate guidance deliveries while dropping stale overlay identities', () => {
    const base: any = plain(encodeGameSave(catalog, fresh()))
    base.deliveredGuidance = [SHARED_TEACHER_ID]
    expect(() => decodeGameSave(catalog, base)).toThrow(/delivered guidance/)

    const duplicate: any = plain(encodeGameSave(catalog, fresh()))
    duplicate.deliveredGuidance = [
      { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
      { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
    ]
    expect(() => decodeGameSave(catalog, duplicate)).toThrow(/duplicate/)

    const crossPuzzle: any = plain(encodeGameSave(catalog, fresh()))
    crossPuzzle.deliveredGuidance = [{ puzzle: FIRST, intervention: 'not-authored-here' }]
    expect(decodeGameSave(catalog, crossPuzzle).deliveredGuidance).toEqual([])
  })

  it('round-trips the exact active guidance page and rejects invalid page ownership', () => {
    let state = select(fresh(), FIRST)
    state = act(state, { kind: 'advanceGuidancePage' })
    const encoded: any = plain(encodeGameSave(catalog, state))
    expect(encoded.version).toBe(6)
    expect(encoded.guidance).toEqual({
      puzzle: FIRST, intervention: SHARED_TEACHER_ID, page: 1,
    })
    expect(decodeGameSave(catalog, encoded).guidance).toEqual(state.guidance)

    encoded.guidance.page = 99
    expect(decodeGameSave(catalog, encoded).guidance).toBeNull()
    encoded.guidance.page = 1
    encoded.guidance.puzzle = SECOND
    expect(() => decodeGameSave(catalog, encoded)).toThrow(/guidance.*active puzzle/)
  })

  it('round-trips a completion receipt with exact move count and replay identity', () => {
    let state = select(fresh(), FIRST)
    state = move(state, FIRST, 0)
    state = move(state, FIRST, 1)
    state = move(state, FIRST, 2)

    const loaded = decodeGameSave(catalog, plain(encodeGameSave(catalog, state)))
    expect(loaded.mode).toBe('completion')
    expect(loaded.activePuzzle).toBe(FIRST)
    expect(loaded.completionReceipt).toEqual({ puzzle: FIRST, moves: 3, replay: false })
    expect(loaded.firstAttempts.has(FIRST)).toBe(false)
  })

  it('uses caller OS preference only for fresh startup and rejects an invalid supplied save', () => {
    expect(startGame(catalog, { save: null, reducedMotion: true }).settings).toMatchObject({
      reducedMotion: true,
      fullscreen: true,
      textSize: 'medium',
    })
    expect(() => startGame(catalog, {
      save: { format: 'cursebreaker-save', version: 4 },
      reducedMotion: false,
    })).toThrow(/unsupported game save format or version/)
  })

  it('keeps the first catalog culture selected and saveable even when its archive is gated', () => {
    const source = controllerSource()
    const gatedFirst = buildTestCatalog({
      ...source,
      cultures: source.cultures.map((culture) => culture.id === FIRST_CULTURE
        ? { ...culture, unlocksAfter: [SECOND] }
        : culture),
    })
    const initial = fresh(gatedFirst)

    expect(initial.selectedCulture).toBe(FIRST_CULTURE)
    expect(decodeGameSave(gatedFirst, encodeGameSave(gatedFirst, initial)).selectedCulture)
      .toBe(FIRST_CULTURE)
  })

  it('refuses a forged locked selection for any non-first culture', () => {
    const source = controllerSource()
    const gatedSecond = buildTestCatalog({
      ...source,
      cultures: source.cultures.map((culture) => culture.id === SECOND_CULTURE
        ? { ...culture, unlocksAfter: [FIRST] }
        : culture),
    })
    const forged: any = plain(encodeGameSave(gatedSecond, fresh(gatedSecond)))
    forged.selectedCulture = SECOND_CULTURE

    expect(() => decodeGameSave(gatedSecond, forged)).toThrow(/selected culture.*locked/)
  })

  it('replays serialized actions and refuses forged constituent steps', () => {
    const encoded: any = plain(encodeGameSave(catalog, richPuzzleState()))
    encoded.attempts[SECOND].actions[0].steps[0] = {
      rule: 'doubleCutElim', region: 'forged-region',
    }

    expect(() => decodeGameSave(catalog, encoded)).toThrow(/invalid saved timeline|unknown region/)
  })

  it('refuses a locked active puzzle', () => {
    const source = controllerSource()
    const locked = buildTestCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => puzzle.id === SECOND
        ? { ...puzzle, prerequisites: [FIRST] }
        : puzzle),
    })
    const encoded: any = plain(encodeGameSave(locked, fresh(locked)))
    encoded.mode = 'puzzle'
    encoded.activePuzzle = SECOND
    encoded.attempts[SECOND] = { actions: [], cursor: 0 }
    encoded.puzzleFingerprints[SECOND] = locked.puzzleFingerprint(SECOND)

    expect(() => decodeGameSave(locked, encoded)).toThrow(/locked/)
  })

  it('refuses a locked inactive first attempt in archive mode', () => {
    const source = controllerSource()
    const locked = buildTestCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => puzzle.id === SECOND
        ? { ...puzzle, prerequisites: [FIRST] }
        : puzzle),
    })
    const encoded: any = plain(encodeGameSave(locked, fresh(locked)))
    encoded.attempts[SECOND] = { actions: [], cursor: 0 }
    encoded.puzzleFingerprints[SECOND] = locked.puzzleFingerprint(SECOND)

    expect(() => decodeGameSave(locked, encoded)).toThrow(/first attempt.*locked/)
  })

  it('refuses first-attempt and replay misclassification', () => {
    let completed = select(fresh(), FIRST)
    for (let index = 0; index < 3; index += 1) completed = move(completed, FIRST, index)
    const completedSave: any = plain(encodeGameSave(catalog, completed))
    completedSave.attempts[FIRST] = { actions: [], cursor: 0 }
    expect(() => decodeGameSave(catalog, completedSave)).toThrow(/first attempt.*completed puzzle/)

    const incompleteSave: any = plain(encodeGameSave(catalog, fresh()))
    incompleteSave.replays[SECOND] = { actions: [], cursor: 0 }
    incompleteSave.puzzleFingerprints[SECOND] = catalog.puzzleFingerprint(SECOND)
    expect(() => decodeGameSave(catalog, incompleteSave)).toThrow(/replay.*incomplete puzzle/)
  })

  it('refuses cursor bounds and unfinished timelines that already reach blank', () => {
    const cursor: any = plain(encodeGameSave(catalog, richPuzzleState()))
    cursor.attempts[SECOND].cursor = 3
    expect(() => decodeGameSave(catalog, cursor)).toThrow(/cursor.*outside/)

    const completedTimeline: any = plain(encodeGameSave(catalog, fresh()))
    completedTimeline.attempts[FIRST] = {
      actions: controllerPuzzle(FIRST).witness.map((step) =>
        actionToJson(singleStepAction(step.rule, step))),
      cursor: 0,
    }
    completedTimeline.puzzleFingerprints[FIRST] = catalog.puzzleFingerprint(FIRST)
    expect(() => decodeGameSave(catalog, completedTimeline)).toThrow(/unfinished timeline.*completion/)
  })

  it('refuses unknown IDs, unknown fields, and missing or extra fingerprints', () => {
    const unknownId: any = plain(encodeGameSave(catalog, fresh()))
    unknownId.completedArtifacts = [{ puzzle: 'unknown-puzzle', actions: [] }]
    unknownId.puzzleFingerprints['unknown-puzzle'] = 'forged'
    expect(() => decodeGameSave(catalog, unknownId)).toThrow(/unknown puzzle/)

    const unknownField: any = plain(encodeGameSave(catalog, fresh()))
    unknownField.extra = true
    expect(() => decodeGameSave(catalog, unknownField)).toThrow(/unknown field 'extra'/)
    const nestedUnknown: any = plain(encodeGameSave(catalog, fresh()))
    nestedUnknown.settings.extra = true
    expect(() => decodeGameSave(catalog, nestedUnknown)).toThrow(/unknown field 'extra'/)

    const referenced = plain(encodeGameSave(catalog, select(fresh(), FIRST))) as any
    delete referenced.puzzleFingerprints[FIRST]
    expect(() => decodeGameSave(catalog, referenced)).toThrow(/missing logical fingerprint/)
    const extra = plain(encodeGameSave(catalog, fresh())) as any
    extra.puzzleFingerprints[FIRST] = catalog.puzzleFingerprint(FIRST)
    expect(() => decodeGameSave(catalog, extra)).toThrow(/unreferenced logical fingerprint/)
  })

  it('refuses logical fingerprint drift while allowing presentation-only catalog changes', () => {
    const state = select(fresh(), FIRST)
    const encoded: any = plain(encodeGameSave(catalog, state))
    encoded.puzzleFingerprints[FIRST] = 'drifted'
    expect(() => decodeGameSave(catalog, encoded)).toThrow(/logical fingerprint does not match/)

    const source = controllerSource()
    const changedPresentation = buildTestCatalog({
      ...source,
      cultures: source.cultures.map((culture) => ({
        ...culture,
        name: `${culture.name} renamed`,
        historicalSummary: `${culture.historicalSummary} Revised presentation.`,
      })),
      puzzles: source.puzzles.map((puzzle) => ({
        ...puzzle,
        name: { ...puzzle.name, professional: `${puzzle.name.professional} renamed` },
        provenance: { ...puzzle.provenance, summary: `${puzzle.provenance.summary} Revised.` },
        teacher: puzzle.teacher.map((teacher) => ({
          ...teacher,
          pages: teacher.pages.map((page) => `${page} Revised.`),
        })),
      })),
    })
    expect(() => decodeGameSave(changedPresentation, encodeGameSave(catalog, state))).not.toThrow()

    const withoutGuidance = buildTestCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => ({ ...puzzle, teacher: [] })),
    })
    const restored = decodeGameSave(withoutGuidance, encodeGameSave(catalog, state))
    expect(restored.activePuzzle).toBe(FIRST)
    expect(restored.firstAttempts.get(FIRST)?.timeline.cursor).toBe(0)
    expect(restored.deliveredGuidance).toEqual([])
    expect(restored.guidance).toBeNull()
  })

  it('refuses invalid scroll, settings, and mode/receipt combinations', () => {
    const negativeScroll: any = plain(encodeGameSave(catalog, fresh()))
    negativeScroll.scrollByCulture[FIRST_CULTURE] = -1
    expect(() => decodeGameSave(catalog, negativeScroll)).toThrow(/scroll.*nonnegative finite/)
    const missingScroll: any = plain(encodeGameSave(catalog, fresh()))
    delete missingScroll.scrollByCulture[SECOND_CULTURE]
    expect(() => decodeGameSave(catalog, missingScroll)).toThrow(/scroll.*every catalog culture/)

    for (const settings of [
      { reducedMotion: 'yes', fullscreen: true, textSize: 'medium' },
      { reducedMotion: false, fullscreen: 1, textSize: 'medium' },
      { reducedMotion: false, fullscreen: true, textSize: 'huge' },
      { reducedMotion: false, fullscreen: true, textSize: ['medium'] },
    ]) {
      const invalid: any = plain(encodeGameSave(catalog, fresh()))
      invalid.settings = settings
      expect(() => decodeGameSave(catalog, invalid)).toThrow(/settings/)
    }

    const archiveWithActive: any = plain(encodeGameSave(catalog, fresh()))
    archiveWithActive.activePuzzle = FIRST
    expect(() => decodeGameSave(catalog, archiveWithActive)).toThrow(/archive mode/)
    const completionWithoutReceipt: any = plain(encodeGameSave(catalog, fresh()))
    completionWithoutReceipt.mode = 'completion'
    completionWithoutReceipt.activePuzzle = FIRST
    expect(() => decodeGameSave(catalog, completionWithoutReceipt)).toThrow(/completion receipt/)

    let completed = select(fresh(), FIRST)
    for (let index = 0; index < 3; index += 1) completed = move(completed, FIRST, index)
    const impossibleReceipt: any = plain(encodeGameSave(catalog, completed))
    impossibleReceipt.completionReceipt.moves = 0
    expect(() => decodeGameSave(catalog, impossibleReceipt)).toThrow(/moves must be a positive integer/)
  })
})
