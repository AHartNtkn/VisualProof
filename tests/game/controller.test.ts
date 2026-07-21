import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import type { GameCatalog } from '../../src/game/catalog'
import {
  createInitialGameState,
  type GameControllerState,
} from '../../src/game/controller-state'
import { reduceGame } from '../../src/game/controller'
import { applyGameAction, currentDiagram, startPuzzle } from '../../src/game/session'
import { singleStepAction, type ProofAction } from '../../src/kernel/proof/action'
import type { ProofStep } from '../../src/kernel/proof/step'
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

const fresh = (reducedMotion = false): GameControllerState =>
  createInitialGameState(catalog, { reducedMotion })

const transition = (
  state: GameControllerState,
  action: Parameters<typeof reduceGame>[2],
  authority: GameCatalog = catalog,
) => reduceGame(authority, state, action)

const select = (state: GameControllerState, puzzle: typeof FIRST | typeof SECOND) =>
  transition(state, { kind: 'selectPuzzle', puzzle }).state

const gesture = (step: ProofStep): ProofAction => singleStepAction(step.rule, step)
const compound = (label: string, steps: readonly ProofStep[]): ProofAction => ({
  label,
  steps,
  placements: [],
})

const applyWitness = (
  state: GameControllerState,
  puzzle: typeof FIRST | typeof SECOND,
  index: number,
) => transition(state, {
  kind: 'applyProofAction',
  action: gesture(controllerPuzzle(puzzle).witness[index]!),
}).state

describe('authoritative game controller', () => {
  it('starts in the archive with caller-owned reduced motion and first-launch defaults', () => {
    const state = fresh(true)

    expect(state.mode).toBe('archive')
    expect(state.activePuzzle).toBeNull()
    expect(state.completedArtifacts.size).toBe(0)
    expect(state.firstAttempts.size).toBe(0)
    expect(state.replays.size).toBe(0)
    expect(state.guidance).toBeNull()
    expect(state.deliveredGuidance).toEqual([])
    expect(state.selectedCulture).toBe(FIRST_CULTURE)
    expect([...state.scrollByCulture]).toEqual([
      [FIRST_CULTURE, 0],
      [SECOND_CULTURE, 0],
    ])
    expect(state.settings).toEqual({
      reducedMotion: true,
      fullscreen: true,
      textSize: 'medium',
    })
  })

  it('moves through archive, puzzle, completion, and back to archive', () => {
    let state = select(fresh(), FIRST)
    expect(state.mode).toBe('puzzle')
    expect(state.activePuzzle).toBe(FIRST)

    state = applyWitness(state, FIRST, 0)
    state = applyWitness(state, FIRST, 1)
    state = applyWitness(state, FIRST, 2)
    expect(state.mode).toBe('completion')
    expect(state.activePuzzle).toBe(FIRST)
    expect(state.completionReceipt).toEqual({ puzzle: FIRST, moves: 3, replay: false })

    state = transition(state, { kind: 'levelSelection' }).state
    expect(state.mode).toBe('archive')
    expect(state.activePuzzle).toBeNull()
    expect(state.completionReceipt).toBeNull()
  })

  it('commits a prepared batch as one controller action while counting every ordinary proof move', () => {
    const witness = controllerPuzzle(FIRST).witness
    const state = transition(select(fresh(), FIRST), {
      kind: 'applyProofAction',
      action: compound('complete puzzle', witness),
    }).state

    expect(state.mode).toBe('completion')
    expect(state.completionReceipt).toEqual({ puzzle: FIRST, moves: 1, replay: false })
    expect(state.completedArtifacts.has(FIRST)).toBe(true)
    expect(state.completedArtifacts.get(FIRST)?.actions).toEqual([
      compound('complete puzzle', witness),
    ])
  })

  it('applies Escape precedence for editor, pause settings, pause, and no transient while guidance remains passive', () => {
    let state = select(fresh(), FIRST)
    const guidance = state.guidance

    state = transition(state, { kind: 'openEditor' }).state
    expect(state.transient?.kind).toBe('editor')
    expect(state.guidance).toBe(guidance)
    state = transition(state, { kind: 'escape' }).state
    expect(state.transient).toBeNull()

    state = transition(state, { kind: 'escape' }).state
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'menu' })
    state = transition(state, { kind: 'openPauseSettings' }).state
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'settings' })
    state = transition(state, { kind: 'escape' }).state
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'menu' })
    state = transition(state, { kind: 'escape' }).state
    expect(state.transient).toBeNull()
    expect(state.guidance).toBe(guidance)
  })

  it('keeps passive guidance outside mutually exclusive input-owning transients', () => {
    let state = select(fresh(), FIRST)
    const guidance = state.guidance
    state = transition(state, { kind: 'openEditor' }).state
    expect(state.transient).toEqual({ kind: 'editor' })
    expect(state.guidance).toBe(guidance)
    state = transition(state, { kind: 'openPause' }).state
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'menu' })
    expect(state.guidance).toBe(guidance)
  })

  it('supports pause resume, settings, level selection, and typed exit request without restart', () => {
    let state = select(fresh(), FIRST)
    state = transition(state, { kind: 'openPause' }).state
    state = transition(state, { kind: 'resume' }).state
    expect(state.transient).toBeNull()

    state = transition(state, { kind: 'openPause' }).state
    state = transition(state, { kind: 'openPauseSettings' }).state
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'settings' })
    const exit = transition(state, { kind: 'exitGame' })
    expect(exit.state).toBe(state)
    expect(exit.effects).toEqual([{ kind: 'saveBeforeExitAndExitRequested' }])

    state = transition(state, { kind: 'levelSelection' }).state
    expect(state.mode).toBe('archive')
    expect(state.activePuzzle).toBeNull()
  })

  it('refuses proof and timeline input atomically while pause owns input', () => {
    let state = select(fresh(), FIRST)
    state = transition(state, { kind: 'openPause' }).state
    const timeline = state.firstAttempts.get(FIRST)?.timeline

    expect(() => transition(state, {
      kind: 'applyProofAction', action: gesture(controllerPuzzle(FIRST).witness[0]!),
    })).toThrow(/pause.*owns input/)
    expect(() => transition(state, { kind: 'moveTimeline', cursor: 0 }))
      .toThrow(/pause.*owns input/)
    expect(state.firstAttempts.get(FIRST)?.timeline).toBe(timeline)
    expect(state.transient).toEqual({ kind: 'pause', presentation: 'menu' })
  })

  it('keeps first attempts for different puzzles independent and resumes each exact session', () => {
    let state = select(fresh(), FIRST)
    state = applyWitness(state, FIRST, 0)
    const firstSession = state.firstAttempts.get(FIRST)!
    state = transition(state, { kind: 'levelSelection' }).state

    state = select(state, SECOND)
    state = applyWitness(state, SECOND, 0)
    const secondSession = state.firstAttempts.get(SECOND)!
    state = transition(state, { kind: 'levelSelection' }).state
    state = select(state, FIRST)

    expect(state.firstAttempts.size).toBe(2)
    expect(state.firstAttempts.get(FIRST)).toEqual(firstSession)
    expect(state.firstAttempts.get(SECOND)).toEqual(secondSession)
    expect(state.activePuzzle).toBe(FIRST)
  })

  it('keeps completed replay attempts independent and clears only the replay that completes', () => {
    let state = fresh()
    for (const puzzle of [FIRST, SECOND] as const) {
      state = select(state, puzzle)
      state = applyWitness(state, puzzle, 0)
      state = applyWitness(state, puzzle, 1)
      state = applyWitness(state, puzzle, 2)
      state = transition(state, { kind: 'levelSelection' }).state
    }
    state = select(state, FIRST)
    state = applyWitness(state, FIRST, 0)
    state = transition(state, { kind: 'levelSelection' }).state
    state = select(state, SECOND)
    state = applyWitness(state, SECOND, 0)
    state = transition(state, { kind: 'levelSelection' }).state

    state = select(state, FIRST)
    state = applyWitness(state, FIRST, 1)
    state = applyWitness(state, FIRST, 2)

    expect(state.mode).toBe('completion')
    expect(state.completionReceipt).toEqual({ puzzle: FIRST, moves: 3, replay: true })
    expect(state.replays.has(FIRST)).toBe(false)
    expect(state.replays.get(SECOND)?.timeline.cursor).toBe(1)
    expect([...state.completedArtifacts.keys()]).toEqual([FIRST, SECOND])
  })

  it('retains future on rewind, branches only the active puzzle, and uses cursor zero as restart', () => {
    let state = select(fresh(), FIRST)
    state = applyWitness(state, FIRST, 0)
    state = applyWitness(state, FIRST, 1)
    state = transition(state, { kind: 'levelSelection' }).state
    state = select(state, SECOND)
    state = applyWitness(state, SECOND, 0)
    state = applyWitness(state, SECOND, 1)
    state = transition(state, { kind: 'moveTimeline', cursor: 0 }).state

    expect(state.firstAttempts.get(SECOND)?.timeline.cursor).toBe(0)
    expect(state.firstAttempts.get(SECOND)?.timeline.states).toHaveLength(3)
    expect(state.firstAttempts.get(SECOND)?.timeline.actions).toHaveLength(2)
    const untouchedFirst = state.firstAttempts.get(FIRST)
    state = transition(state, {
      kind: 'applyProofAction',
      action: gesture(controllerPuzzle(SECOND).witness[2]!),
    }).state

    expect(state.firstAttempts.get(SECOND)?.timeline.cursor).toBe(1)
    expect(state.firstAttempts.get(SECOND)?.timeline.states).toHaveLength(2)
    expect(state.firstAttempts.get(SECOND)?.timeline.actions).toHaveLength(1)
    expect(state.firstAttempts.get(FIRST)).toBe(untouchedFirst)
  })

  it('branches after rewind with a non-completing batch and preserves one-operation timeline traversal', () => {
    const witness = controllerPuzzle(FIRST).witness
    let state = select(fresh(), FIRST)
    state = applyWitness(state, FIRST, 0)
    state = applyWitness(state, FIRST, 1)
    const future = state.firstAttempts.get(FIRST)!.timeline
    expect(future).toMatchObject({ cursor: 2 })
    expect(future.states).toHaveLength(3)

    state = transition(state, { kind: 'moveTimeline', cursor: 0 }).state
    state = transition(state, {
      kind: 'applyProofAction',
      action: compound('two proof operations', [witness[0]!, witness[1]!]),
    }).state
    const branched = state.firstAttempts.get(FIRST)!.timeline
    expect(state.mode).toBe('puzzle')
    expect(branched.cursor).toBe(1)
    expect(branched.actions).toEqual([
      compound('two proof operations', [witness[0]!, witness[1]!]),
    ])
    expect(branched.states).toHaveLength(2)
    expect(branched.states[1]).not.toBe(branched.states[0])
    state = transition(state, { kind: 'moveTimeline', cursor: 1 }).state
    expect(state.firstAttempts.get(FIRST)!.timeline.cursor).toBe(1)
    expect(currentDiagram(state.firstAttempts.get(FIRST)!)).toBe(branched.states[1])
    state = transition(state, { kind: 'moveTimeline', cursor: 0 }).state
    expect(currentDiagram(state.firstAttempts.get(FIRST)!)).toBe(branched.states[0])
    state = transition(state, { kind: 'moveTimeline', cursor: 1 }).state
    expect(currentDiagram(state.firstAttempts.get(FIRST)!)).toBe(branched.states[1])
  })

  it('refuses locked selection atomically with a domain effect', () => {
    const source = controllerSource()
    const lockedCatalog = buildTestCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => puzzle.id === SECOND
        ? { ...puzzle, prerequisites: [FIRST] }
        : puzzle),
    })
    const before = createInitialGameState(lockedCatalog, { reducedMotion: false })
    const result = reduceGame(lockedCatalog, before, { kind: 'selectPuzzle', puzzle: SECOND })

    expect(result.state).toBe(before)
    expect(result.effects).toEqual([{
      kind: 'selectionRefused', puzzle: SECOND, reason: 'locked',
    }])
  })

  it('completes first attempts and replays atomically with exact retained-path move counts', () => {
    let first = select(fresh(), FIRST)
    first = applyWitness(first, FIRST, 0)
    first = applyWitness(first, FIRST, 1)
    first = transition(first, { kind: 'openEditor' }).state
    const completed = applyWitness(first, FIRST, 2)

    expect([...completed.completedArtifacts.keys()]).toEqual([FIRST])
    expect(completed.firstAttempts.has(FIRST)).toBe(false)
    expect(completed.mode).toBe('completion')
    expect(completed.transient).toBeNull()
    expect(completed.guidance).toBeNull()
    expect(completed.completionReceipt).toEqual({ puzzle: FIRST, moves: 3, replay: false })

    let replay = transition(completed, { kind: 'levelSelection' }).state
    replay = select(replay, FIRST)
    replay = applyWitness(replay, FIRST, 0)
    replay = applyWitness(replay, FIRST, 1)
    replay = applyWitness(replay, FIRST, 2)
    expect([...replay.completedArtifacts.keys()]).toEqual([FIRST])
    expect(replay.replays.has(FIRST)).toBe(false)
    expect(replay.completionReceipt).toEqual({ puzzle: FIRST, moves: 3, replay: true })
  })

  it('starts a fresh replay after a completed replay was cleared', () => {
    let state = select(fresh(), FIRST)
    for (let index = 0; index < 3; index += 1) state = applyWitness(state, FIRST, index)
    state = transition(state, { kind: 'levelSelection' }).state
    state = select(state, FIRST)
    for (let index = 0; index < 3; index += 1) state = applyWitness(state, FIRST, index)
    state = transition(state, { kind: 'levelSelection' }).state

    expect(state.replays.has(FIRST)).toBe(false)
    state = select(state, FIRST)
    expect(state.replays.get(FIRST)?.timeline.cursor).toBe(0)
    expect(state.replays.get(FIRST)?.timeline.states).toHaveLength(1)
  })

  it('delivers and pages opening guidance without changing the puzzle timeline', () => {
    let state = select(fresh(), FIRST)
    const timeline = state.firstAttempts.get(FIRST)?.timeline

    expect(state.guidance).toMatchObject({
      identity: { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
      page: 0,
    })
    expect(state.deliveredGuidance).toEqual([{
      puzzle: FIRST,
      intervention: SHARED_TEACHER_ID,
    }])
    state = transition(state, { kind: 'advanceGuidancePage' }).state
    expect(state.guidance?.page).toBe(1)
    expect(state.firstAttempts.get(FIRST)?.timeline).toBe(timeline)

    const atLastPage = transition(state, { kind: 'advanceGuidancePage' }).state
    expect(atLastPage).toBe(state)

    state = applyWitness(state, FIRST, 0)
    expect(state.guidance).toBeNull()
  })

  it('delivers the same local intervention id independently for each puzzle', () => {
    let state = select(fresh(), FIRST)
    const firstIntervention = catalog.guidance(FIRST).interventions[0]!
    const secondIntervention = catalog.guidance(SECOND).interventions[0]!
    expect(firstIntervention.id).toBe(SHARED_TEACHER_ID)
    expect(secondIntervention.id).toBe(SHARED_TEACHER_ID)

    state = transition(state, { kind: 'levelSelection' }).state
    state = select(state, SECOND)

    expect(state.guidance).toMatchObject({
      identity: { puzzle: SECOND, intervention: SHARED_TEACHER_ID },
    })
    expect(state.deliveredGuidance).toEqual([
      { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
      { puzzle: SECOND, intervention: SHARED_TEACHER_ID },
    ])
  })

  it('replaces opening guidance at an exact recognized state and clears it on rewind', () => {
    const source = controllerSource()
    const second = source.puzzles.find((puzzle) => puzzle.id === SECOND)!
    const firstStep = second.witness[0]!
    const reached = applyGameAction(
      startPuzzle({ id: second.id, diagram: second.goal.diagram }),
      gesture(firstStep),
      { context: buildTestCatalog(source).context },
    )
    const authority = buildTestCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => puzzle.id !== SECOND ? puzzle : {
        ...puzzle,
        teacher: [...puzzle.teacher, {
          id: 'recognized-route',
          trigger: {
            kind: 'recognizedUnwinnable' as const,
            state: { diagram: currentDiagram(reached.session), boundary: puzzle.goal.boundary },
            demonstration: [firstStep],
          },
          pages: ['Draw the timeline back before this route.'],
          repeat: 'repeatable' as const,
          recovery: 'timeline' as const,
        }],
      }),
    })
    let state = reduceGame(
      authority,
      createInitialGameState(authority, { reducedMotion: false }),
      { kind: 'selectPuzzle', puzzle: SECOND },
    ).state

    state = reduceGame(authority, state, {
      kind: 'applyProofAction', action: gesture(firstStep),
    }).state
    expect(state.guidance).toMatchObject({
      identity: { puzzle: SECOND, intervention: 'recognized-route' },
      page: 0,
    })
    state = reduceGame(authority, state, { kind: 'moveTimeline', cursor: 0 }).state
    expect(state.guidance).toBeNull()
  })

  it('does not change controller state when a proof move is invalid', () => {
    const state = select(fresh(), FIRST)
    expect(() => transition(state, {
      kind: 'applyProofAction',
      action: gesture({ rule: 'doubleCutElim', region: 'forged-region' }),
    })).toThrow()
    expect(state.firstAttempts.get(FIRST)?.timeline).toMatchObject({ cursor: 0, actions: [] })
    expect(state.guidance?.page).toBe(0)
  })

  it('persists culture scroll independently and emits fullscreen platform intent', () => {
    let state = fresh()
    state = transition(state, { kind: 'setCultureScroll', culture: FIRST_CULTURE, scroll: 17.25 }).state
    state = transition(state, { kind: 'selectCulture', culture: SECOND_CULTURE }).state
    state = transition(state, { kind: 'setCultureScroll', culture: SECOND_CULTURE, scroll: 91 }).state
    state = transition(state, { kind: 'setReducedMotion', value: true }).state
    state = transition(state, { kind: 'setTextSize', value: 'large' }).state
    const fullscreen = transition(state, { kind: 'setFullscreen', value: false })

    expect(fullscreen.state.selectedCulture).toBe(SECOND_CULTURE)
    expect(fullscreen.state.scrollByCulture.get(FIRST_CULTURE)).toBe(17.25)
    expect(fullscreen.state.scrollByCulture.get(SECOND_CULTURE)).toBe(91)
    expect(fullscreen.state.settings).toEqual({
      reducedMotion: true, fullscreen: false, textSize: 'large',
    })
    expect(fullscreen.effects).toEqual([{ kind: 'fullscreenRequested', fullscreen: false }])
  })

  it('contains no platform/view authority and exposes no restart or reset command', () => {
    const source = [
      'src/game/controller-state.ts',
      'src/game/controller.ts',
      'src/game/save.ts',
    ].map((path) => readFileSync(path, 'utf8')).join('\n')

    for (const forbidden of ['electron', 'localStorage', "from '../app", "from '../view", 'document.', 'window.']) {
      expect(source).not.toContain(forbidden)
    }
    expect(source).not.toMatch(/kind:\s*['"](?:restart|reset)/i)
    expect(source).not.toMatch(/\b(?:restart|reset)(?:Puzzle|Game|Timeline)\b/)
  })
})
