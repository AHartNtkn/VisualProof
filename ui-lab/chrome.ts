/**
 * Round-6 chrome core: the MODE MACHINE. One canvas hosts both decided
 * vocabularies — the construction composite (EDIT) and the verdict proof
 * moves (PROVE tracks) — gated by the current mode; the spawn cascade rides
 * EDIT's still right-click; F/B start a track from the current sheet
 * (derive-then-declare), E ends it back to EDIT keeping the sheet. Declared
 * theorems persist in ONE context across tracks. Pages own the LAYOUT.
 */
import type { ProofStep, ProofContext } from '../src/kernel/proof/step'
import { installComposite } from './composite'
import { installVerdictMoves, mkRefusalBubble, type MoveSink } from './verdict'
import { mkTrackLab, type TrackLab } from './session5'
import { openSpawnCascade } from './spawn'
import { fregeCtx } from './prove4'
import { promptAt, type BrushHandle, type LabCtx } from './shared'

export type ChromeApp = {
  readonly ctx: ProofContext
  mode(): 'edit' | 'forward' | 'backward'
  track(): TrackLab | null
  startTrack(dir: 'forward' | 'backward'): void
  /** End the track (declared or not) — back to EDIT, keeping the sheet. */
  endTrack(): void
  promptDeclare(): void
  refuse(text: string): void
  onChange(fn: () => void): void
}

export function mkChromeApp(lab: LabCtx): ChromeApp {
  const ctx = fregeCtx()
  let track: TrackLab | null = null
  let trackSink: MoveSink | null = null
  const listeners: (() => void)[] = []
  const changed = () => { for (const fn of listeners) fn() }
  let brushRef: BrushHandle | null = null
  const refuse = mkRefusalBubble(lab, () => brushRef)
  const mode = (): 'edit' | 'forward' | 'backward' => track?.direction() ?? 'edit'

  installComposite(lab, {
    active: () => mode() === 'edit',
    onRightStill: (at) => openSpawnCascade(lab, ctx, { sx: at.sx, sy: at.sy }, at.world),
  })
  const proxySink: MoveSink = {
    ctx,
    apply: (step: ProofStep) => {
      if (trackSink === null) throw new Error('start proving first (F forward, B backward)')
      trackSink.apply(step)
    },
    refuse,
    mode: () => track?.direction() ?? 'forward',
    undo: () => { trackSink?.undo?.() },
  }
  brushRef = installVerdictMoves(lab, proxySink, { active: () => mode() !== 'edit' })

  const app: ChromeApp = {
    ctx,
    mode,
    track: () => track,
    startTrack: (dir) => {
      if (track !== null) throw new Error(`already proving ${track.direction()} — declare or exit (E) first`)
      track = mkTrackLab(lab, ctx)
      track.onChange(changed)
      trackSink = track.sink(refuse)
      track.start(dir)
      changed()
    },
    endTrack: () => {
      track = null
      trackSink = null
      lab.toast('back to construction — the sheet stays as you left it')
      changed()
    },
    promptDeclare: () => {
      if (track === null) { refuse('start proving first (F forward, B backward)'); return }
      promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
        if (name.trim() === '') { refuse('a theorem needs a name'); return false }
        try {
          track!.declare(name.trim())
          lab.toast(`theorem '${name.trim()}' declared — checked by replay, citable from now on`)
          return true
        } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
      })
    },
    refuse,
    onChange: (fn) => listeners.push(fn),
  }
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    const guard = (fn: () => void) => { try { fn() } catch (err) { refuse(err instanceof Error ? err.message : String(err)) } }
    if (e.key === 'f' || e.key === 'F') { if (mode() === 'edit') guard(() => app.startTrack('forward')) }
    else if (e.key === 'b' || e.key === 'B') { if (mode() === 'edit') guard(() => app.startTrack('backward')) }
    else if (e.key === 'd' || e.key === 'D') { if (mode() !== 'edit') app.promptDeclare() }
    else if (e.key === 'e' || e.key === 'E') { if (mode() !== 'edit') app.endTrack() }
  })
  return app
}

