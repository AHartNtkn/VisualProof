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

/** The round-6 verdict chrome (variant A): the mode pill and the '?' map —
    the only permanent apparatus. History surfaces plug in beside it. */
export function installMinimalChrome(lab: LabCtx, app: ChromeApp): void {
  const pill = document.createElement('div')
  pill.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);top:44px;z-index:7;padding:5px 18px;border-radius:0 0 12px 12px;font:600 13px system-ui;color:#fff'
  document.body.append(pill)
  const MODE = { edit: ['#b45309', 'EDIT — construct freely'], forward: ['#15803d', 'PROVING FORWARD — D declares (origin ⟹ here)'], backward: ['#6d28d9', 'PROVING BACKWARD — D declares (here ⟹ origin)'] } as const
  const sync = () => { pill.style.background = MODE[app.mode()][0]; pill.textContent = MODE[app.mode()][1] }
  app.onChange(sync)
  sync()
  const help = document.createElement('div')
  help.style.cssText = 'position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);z-index:10;display:none;background:#fff;border:1.5px solid #d97706;border-radius:10px;box-shadow:0 8px 30px #0004;padding:14px 18px;font:13px/1.7 system-ui;white-space:pre'
  help.textContent = [
    'EDIT   right-click: spawn cascade · drag line→line: join · J: join selected',
    '       right-drag: slash sever (⚙ toggles dbl-click) · W/Shift+W: cut/bubble wrap',
    '       drag selected node: move between regions · Delete: dissolve/delete · Ctrl+Z',
    'PROVE  F/B: start forward/backward from the sheet · right-click: moves legal here',
    '       Delete: contextual deletion · W/Shift+W: wraps · drag selection: iterate',
    '       dbl-click term: normalize · Tab/Enter: cycle/apply citation · D: declare · E: exit',
    'ALWAYS Ctrl+drag: physics handle (no meaning) · ?: this map · Esc: close things',
  ].join('\n')
  document.body.append(help)
  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === '?') help.style.display = help.style.display === 'none' ? 'block' : 'none'
    else if (e.key === 'Escape') help.style.display = 'none'
  })
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
    redo: () => { trackSink?.redo?.() },
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

