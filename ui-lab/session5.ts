/**
 * Round-5 session harness: a REAL ProofSession (kernel-recorded steps, meet
 * by canonical form, assembly re-checked by replay) wired to the lab and the
 * verdict move layer. Pages own the PRESENTATION; this owns the truth.
 * The demo goal is succNat's own statement — one forward citation away, so
 * the loop (goal → move → meet → assemble → cite the new theorem) is short,
 * with room to wander (wraps, backward un-cite) and come back.
 */
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../src/kernel/diagram/boundary'
import { applyStep, replayProof, type ProofStep } from '../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../src/kernel/proof/theorem'
import { applyBackward, applyForward, assembleTheorem, meet, sideBoundary, startSession, undoBackward, undoForward, type BackwardAction, type ProofSession } from '../src/app/session'
import type { LabCtx } from './shared'
import { fregeCtx } from './prove4'
import type { MoveSink } from './verdict'

export type SessionLab = {
  session(): ProofSession
  side(): 'forward' | 'backward'
  /** Swap the displayed side (rebuilds the lab view onto that side's current). */
  swap(): void
  met(): boolean
  /** Assemble + kernel-check + adopt into the context; returns the theorem. */
  assemble(name: string): Theorem
  /** The move sink for installVerdictMoves. */
  sink(refuse: (text: string) => void): MoveSink
  /** All states of a side, oldest first (history + current) — the timeline. */
  states(side: 'forward' | 'backward'): Diagram[]
  stepLabels(side: 'forward' | 'backward'): string[]
  /** Replay states of an assembled theorem (lhs, after step 1, …, rhs). */
  replayStates(thm: Theorem): { d: Diagram; boundary: readonly WireId[] }[]
  onChange(fn: () => void): void
}

/** The boot showcase for session pages: the goal's lhs (forward start). */
export function sessionStart(): { d: Diagram; boundary: WireId[] } {
  const t = fregeCtx().theorems.get('succNat')!
  return { d: t.lhs.diagram, boundary: [...t.lhs.boundary] }
}

/**
 * Single-track proving (USER ruling, round 5): pick a direction, derive, and
 * DECLARE — the other end of the theorem falls out of the proof for free.
 * Forward: theorem = (origin ⟹ current), steps as recorded. Backward:
 * theorem = (current ⟹ origin); the internal backward side maintains the
 * exact replay tail (composedTail), so declaration is checkTheorem-ready.
 * The two-ended meet session remains the special case for statements fixed
 * a priori — an optional second front, not an entry ritual.
 */
export type TrackLab = {
  direction(): 'forward' | 'backward' | null
  start(direction: 'forward' | 'backward'): void
  /** Steps so far, origin-first (labels for the timeline). */
  labels(): string[]
  states(): Diagram[]
  boundary(): readonly WireId[]
  /** Build (origin ⟹ current) or (current ⟹ origin), kernel-check by
      replay, adopt into the context; the track keeps going (lemmas stack). */
  declare(name: string): Theorem
  sink(refuse: (text: string) => void): MoveSink
  onChange(fn: () => void): void
}

export function mkTrackLab(lab: LabCtx): TrackLab {
  const ctx = fregeCtx()
  const origin: { d: Diagram; boundary: readonly WireId[] } = { d: lab.d, boundary: [...lab.boundary] }
  const originDWB = (): DiagramWithBoundary => mkDiagramWithBoundary(origin.d, origin.boundary)
  let dir: 'forward' | 'backward' | null = null
  // forward bookkeeping
  let fSteps: ProofStep[] = []
  let fStates: Diagram[] = [origin.d]
  // backward bookkeeping rides a session's backward side (composedTail law)
  let bs: ProofSession | null = null
  const listeners: (() => void)[] = []
  const changed = () => { for (const fn of listeners) fn() }
  const current = (): Diagram => dir === 'backward' ? bs!.backward.current : fStates[fStates.length - 1]!
  const sync = () => {
    lab.mutate(current(), undefined, origin.boundary.filter((w) => current().wires[w] !== undefined))
    changed()
  }
  return {
    direction: () => dir,
    start: (d) => {
      if (dir !== null) throw new Error(`already proving ${dir} — declare or undo to the origin first`)
      dir = d
      if (d === 'backward') bs = startSession(mkDiagramWithBoundary(new DiagramBuilder().build(), []), originDWB(), ctx)
      changed()
    },
    labels: () => {
      const steps = dir === 'backward' ? bs?.backward.steps ?? [] : fSteps
      return steps.map((st) => st.rule === 'theorem' ? `cite ${st.name}` : st.rule)
    },
    states: () => dir === 'backward' ? [...bs!.backward.history, bs!.backward.current] : [...fStates],
    boundary: () => origin.boundary,
    declare: (name) => {
      if (dir === null) throw new Error('start proving first (F forward, B backward)')
      const bd = (d: Diagram) => origin.boundary.filter((w) => d.wires[w] !== undefined)
      const thm: Theorem = dir === 'forward'
        ? { name, lhs: originDWB(), rhs: mkDiagramWithBoundary(current(), bd(current())), steps: [...fSteps] }
        : { name, lhs: mkDiagramWithBoundary(current(), bd(current())), rhs: originDWB(), steps: [...bs!.backward.composedTail] }
      checkTheorem(thm, ctx)
      ctx.theorems.set(name, thm)
      changed()
      return thm
    },
    sink: (refuse) => ({
      ctx,
      apply: (step: ProofStep) => {
        if (dir === null) throw new Error('start proving first (F forward, B backward)')
        if (dir !== 'forward') throw new Error('this track proves backward — right-click for un-citations')
        const next = applyStep(lab.d, step, ctx)
        fSteps.push(step)
        fStates.push(next)
        sync()
      },
      applyBackward: (action: BackwardAction) => {
        if (dir !== 'backward') throw new Error('un-citations belong to a backward track (start with B)')
        bs = applyBackward(bs!, action)
        sync()
      },
      refuse,
      mode: () => dir ?? 'forward',
      undo: () => {
        if (dir === 'forward' && fSteps.length > 0) { fSteps.pop(); fStates.pop(); sync(); return }
        if (dir === 'backward' && bs!.backward.steps.length > 0) { bs = undoBackward(bs!); sync(); return }
        refuse('nothing to undo on this track')
      },
    }),
    onChange: (fn) => listeners.push(fn),
  }
}

export function mkSessionLab(lab: LabCtx): SessionLab {
  const ctx = fregeCtx()
  const succNat = ctx.theorems.get('succNat')!
  let s = startSession(succNat.lhs, succNat.rhs, ctx)
  let side: 'forward' | 'backward' = 'forward'
  const listeners: (() => void)[] = []
  const changed = () => { for (const fn of listeners) fn() }
  const sync = () => {
    const cur = side === 'forward' ? s.forward.current : s.backward.current
    lab.mutate(cur, undefined, sideBoundary(s, side))
    changed()
  }
  return {
    session: () => s,
    side: () => side,
    swap: () => { side = side === 'forward' ? 'backward' : 'forward'; sync() },
    met: () => meet(s),
    assemble: (name) => {
      const thm = assembleTheorem(s, name) // checkTheorem replays inside
      ctx.theorems.set(name, thm)
      changed()
      return thm
    },
    sink: (refuse) => ({
      ctx,
      apply: (step: ProofStep) => {
        if (side !== 'forward') throw new Error('forward moves act on the forward side; swap sides first')
        s = applyForward(s, step)
        sync()
      },
      applyBackward: (action: BackwardAction) => {
        s = applyBackward(s, action)
        sync()
      },
      refuse,
      mode: () => side,
      undo: () => {
        const before = side === 'forward' ? s.forward.steps.length : s.backward.steps.length
        s = side === 'forward' ? undoForward(s) : undoBackward(s)
        const after = side === 'forward' ? s.forward.steps.length : s.backward.steps.length
        if (before === after) { refuse(`nothing to undo on the ${side} side`); return }
        sync()
      },
    }),
    states: (which) => {
      const sd = which === 'forward' ? s.forward : s.backward
      return [...sd.history, sd.current]
    },
    stepLabels: (which) => {
      const sd = which === 'forward' ? s.forward : s.backward
      return sd.steps.map((st) => st.rule === 'theorem' ? `cite ${st.name}` : st.rule)
    },
    replayStates: (thm) => {
      const out: { d: Diagram; boundary: readonly WireId[] }[] = [{ d: thm.lhs.diagram, boundary: thm.lhs.boundary }]
      replayProof(thm.lhs.diagram, thm.steps, ctx, (d) => out.push({ d, boundary: thm.lhs.boundary }))
      return out
    },
    onChange: (fn) => listeners.push(fn),
  }
}