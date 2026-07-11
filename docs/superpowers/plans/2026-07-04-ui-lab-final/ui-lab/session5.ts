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
import { applyStep, replayProof, type ProofContext, type ProofStep } from '../src/kernel/proof/step'
import { checkTheorem, type Theorem } from '../src/kernel/proof/theorem'
import { applyBackward, applyForward, assembleTheorem, currentSide, meet, sideBoundary, startSession, undoBackward, undoForward, type ProofSession } from '../src/app/session'
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
 * recorded flip-gated steps, replayed from the rhs at declaration.
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
  /** The current position in history (0 = origin). States AFTER the cursor
      are the retained future — redo reaches them; a NEW move from here
      discards them (USER ruling: scrubbing is rapid undo AND redo). */
  cursor(): number
  /** Build (origin ⟹ cursor state) or (cursor state ⟹ origin) from the steps
      up to the cursor, kernel-check by replay, adopt into the context. */
  declare(name: string): Theorem
  /** Move the cursor to state k — non-destructive time travel (undo/redo). */
  rewind(k: number): void
  sink(refuse: (text: string) => void): MoveSink
  onChange(fn: () => void): void
}

/** Human copy for a step — rule identifiers are jargon, not labels. */
export function stepLabel(step: ProofStep): string {
  switch (step.rule) {
    case 'theorem': return `cite ${step.name}`
    case 'doubleCutIntro': return 'wrap in double cut'
    case 'doubleCutElim': return 'eliminate double cut'
    case 'vacuousIntro': return 'wrap in bubble'
    case 'vacuousElim': return 'dissolve bubble'
    case 'erasure': return 'erase'
    case 'insertion': return 'insert'
    case 'iteration': return 'iterate'
    case 'deiteration': return 'deiterate'
    case 'conversion': return 'convert (βη)'
    case 'relUnfold': return 'unfold'
    case 'relFold': return `fold into ${step.defId}`
    case 'comprehensionInstantiate': return 'instantiate'
    default: return step.rule
  }
}

export function mkTrackLab(lab: LabCtx, ctx: ProofContext = fregeCtx()): TrackLab {
  const origin: { d: Diagram; boundary: readonly WireId[] } = { d: lab.d, boundary: [...lab.boundary] }
  const originDWB = (): DiagramWithBoundary => mkDiagramWithBoundary(origin.d, origin.boundary)
  let dir: 'forward' | 'backward' | null = null
  // forward bookkeeping
  let fSteps: ProofStep[] = []
  let fStates: Diagram[] = [origin.d]
  // what the USER did, in their orientation (backward.steps hold inverses)
  let actionLabels: string[] = []
  // backward bookkeeping: one immutable session snapshot per state, so the
  // retained future survives cursor travel
  let bSessions: ProofSession[] = []
  // the time-travel position: 0 = origin; states beyond it are the future
  let cursor = 0
  const listeners: (() => void)[] = []
  const changed = () => { for (const fn of listeners) fn() }
  const stateAt = (k: number): Diagram => dir === 'backward' ? currentSide(bSessions[k]!, 'backward') : fStates[k]!
  const current = (): Diagram => stateAt(cursor)
  const count = (): number => dir === 'backward' ? bSessions.length - 1 : fStates.length - 1
  const sync = () => {
    lab.mutate(current(), undefined, origin.boundary.filter((w) => current().wires[w] !== undefined))
    changed()
  }
  return {
    direction: () => dir,
    start: (d) => {
      if (dir !== null) throw new Error(`already proving ${dir} — declare or undo to the origin first`)
      dir = d
      if (d === 'backward') bSessions = [startSession(mkDiagramWithBoundary(new DiagramBuilder().build(), []), originDWB(), ctx)]
      changed()
    },
    labels: () => [...actionLabels],
    states: () => {
      const out: Diagram[] = []
      for (let k = 0; k <= count(); k++) out.push(stateAt(k))
      return out
    },
    boundary: () => origin.boundary,
    cursor: () => cursor,
    declare: (name) => {
      if (dir === null) throw new Error('start proving first (F forward, B backward)')
      const bd = (d: Diagram) => origin.boundary.filter((w) => d.wires[w] !== undefined)
      const thm: Theorem = dir === 'forward'
        ? { name, lhs: originDWB(), rhs: mkDiagramWithBoundary(current(), bd(current())), steps: fSteps.slice(0, cursor) }
        : { name, lhs: mkDiagramWithBoundary(current(), bd(current())), rhs: originDWB(), steps: [], backSteps: [...bSessions[cursor]!.backward.steps] }
      checkTheorem(thm, ctx)
      ctx.theorems.set(name, thm)
      changed()
      return thm
    },
    sink: (refuse) => ({
      ctx,
      apply: (step: ProofStep) => {
        if (dir === null) throw new Error('start proving first (F forward, B backward)')
        // a NEW move from the cursor discards the retained future
        fSteps = fSteps.slice(0, cursor)
        fStates = fStates.slice(0, cursor + 1)
        bSessions = bSessions.slice(0, cursor + 1)
        actionLabels = actionLabels.slice(0, cursor)
        if (dir === 'forward') {
          const next = applyStep(lab.d, step, ctx)
          fSteps.push(step)
          fStates.push(next)
        } else {
          bSessions.push(applyBackward(bSessions[cursor]!, step))
        }
        actionLabels.push(stepLabel(step))
        cursor++
        sync()
      },
      refuse,
      mode: () => dir ?? 'forward',
      undo: () => {
        if (dir !== null && cursor > 0) { cursor--; sync(); return }
        refuse('nothing to undo on this track')
      },
      redo: () => {
        if (dir !== null && cursor < count()) { cursor++; sync(); return }
        refuse('nothing to redo on this track')
      },
    }),
    rewind: (k) => {
      if (dir === null) throw new Error('start proving first (F forward, B backward)')
      if (k < 0 || k > count()) throw new Error(`no state ${k} on this track`)
      cursor = k
      sync()
    },
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
    const cur = currentSide(s, side)
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
        // ONE vocabulary: the side decides the orientation, not the caller
        s = side === 'forward' ? applyForward(s, step) : applyBackward(s, step)
        sync()
      },
      refuse,
      mode: () => side,
      undo: () => {
        const before = s[side].cursor
        s = side === 'forward' ? undoForward(s) : undoBackward(s)
        const after = s[side].cursor
        if (before === after) { refuse(`nothing to undo on the ${side} side`); return }
        sync()
      },
    }),
    states: (which) => {
      const sd = which === 'forward' ? s.forward : s.backward
      return [...sd.states]
    },
    stepLabels: (which) => {
      const sd = which === 'forward' ? s.forward : s.backward
      return sd.steps.map((st) => st.rule === 'theorem' ? `cite ${st.name}` : st.rule)
    },
    replayStates: (thm) => {
      // dual-form theorems: the forward half walks from the lhs, the backward
      // half from the rhs — display them lhs → meet → rhs
      const fwd: { d: Diagram; boundary: readonly WireId[] }[] = [{ d: thm.lhs.diagram, boundary: thm.lhs.boundary }]
      replayProof(thm.lhs.diagram, thm.steps, ctx, (d) => fwd.push({ d, boundary: thm.lhs.boundary }))
      const bwd: { d: Diagram; boundary: readonly WireId[] }[] = []
      replayProof(thm.rhs.diagram, thm.backSteps ?? [], ctx, (d) => bwd.push({ d, boundary: thm.rhs.boundary }), 'backward')
      bwd.reverse()
      // the backward walk's last-produced state IS the meet (≅ fwd's end) —
      // skip it to avoid showing the meet twice; then append rhs-ward states
      return [...fwd, ...bwd.slice(1), ...(thm.backSteps?.length ? [{ d: thm.rhs.diagram, boundary: thm.rhs.boundary }] : [])]
    },
    onChange: (fn) => listeners.push(fn),
  }
}
