/**
 * Round-5 session harness: a REAL ProofSession (kernel-recorded steps, meet
 * by canonical form, assembly re-checked by replay) wired to the lab and the
 * verdict move layer. Pages own the PRESENTATION; this owns the truth.
 * The demo goal is succNat's own statement — one forward citation away, so
 * the loop (goal → move → meet → assemble → cite the new theorem) is short,
 * with room to wander (wraps, backward un-cite) and come back.
 */
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'
import type { ProofStep } from '../src/kernel/proof/step'
import type { Theorem } from '../src/kernel/proof/theorem'
import { applyBackward, applyForward, assembleTheorem, meet, sideBoundary, startSession, undoBackward, undoForward, type BackwardAction, type ProofSession } from '../src/app/session'
import { replayProof } from '../src/kernel/proof/step'
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