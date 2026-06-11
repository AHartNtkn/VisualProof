import type { Diagram, RegionId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { diagramFingerprint } from '../kernel/diagram/canonical/fingerprint'
import { applyDoubleCutElim } from '../kernel/rules/doublecut'
import { applyVacuousBubbleElim } from '../kernel/rules/vacuous'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { composeProofs } from '../kernel/proof/compose'

export type Side = {
  readonly current: Diagram
  readonly steps: readonly ProofStep[]
  readonly history: readonly Diagram[]
}

export type ProofSession = {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly ctx: ProofContext
  readonly forward: Side
  readonly backward: Side
}

export function startSession(lhs: DiagramWithBoundary, rhs: DiagramWithBoundary, ctx: ProofContext): ProofSession {
  return {
    lhs, rhs, ctx,
    forward: { current: lhs.diagram, steps: [], history: [] },
    backward: { current: rhs.diagram, steps: [], history: [] },
  }
}

/** Apply a forward step through the kernel; refusals propagate untouched. */
export function applyForward(s: ProofSession, step: ProofStep): ProofSession {
  const next = applyStep(s.forward.current, step, s.ctx)
  return {
    ...s,
    forward: {
      current: next,
      steps: [...s.forward.steps, step],
      history: [...s.forward.history, s.forward.current],
    },
  }
}

export function undoForward(s: ProofSession): ProofSession {
  const history = s.forward.history
  if (history.length === 0) throw new Error('nothing to undo on the forward side')
  return {
    ...s,
    forward: {
      current: history[history.length - 1]!,
      steps: s.forward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
}

/**
 * Backward actions transform the GOAL side: the user removes structure the
 * forward direction would add. Each action computes the inverse-applied
 * diagram G′ and the forward step (G′ → G) TOGETHER, then asserts that
 * replaying the step on G′ reproduces G semantically (by fingerprint) — keeping
 * the recorded tail replayable without id-rewriting anywhere except the meet.
 */
export type BackwardAction =
  | { readonly kind: 'unDoubleCut'; readonly outer: RegionId }
  | { readonly kind: 'unVacuousBubble'; readonly bubble: RegionId }

export function applyBackward(s: ProofSession, action: BackwardAction): ProofSession {
  const g = s.backward.current
  let gPrime: Diagram
  let step: ProofStep
  switch (action.kind) {
    case 'unDoubleCut': {
      const inner = Object.entries(g.regions).find(
        ([, r]) => r.kind === 'cut' && r.parent === action.outer,
      )
      if (inner === undefined) throw new Error(`'${action.outer}' has no inner cut to unwrap`)
      gPrime = applyDoubleCutElim(g, action.outer)
      // the forward step re-creating the pair: intro around what the inner
      // cut contained, which now sits where the OUTER cut's parent was
      const outerRegion = g.regions[action.outer]!
      const parent: RegionId = outerRegion.kind === 'sheet' ? g.root : outerRegion.parent
      const regions = Object.entries(gPrime.regions)
        .filter(([id, r]) => r.kind !== 'sheet' && r.parent === parent && g.regions[id] !== undefined &&
          (g.regions[id]! as { parent?: RegionId }).parent === inner[0])
        .map(([id]) => id)
      const nodes = Object.entries(gPrime.nodes)
        .filter(([id, n]) => n.region === parent && g.nodes[id]?.region === inner[0])
        .map(([id]) => id)
      const wires = Object.entries(gPrime.wires)
        .filter(([id, w]) => w.scope === parent && g.wires[id]?.scope === inner[0])
        .map(([id]) => id)
      step = { rule: 'doubleCutIntro', sel: { region: parent, regions, nodes, wires } }
      break
    }
    case 'unVacuousBubble': {
      const b = g.regions[action.bubble]
      if (b === undefined || b.kind !== 'bubble') throw new Error(`'${action.bubble}' is not a bubble`)
      gPrime = applyVacuousBubbleElim(g, action.bubble)
      const parent = b.parent
      const regions = Object.entries(gPrime.regions)
        .filter(([id, r]) => r.kind !== 'sheet' && r.parent === parent &&
          (g.regions[id] as { parent?: RegionId } | undefined)?.parent === action.bubble)
        .map(([id]) => id)
      const nodes = Object.entries(gPrime.nodes)
        .filter(([id, n]) => n.region === parent && g.nodes[id]?.region === action.bubble)
        .map(([id]) => id)
      const wires = Object.entries(gPrime.wires)
        .filter(([id, w]) => w.scope === parent && g.wires[id]?.scope === action.bubble)
        .map(([id]) => id)
      step = { rule: 'vacuousIntro', sel: { region: parent, regions, nodes, wires }, arity: b.arity }
      break
    }
  }
  // the reproduction assertion: forward(step, G′) must match G semantically by fingerprint
  const reproduced = applyStep(gPrime, step, s.ctx)
  if (diagramFingerprint(reproduced) !== diagramFingerprint(g)) {
    throw new Error(`backward action '${action.kind}' could not reconstruct the goal it inverted; this is a session bug`)
  }
  return {
    ...s,
    backward: {
      current: gPrime,
      steps: [...s.backward.steps, step],
      history: [...s.backward.history, g],
    },
  }
}

export function undoBackward(s: ProofSession): ProofSession {
  const history = s.backward.history
  if (history.length === 0) throw new Error('nothing to undo on the backward side')
  return {
    ...s,
    backward: {
      current: history[history.length - 1]!,
      steps: s.backward.steps.slice(0, -1),
      history: history.slice(0, -1),
    },
  }
}

export function meet(s: ProofSession): boolean {
  return diagramFingerprint(s.forward.current) === diagramFingerprint(s.backward.current)
}

/** Compose both halves into the finished theorem (caller runs checkTheorem). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  const tail = [...s.backward.steps].reverse()
  const composed = composeProofs(s.forward.current, s.backward.current, tail, s.ctx)
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    steps: [...s.forward.steps, ...composed],
  }
}
