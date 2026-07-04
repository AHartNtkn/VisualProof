import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { exploreForm } from '../kernel/diagram/canonical/explore'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { findOccurrences, occurrenceSelection } from '../kernel/diagram/subgraph/match'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'
import { composeProofs } from '../kernel/proof/compose'

export type Side = {
  readonly current: Diagram
  readonly steps: readonly ProofStep[]
  readonly history: readonly Diagram[]
}

export type BackwardSide = Side & {
  /**
   * Steps that replay EXACTLY (id-level) from `current` back to the original
   * rhs, maintained incrementally: replaying a recorded step reproduces the
   * prior goal only up to isomorphism (fresh ids), so on every action the
   * existing tail is remapped onto the freshly reproduced diagram via
   * composeProofs. Paired with `tailHistory` for undo.
   */
  readonly composedTail: readonly ProofStep[]
  readonly tailHistory: readonly (readonly ProofStep[])[]
}

export type ProofSession = {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  readonly ctx: ProofContext
  readonly forward: Side
  readonly backward: BackwardSide
}

/**
 * The boundary wires of a side's statement: the forward side proves from the
 * lhs, the backward side from the rhs, so each renders its own boundary as
 * frame exits. Ids are stable across a side's proof steps (the proof transforms
 * the interior; the interface persists), so this is the boundary the render
 * engine receives for that side.
 */
export function sideBoundary(s: ProofSession, side: 'forward' | 'backward'): readonly WireId[] {
  return side === 'forward' ? s.lhs.boundary : s.rhs.boundary
}

export function startSession(lhs: DiagramWithBoundary, rhs: DiagramWithBoundary, ctx: ProofContext): ProofSession {
  return {
    lhs, rhs, ctx,
    forward: { current: lhs.diagram, steps: [], history: [] },
    backward: { current: rhs.diagram, steps: [], history: [], composedTail: [], tailHistory: [] },
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
/**
 * Backward proving takes ORDINARY steps (USER ruling: no mirrored un-rule
 * vocabulary — one shared implementation). Acting on the goal G, the step is
 * EXECUTED by the very same appliers with orientation='backward', which flips
 * exactly the polarity-tied gates (erasure, insertion, theorem citation) and
 * nothing else. The recorded replay step is the INVERSE, constructed here by
 * pure diff bookkeeping — its correctness is enforced twice: the reproduction
 * assertion below, and checkTheorem's full forward replay at declaration.
 */
const BACKWARD_INVERTIBLE = new Set([
  'erasure', 'insertion', 'doubleCutIntro', 'doubleCutElim', 'vacuousIntro',
  'vacuousElim', 'iteration', 'deiteration', 'conversion', 'theorem',
  'relUnfold', 'relFold',
])

/** Ids present in `after` but not `before`, sitting directly at `region`. */
function freshSelection(before: Diagram, after: Diagram, region: RegionId): SubgraphSelection {
  return {
    region,
    regions: Object.keys(after.regions).filter((id) => before.regions[id] === undefined && (after.regions[id] as { parent?: RegionId }).parent === region),
    nodes: Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined && after.nodes[id]!.region === region),
    wires: Object.keys(after.wires).filter((id) => before.wires[id] === undefined && after.wires[id]!.scope === region),
  }
}

/** Ids that sat in `fromRegion` in `before` and now sit at `parent` in `after`
    (the contents an elimination promoted). */
function promotedSelection(before: Diagram, after: Diagram, parent: RegionId, fromRegion: RegionId): SubgraphSelection {
  return {
    region: parent,
    regions: Object.entries(after.regions)
      .filter(([id, r]) => r.kind !== 'sheet' && r.parent === parent &&
        (before.regions[id] as { parent?: RegionId } | undefined)?.parent === fromRegion)
      .map(([id]) => id),
    nodes: Object.entries(after.nodes)
      .filter(([id, n]) => n.region === parent && before.nodes[id]?.region === fromRegion)
      .map(([id]) => id),
    wires: Object.entries(after.wires)
      .filter(([id, w]) => w.scope === parent && before.wires[id]?.scope === fromRegion)
      .map(([id]) => id),
  }
}

/** The forward step undoing `step`: applyStep(gPrime, inverseStep(...)) ≅ g.
    Diff bookkeeping only — every transformation lives in the appliers. */
function inverseStep(g: Diagram, step: ProofStep, gPrime: Diagram, ctx: ProofContext): ProofStep {
  switch (step.rule) {
    case 'erasure': {
      const { pattern, attachments } = extractSubgraph(g, step.sel)
      return { rule: 'insertion', region: step.sel.region, pattern, attachments, binders: {} }
    }
    case 'insertion':
      return { rule: 'erasure', sel: freshSelection(g, gPrime, step.region) }
    case 'doubleCutIntro': {
      const outer = Object.entries(gPrime.regions).find(
        ([id, r]) => g.regions[id] === undefined && r.kind === 'cut' && r.parent === step.sel.region,
      )
      if (outer === undefined) throw new Error('backward doubleCutIntro left no fresh outer cut; this is a session bug')
      return { rule: 'doubleCutElim', region: outer[0] }
    }
    case 'doubleCutElim': {
      const outerRegion = g.regions[step.region]!
      const parent: RegionId = outerRegion.kind === 'sheet' ? g.root : outerRegion.parent
      const inner = Object.entries(g.regions).find(([, r]) => r.kind === 'cut' && r.parent === step.region)!
      return { rule: 'doubleCutIntro', sel: promotedSelection(g, gPrime, parent, inner[0]) }
    }
    case 'vacuousIntro': {
      const bubble = Object.entries(gPrime.regions).find(
        ([id, r]) => g.regions[id] === undefined && r.kind === 'bubble' && r.parent === step.sel.region,
      )
      if (bubble === undefined) throw new Error('backward vacuousIntro left no fresh bubble; this is a session bug')
      return { rule: 'vacuousElim', region: bubble[0] }
    }
    case 'vacuousElim': {
      const b = g.regions[step.region]
      if (b === undefined || b.kind !== 'bubble') throw new Error(`'${step.region}' is not a bubble`)
      return { rule: 'vacuousIntro', sel: promotedSelection(g, gPrime, b.parent, step.region), arity: b.arity }
    }
    case 'iteration':
      return { rule: 'deiteration', sel: freshSelection(g, gPrime, step.target), fuel: 64 }
    case 'deiteration': {
      // the removed copy's justifier survives in gPrime; iterating it back
      // into the emptied region must reproduce g — try each occurrence and
      // let the reproduction check pick (the assertion below re-verifies)
      const { pattern } = extractSubgraph(g, step.sel)
      const occs = findOccurrences(gPrime, pattern, { fuel: step.fuel, mode: 'exact' }).matches
      for (const occ of occs) {
        const cand: ProofStep = { rule: 'iteration', sel: occurrenceSelection(pattern, occ, gPrime), target: step.sel.region }
        try {
          if (exploreForm(applyStep(gPrime, cand, ctx)) === exploreForm(g)) return cand
        } catch {
          // an out-of-scope occurrence refuses to iterate here; try the next
        }
      }
      throw new Error('backward deiteration: no surviving occurrence iterates back to the goal (the justifying copy must remain in scope)')
    }
    case 'conversion': {
      const node = g.nodes[step.node]
      if (node === undefined || node.kind !== 'term') throw new Error(`'${step.node}' is not a term node`)
      return {
        rule: 'conversion', node: step.node, term: node.term,
        certificate: { leftSteps: step.certificate.rightSteps, rightSteps: step.certificate.leftSteps },
        attachments: {},
      }
    }
    case 'theorem':
      return {
        rule: 'theorem', name: step.name,
        at: { sel: freshSelection(g, gPrime, step.at.sel.region), args: [...step.at.args] },
        direction: step.direction === 'forward' ? 'reverse' : 'forward',
      }
    case 'relUnfold': {
      const ref = g.nodes[step.node]
      if (ref === undefined || ref.kind !== 'ref') throw new Error(`'${step.node}' is not a relation reference`)
      const args: WireId[] = []
      for (let i = 0; i < ref.arity; i++) {
        const port = { kind: 'arg', index: i } as const
        const holder = Object.entries(g.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === step.node && ep.port.kind === 'arg' && ep.port.index === i))
        if (holder === undefined) throw new Error(`ref '${step.node}' has no wire on arg ${i}`)
        void port
        args.push(holder[0])
      }
      return { rule: 'relFold', sel: freshSelection(g, gPrime, ref.region), defId: ref.defId, args }
    }
    case 'relFold': {
      const fresh = freshSelection(g, gPrime, step.sel.region)
      const refId = fresh.nodes.find((id) => gPrime.nodes[id]!.kind === 'ref')
      if (refId === undefined) throw new Error('backward relFold left no reference node; this is a session bug')
      return { rule: 'relUnfold', node: refId }
    }
    default:
      throw new Error(`rule '${step.rule}' has no backward inverse yet (invertible: ${[...BACKWARD_INVERTIBLE].join(', ')})`)
  }
}

export function applyBackward(s: ProofSession, step: ProofStep): ProofSession {
  const g = s.backward.current
  if (!BACKWARD_INVERTIBLE.has(step.rule)) {
    throw new Error(`rule '${step.rule}' has no backward inverse yet (invertible: ${[...BACKWARD_INVERTIBLE].join(', ')})`)
  }
  // SHARED execution: the same appliers, orientation flips only polarity gates
  const gPrime = applyStep(g, step, s.ctx, 'backward')
  const inv = inverseStep(g, step, gPrime, s.ctx)
  // the reproduction assertion: forward(inv, G\u2032) must match G semantically
  const reproduced = applyStep(gPrime, inv, s.ctx)
  if (exploreForm(reproduced) !== exploreForm(g)) {
    throw new Error(`backward '${step.rule}' could not reconstruct the goal it inverted; this is a session bug`)
  }
  // re-anchor the existing exact tail onto the reproduced diagram: it was
  // exact from g, and `reproduced` is only isomorphic to g, so map it across
  const remapped = composeProofs(reproduced, g, s.backward.composedTail, s.ctx)
  return {
    ...s,
    backward: {
      current: gPrime,
      steps: [...s.backward.steps, inv],
      history: [...s.backward.history, g],
      composedTail: [inv, ...remapped],
      tailHistory: [...s.backward.tailHistory, s.backward.composedTail],
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
      composedTail: s.backward.tailHistory[s.backward.tailHistory.length - 1]!,
      tailHistory: s.backward.tailHistory.slice(0, -1),
    },
  }
}

export function meet(s: ProofSession): boolean {
  return exploreForm(s.forward.current) === exploreForm(s.backward.current)
}

/** Compose both halves into the finished theorem (caller runs checkTheorem). */
export function assembleTheorem(s: ProofSession, name: string): Theorem {
  if (!meet(s)) throw new Error('the two sides have not met; nothing to assemble')
  // composedTail is exact from backward.current; one final remap crosses the meet
  const composed = composeProofs(s.forward.current, s.backward.current, s.backward.composedTail, s.ctx)
  return {
    name,
    lhs: s.lhs,
    rhs: s.rhs,
    steps: [...s.forward.steps, ...composed],
  }
}

/** Verify and add a finished theorem to the session context — citable from now on. */
export function adoptTheorem(s: ProofSession, thm: Theorem): ProofSession {
  if (s.ctx.theorems.has(thm.name)) {
    throw new Error(`'${thm.name}' already names a theorem in this session`)
  }
  checkTheorem(thm, s.ctx)
  const theorems = new Map(s.ctx.theorems)
  theorems.set(thm.name, thm)
  return { ...s, ctx: { theorems, relations: s.ctx.relations } }
}
