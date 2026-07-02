import type { Diagram, RegionId, NodeId, WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import { diagramFingerprint, boundaryFingerprint } from '../kernel/diagram/canonical/fingerprint'
import { polarity } from '../kernel/diagram/regions'
import { spliceSubgraph, removeSubgraph } from '../kernel/diagram/subgraph/splice'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { applyDoubleCutElim } from '../kernel/rules/doublecut'
import { applyVacuousBubbleElim } from '../kernel/rules/vacuous'
import { applyConversion } from '../kernel/rules/conversion'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import { applyStep } from '../kernel/proof/step'
import type { Theorem, TheoremApplication } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'
import { composeProofs } from '../kernel/proof/compose'
import type { Term } from '../kernel/term'

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
export type BackwardAction =
  | { readonly kind: 'unDoubleCut'; readonly outer: RegionId }
  | { readonly kind: 'unVacuousBubble'; readonly bubble: RegionId }
  | { readonly kind: 'unErase'; readonly region: RegionId; readonly pattern: DiagramWithBoundary; readonly attachments: readonly WireId[] }
  | { readonly kind: 'unConvert'; readonly node: NodeId; readonly term: Term; readonly fuel: number }
  | { readonly kind: 'unCite'; readonly name: string; readonly at: TheoremApplication }

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
    case 'unErase': {
      if (polarity(g, action.region) !== 'positive') {
        throw new Error(`un-erase targets a positive region (the forward erasure's gate); '${action.region}' is negative`)
      }
      gPrime = spliceSubgraph(g, action.region, action.pattern, action.attachments)
      const regions = Object.keys(gPrime.regions).filter((id) => g.regions[id] === undefined && (gPrime.regions[id] as { parent?: RegionId }).parent === action.region)
      const nodes = Object.keys(gPrime.nodes).filter((id) => g.nodes[id] === undefined && gPrime.nodes[id]!.region === action.region)
      const wires = Object.keys(gPrime.wires).filter((id) => g.wires[id] === undefined && gPrime.wires[id]!.scope === action.region)
      step = { rule: 'erasure', sel: { region: action.region, regions, nodes, wires } }
      break
    }
    case 'unConvert': {
      const node = g.nodes[action.node]
      if (node === undefined || node.kind !== 'term') throw new Error(`'${action.node}' is not a term node`)
      const res = applyConversion(g, action.node, action.term, action.fuel)
      gPrime = res.diagram
      step = {
        rule: 'conversion', node: action.node, term: node.term,
        certificate: { leftSteps: res.certificate.rightSteps, rightSteps: res.certificate.leftSteps },
        attachments: {},
      }
      break
    }
    case 'unCite': {
      const thm = s.ctx.theorems.get(action.name)
      if (thm === undefined) throw new Error(`unknown theorem '${action.name}'`)
      if (polarity(g, action.at.sel.region) !== 'positive') {
        throw new Error(`un-citation targets a positive region (the forward citation's gate); '${action.at.sel.region}' is negative`)
      }
      // verify the selection IS an rhs-occurrence (applyTheorem's machinery, sans polarity gate)
      const { pattern, attachments, binderStubs } = extractSubgraph(g, action.at.sel)
      if (binderStubs.length > 0) throw new Error('open occurrences cannot be un-cited')
      if (action.at.args.length !== attachments.length || new Set(action.at.args).size !== action.at.args.length) {
        throw new Error(`the selection has ${attachments.length} attachment wires; arguments must list each exactly once`)
      }
      const reordered = action.at.args.map((a) => {
        const j = attachments.indexOf(a)
        if (j === -1) throw new Error(`argument wire '${a}' is not an attachment of the selection`)
        return pattern.boundary[j]!
      })
      if (boundaryFingerprint(mkDiagramWithBoundary(pattern.diagram, reordered)) !== boundaryFingerprint(thm.rhs)) {
        throw new Error(`the selection is not an occurrence of '${action.name}' right-hand side`)
      }
      const spliced = spliceSubgraph(g, action.at.sel.region, thm.lhs, action.at.args)
      gPrime = removeSubgraph(spliced, action.at.sel)
      // the forward citation references the spliced LHS occurrence in G′
      const lhsRegions = Object.keys(gPrime.regions).filter((id) => g.regions[id] === undefined && (gPrime.regions[id] as { parent?: RegionId }).parent === action.at.sel.region)
      const lhsNodes = Object.keys(gPrime.nodes).filter((id) => g.nodes[id] === undefined && gPrime.nodes[id]!.region === action.at.sel.region)
      const lhsWires = Object.keys(gPrime.wires).filter((id) => g.wires[id] === undefined && gPrime.wires[id]!.scope === action.at.sel.region)
      step = {
        rule: 'theorem', name: action.name, direction: 'forward',
        at: { sel: { region: action.at.sel.region, regions: lhsRegions, nodes: lhsNodes, wires: lhsWires }, args: action.at.args },
      }
      break
    }
  }
  // the reproduction assertion: forward(step, G′) must match G semantically by fingerprint
  const reproduced = applyStep(gPrime, step, s.ctx)
  if (diagramFingerprint(reproduced) !== diagramFingerprint(g)) {
    throw new Error(`backward action '${action.kind}' could not reconstruct the goal it inverted; this is a session bug`)
  }
  // re-anchor the existing exact tail onto the reproduced diagram: it was
  // exact from g, and `reproduced` is only isomorphic to g, so map it across
  const remapped = composeProofs(reproduced, g, s.backward.composedTail, s.ctx)
  return {
    ...s,
    backward: {
      current: gPrime,
      steps: [...s.backward.steps, step],
      history: [...s.backward.history, g],
      composedTail: [step, ...remapped],
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
  return diagramFingerprint(s.forward.current) === diagramFingerprint(s.backward.current)
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
