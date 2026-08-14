import { EMPTY_PROOF_CONTEXT, checkTheorem } from '../../kernel/proof'
import { isAncestorOrEqual, mkDiagramWithBoundary } from '../../kernel/diagram'
import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import { relSig } from '../../kernel/diagram/sig'
import { bareWireAssembly, bareWireDescription, RuleError } from '../../kernel/rules'
import { emptyGraph, finishDiagramWithBoundary } from '../../theories/graph'
import { PrimitiveStepRecorder, onlyNewCut } from '../../theories/record'
import { deiterationStep } from '../../app/interact/moves'
import { bareWires, childCuts, headWireOf, nodesIn } from '../diagram-scan'
import { readKnobs, type GeneratedProblem, type GeneratorFamily } from '../index'
import {
  atomName,
  containsDoubleNegation,
  containsDuplicateConjunct,
  printTheorem,
  sameFormula,
  usedAtoms,
} from '../prop/formula'
import { isMinimalTautology } from '../prop/shrink'
import { propWireIndex, readPropRegion, readPropTheorem } from '../prop/read'
import { enumerateMoves, type CandidateMove, type MoveClass } from '../moves'

/**
 * Walk move weights, PER CLASS — a class's share of the draw is fixed by
 * this table, independent of how many candidates that class currently
 * offers (the candidate itself is then chosen uniformly within the class).
 * Distribution shaping ONLY — legality always comes from enumerating
 * actually-applicable moves, and no correctness property depends on these
 * values. The ordering encodes the spec's bias: iteration/deiteration and
 * double-cut moves build reusable structure; atomSpawn is the junk source
 * (it is insertion, seen from the player's backward proof); erasure undoes
 * walk progress. The minimality filter, not the weights, guarantees quality.
 */
const WALK_CLASS_WEIGHTS: Readonly<Record<MoveClass, number>> = {
  iteration: 4,
  doubleCut: 3,
  spawn: 2,
  erasure: 1,
  vacuity: 0, // excluded from the walk alphabet below; listed for the type
}
const WALK_CLASSES: ReadonlySet<MoveClass> = new Set(['erasure', 'spawn', 'doubleCut', 'iteration'])

export const propWalkFamily: GeneratorFamily = {
  id: 'prop-walk',
  label: 'Random tautology (rule walk)',
  description: 'Applies real kernel rules forward from the blank sheet; every problem carries a checked derivation.',
  // Walk length default measured, not guessed (final-review fix wave): at
  // length 12 (the originally specified default), 10 seeds against
  // all-default knobs took 0.8-28.8s to generate and one of them exceeded
  // the attempt cap outright — unworkable inside any reasonable test
  // timeout. At length 8, the same measurement (10 seeds, atoms 2,
  // attempts 1,000) generated every seed in 0.1-4.3s (avg ~2s), 0/10
  // failures — comfortably inside a 10s timeout. Atoms doesn't materially
  // affect the cost (measured equal at length 6 for atoms 1 vs 2), so it
  // keeps its original default.
  knobs: [
    { id: 'atoms', label: 'Atoms (max)', min: 1, default: 2 },
    { id: 'length', label: 'Walk length', min: 1, default: 8 },
    { id: 'attempts', label: 'Attempt cap', min: 1, default: 1_000 },
  ],
  generate(params, rng): GeneratedProblem {
    const knobs = readKnobs(propWalkFamily, params)
    for (let attempt = 0; attempt < knobs.attempts!; attempt += 1) {
      const problem = tryWalk(knobs.atoms!, knobs.length!, rng)
      if (problem !== null) return problem
    }
    throw new Error(
      `prop-walk: no walk survived the minimality filter in ${knobs.attempts} attempts; `
      + `try a longer walk or raise 'Attempt cap'`,
    )
  },
}

function tryWalk(atoms: number, length: number, rng: () => number): GeneratedProblem | null {
  const lhs = finishDiagramWithBoundary(emptyGraph(), [])
  const recorder = new PrimitiveStepRecorder(lhs, EMPTY_PROOF_CONTEXT, 'forward')
  // Prelude: the ∀ shell — an empty double cut, then one bare proposition
  // wire per atom vacuity-inserted into the annulus (matching the shape
  // quantifierScope('forall') produces).
  const before = recorder.diagram
  recorder.record('open universal shell', {
    rule: 'doubleCutIntro',
    sel: { region: recorder.diagram.root, regions: [], nodes: [], wires: [] },
  })
  const outer = onlyNewCut(before, recorder.diagram, recorder.diagram.root)
  const inner = onlyNewCut(before, recorder.diagram, outer)
  for (let index = 0; index < atoms; index += 1) {
    recorder.record(`declare proposition ${atomName(index)}`, {
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly(`genp${index}`, outer, relSig([])),
    })
  }
  for (let move = 0; move < length; move += 1) {
    const candidates = enumerateMoves(recorder.diagram, 'forward', WALK_CLASSES, inner)
    if (!applyWeightedRandomMove(recorder, candidates, rng)) return null
  }
  // The 'atoms' knob is an upper bound: a declared proposition the walk
  // never used is left as a bare (all-pin) wire; vacuity-delete it before
  // certifying, rather than rejecting the whole walk over it.
  for (
    let bare = bareWires(recorder.diagram);
    bare.length > 0;
    bare = bareWires(recorder.diagram)
  ) {
    const wireId = bare[0]!
    recorder.record(`erase unused proposition wire '${wireId}'`, {
      rule: 'vacuity',
      direction: 'delete',
      assembly: bareWireDescription(recorder.diagram, wireId),
    })
  }
  // Normalization: a JOINT fixpoint of two ungated-equivalence rewrites,
  // repeated until neither finder fires. Each rewrite strictly shrinks the
  // diagram (doubleCutElim removes two cut regions; a duplicate deiteration
  // removes at least one node or region), and the diagram's (regions +
  // nodes + wires) count is bounded below by zero, so the loop terminates.
  // Interleaving matters: eliminating an empty-annulus double-cut pair
  // beside an occurrence can splice a fresh same-region duplicate up into
  // the parent region (e.g. A ∧ ¬¬A′, A′=A: removing the ¬¬ promotes A′
  // up beside A, exposing A ∧ A), so each pass re-checks double-cut first.
  for (;;) {
    const doubleCut = findDoubleCutToNormalize(recorder.diagram, inner)
    if (doubleCut !== null) {
      recorder.record('normalize double cut', { rule: 'doubleCutElim', region: doubleCut })
      continue
    }
    const duplicate = findDuplicateToNormalize(recorder.diagram, inner)
    if (duplicate !== null) {
      recorder.record('normalize duplicate', deiterationStep(recorder.diagram, duplicate))
      continue
    }
    break
  }
  const diagram = recorder.diagram
  // Certification: replay the recorded derivation from the blank sheet.
  checkTheorem(
    { name: 'generated', lhs, rhs: mkDiagramWithBoundary(diagram, []), actions: recorder.actions },
    EMPTY_PROOF_CONTEXT,
  )
  // Polish filters (spec): readable, minimal.
  let reading
  try {
    reading = readPropTheorem(diagram)
  } catch (error) {
    // The walk left the propositional ∀-shell shape (e.g. it emptied the
    // body into a non-shell form). readPropTheorem's own descriptive
    // rejections (message prefixed 'readPropTheorem:') are walk rejections,
    // not bugs; anything else propagates.
    if (error instanceof Error && error.message.startsWith('readPropTheorem:')) return null
    throw error
  }
  if (usedAtoms(reading.formula).size !== reading.wires.length) {
    throw new Error(
      `prop-walk: internal error — ${reading.wires.length} proposition wire(s) survived the `
      + `bare-wire cleanup but only ${usedAtoms(reading.formula).size} atom(s) are used in the `
      + 'read formula; every surviving wire should head an atom occurrence',
    )
  }
  if (!isMinimalTautology(reading.formula, reading.wires.length)) return null
  // The normalization above eliminates every empty-annulus double-cut pair,
  // so a ¬¬ surviving here is possible only when a pin sits inside the
  // pair's annulus (the applier rightly refuses to eliminate such a pair,
  // since erasing it would strand the pin below the two-end floor) — a
  // rare legitimate rejection of this walk, not a bug.
  if (containsDoubleNegation(reading.formula)) return null
  // Unlike the ¬¬ case above, this is a BUG backstop, not a legitimate
  // rejection: findDoubleCutToNormalize structurally excludes pin-holding
  // annuli from its own candidates (doubleCutElim would destroy the pin —
  // no rescue is possible), but findDuplicateToNormalize excludes nothing
  // on pin grounds, and every step recorder.record applies (including the
  // 'deiteration' this loop records) already auto-pins through
  // ScopePreservationError universally (#recordAction, src/theories/
  // record.ts — not specific to erasure/vacuity). A genuine same-region
  // duplicate the finder reports is therefore always removable; surviving
  // to here means the finder or the joint loop above missed a fixpoint.
  if (containsDuplicateConjunct(reading.formula)) {
    throw new Error(
      'prop-walk: internal error — a same-region duplicate conjunct survived normalization to '
      + 'fixpoint; findDuplicateToNormalize or the joint normalization loop is broken',
    )
  }
  return { diagram, statement: printTheorem(reading.formula), walkUpperBound: recorder.actions.length }
}

/**
 * Find a cut region strictly inside `inner` (the body) whose annulus is
 * empty (exactly one child cut, no nodes) — the shape doubleCutElim
 * removes. `inner` itself is excluded: it and its ¬-headed body are the
 * shell's own intrinsic double-cut pair, not walk-introduced junk.
 */
export function findDoubleCutToNormalize(diagram: Diagram, inner: RegionId): RegionId | null {
  for (const id of Object.keys(diagram.regions).sort()) {
    if (diagram.regions[id]!.kind !== 'cut') continue
    if (id === inner) continue
    if (!isAncestorOrEqual(diagram, inner, id)) continue
    if (childCuts(diagram, id).length !== 1) continue
    if (nodesIn(diagram, id).length !== 0) continue
    return id
  }
  return null
}

/**
 * Find a same-region duplicate strictly at-or-below `inner` (the body): a
 * pair of siblings in one region that are exactly the same content, with no
 * cut boundary between them — a free, uninteresting deiteration for the
 * backward player (a positive-polarity analogue of the ¬¬ repair above; see
 * the design doc's idempotence-repair motivation). Two shapes qualify:
 *
 *   (a) two atom nodes in the same region heading the SAME wire;
 *   (b) two child cuts of the same region whose content — read via
 *       `readPropRegion` against a shared, whole-diagram wire index, so
 *       comparison is keyed by wire identity, not just shape — is exactly
 *       equal (`sameFormula`). Two cuts that merely look alike (¬P and ¬Q,
 *       distinct wires) are NOT duplicates: their read formulas carry
 *       different atom indices because the index is per-wire.
 *
 * Returns a selection for the SECOND occurrence found (id-sorted within its
 * region) — the "copy" — leaving the first as the deiteration's implicit
 * justifier (`findDeiterationEvidence` locates it structurally).
 */
export function findDuplicateToNormalize(diagram: Diagram, inner: RegionId): SubgraphSelection | null {
  const regions = Object.keys(diagram.regions)
    .filter((region) => isAncestorOrEqual(diagram, inner, region))
    .sort()
  const wireIndex = propWireIndex(diagram)
  for (const region of regions) {
    const seenAtomWires = new Map<string, string>()
    for (const nodeId of nodesIn(diagram, region)) {
      if (diagram.nodes[nodeId]!.kind !== 'atom') continue
      const wire = headWireOf(diagram, nodeId)
      if (seenAtomWires.has(wire)) return { region, regions: [], nodes: [nodeId], wires: [] }
      seenAtomWires.set(wire, nodeId)
    }
    const seenCutFormulas: { readonly formula: ReturnType<typeof readPropRegion> }[] = []
    for (const cut of childCuts(diagram, region)) {
      const formula = readPropRegion(diagram, cut, wireIndex)
      if (seenCutFormulas.some((seen) => sameFormula(seen.formula, formula))) {
        return { region, regions: [cut], nodes: [], wires: [] }
      }
      seenCutFormulas.push({ formula })
    }
  }
  return null
}

/**
 * Weighted draw without replacement until one candidate applies. Sampling is
 * CLASS-first: candidates are grouped by moveClass, a class is drawn
 * proportional to WALK_CLASS_WEIGHTS among classes that currently hold at
 * least one candidate, then a candidate is drawn uniformly within that
 * class — so a class's share of the draw never grows just because it
 * happens to have more legal candidates than another class right now. The
 * recorder auto-pins on scope-preservation refusals; any other RuleError
 * withdraws the candidate and resampling continues; non-RuleErrors are real
 * bugs and propagate.
 */
function applyWeightedRandomMove(
  recorder: PrimitiveStepRecorder,
  candidates: readonly CandidateMove[],
  rng: () => number,
): boolean {
  const byClass = new Map<MoveClass, CandidateMove[]>()
  for (const candidate of candidates) {
    const pool = byClass.get(candidate.moveClass)
    if (pool === undefined) byClass.set(candidate.moveClass, [candidate])
    else pool.push(candidate)
  }
  while (byClass.size > 0) {
    const classes = [...byClass.keys()]
    const total = classes.reduce((sum, cls) => sum + WALK_CLASS_WEIGHTS[cls], 0)
    let draw = rng() * total
    let chosenClass = classes[classes.length - 1]!
    for (const cls of classes) {
      draw -= WALK_CLASS_WEIGHTS[cls]
      if (draw < 0) {
        chosenClass = cls
        break
      }
    }
    const pool = byClass.get(chosenClass)!
    const index = Math.floor(rng() * pool.length)
    const candidate = pool.splice(index, 1)[0]!
    if (pool.length === 0) byClass.delete(chosenClass)
    try {
      recorder.record(`walk ${candidate.step.rule}`, candidate.step)
      return true
    } catch (error) {
      if (!(error instanceof RuleError)) throw error
    }
  }
  return false
}
