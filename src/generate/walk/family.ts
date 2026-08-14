import { EMPTY_PROOF_CONTEXT, checkTheorem } from '../../kernel/proof'
import { isAncestorOrEqual, mkDiagramWithBoundary } from '../../kernel/diagram'
import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import { relSig } from '../../kernel/diagram/sig'
import { bareWireAssembly, bareWireDescription, RuleError } from '../../kernel/rules'
import { emptyGraph, finishDiagramWithBoundary } from '../../theories/graph'
import { PrimitiveStepRecorder, onlyNewCut } from '../../theories/record'
import { bareWires, childCuts, nodesIn } from '../diagram-scan'
import { readKnobs, type GeneratedProblem, type GeneratorFamily } from '../index'
import { atomName, containsDoubleNegation, printTheorem, usedAtoms } from '../prop/formula'
import { isMinimalTautology } from '../prop/shrink'
import { readPropTheorem } from '../prop/read'
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
  // ¬¬ repair: eliminate every empty-annulus double-cut pair strictly
  // inside the body (the shell's own intrinsic pair, at 'inner' itself, is
  // excluded — unwrapping it is not part of this cleanup). doubleCutElim is
  // an ungated equivalence, so this never changes what the derivation
  // certifies, only its presentation.
  for (
    let target = findDoubleCutToNormalize(recorder.diagram, inner);
    target !== null;
    target = findDoubleCutToNormalize(recorder.diagram, inner)
  ) {
    recorder.record('normalize double cut', { rule: 'doubleCutElim', region: target })
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
  return { diagram, statement: printTheorem(reading.formula), walkUpperBound: recorder.actions.length }
}

/**
 * Find a cut region strictly inside `inner` (the body) whose annulus is
 * empty (exactly one child cut, no nodes) — the shape doubleCutElim
 * removes. `inner` itself is excluded: it and its ¬-headed body are the
 * shell's own intrinsic double-cut pair, not walk-introduced junk.
 */
function findDoubleCutToNormalize(diagram: Diagram, inner: RegionId): RegionId | null {
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
