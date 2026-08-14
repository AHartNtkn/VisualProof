import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import { isAncestorOrEqual, polarity, wireVisibleAt } from '../kernel/diagram'
import { relSig } from '../kernel/diagram/sig'
import type { ProofStep } from '../kernel/proof'
import { applyStep, EMPTY_PROOF_CONTEXT } from '../kernel/proof'
import type { SubgraphSelection } from '../kernel/diagram'
import { bareWireAssembly, bareWireDescription, RuleError } from '../kernel/rules'
import { ScopePreservationError } from '../kernel/rules/wire-ends'
import { deiterationStep, erasureStep } from '../app/interact/moves'
import { bareWires, childCuts, nodesIn, propWires } from './diagram-scan'

export type MoveClass = 'erasure' | 'spawn' | 'doubleCut' | 'iteration' | 'vacuity'

export type CandidateMove = {
  readonly step: ProofStep
  readonly moveClass: MoveClass
}

/**
 * Enumerate the atomic propositional move alphabet on `diagram`, restricted
 * to content inside `within` (the frame region itself is never removed).
 * Atomic selections are a single atom node or a single cut with its whole
 * subtree. Gates are mirrored from the appliers; the applier remains the
 * authority — callers apply each candidate and treat a `RuleError` as the
 * candidate being withdrawn.
 */
export function enumerateMoves(
  diagram: Diagram,
  orientation: 'forward' | 'backward',
  classes: ReadonlySet<MoveClass>,
  within: RegionId = diagram.root,
): readonly CandidateMove[] {
  const out: CandidateMove[] = []
  const regions = Object.keys(diagram.regions)
    .filter((region) => isAncestorOrEqual(diagram, within, region))
    .sort()
  const atomicSelections: SubgraphSelection[] = []
  for (const region of regions) {
    for (const nodeId of nodesIn(diagram, region)) {
      if (diagram.nodes[nodeId]!.kind === 'atom') {
        atomicSelections.push({ region, regions: [], nodes: [nodeId], wires: [] })
      }
    }
    for (const cut of childCuts(diagram, region)) {
      atomicSelections.push({ region, regions: [cut], nodes: [], wires: [] })
    }
  }
  const deletionPolarity = orientation === 'forward' ? 'positive' : 'negative'
  const insertionPolarity = orientation === 'forward' ? 'negative' : 'positive'

  if (classes.has('erasure')) {
    for (const sel of atomicSelections) {
      if (polarity(diagram, sel.region) !== deletionPolarity) continue
      const step = erasureStep(diagram, sel)
      if (sel.regions.length > 0) {
        // erasureStep's rider computation (src/app/interact/moves.ts) only
        // orphans wires all of whose endpoints sit on the selection's
        // *direct* nodes (`orphanedWires(diagram, new Set(selection.nodes))`);
        // it does not walk the interior of a selected cut subtree. A
        // cut-selection (this branch: `sel.regions = [cut]`, `sel.nodes = []`)
        // can therefore hide a half-orphaned rider: a wire with one endpoint
        // deep inside the selected subtree and another endpoint outside it
        // (e.g. at the selection's own region, the wire's derived scope) is
        // invisible to that direct-nodes check, so it is never added to the
        // erasure's `wires` and never pinned. Erasing then leaves it with a
        // single end, and applyErasure correctly refuses with
        // ScopePreservationError — but that is exactly the case the auto-pin
        // bundle exists to rescue (spec, search section): consumers pin the
        // stranded wire and retry (the search's `applyCandidateWithPins`,
        // the walk's `PrimitiveStepRecorder`), so this candidate is still
        // legitimate and is emitted rather than dropped. Any other
        // RuleError here is a real gate-mirroring bug for this branch and is
        // probed and dropped; anything that isn't a RuleError at all is
        // rethrown.
        //
        // Atom-node selections (`sel.nodes = [nodeId]`, the `else` branch)
        // are exactly what `orphanedWires` handles correctly — a node's own
        // wires are checked directly — so they are verified purely by gate
        // mirroring, with no probe, so a future gate-mirroring regression
        // there still surfaces as a soundness-test failure instead of being
        // silently swallowed by this catch.
        try {
          applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
          out.push({ moveClass: 'erasure', step })
        } catch (error) {
          if (error instanceof ScopePreservationError) {
            out.push({ moveClass: 'erasure', step })
            continue
          }
          if (error instanceof RuleError) continue
          throw error
        }
      } else {
        out.push({ moveClass: 'erasure', step })
      }
    }
  }
  if (classes.has('spawn')) {
    for (const region of regions) {
      if (polarity(diagram, region) !== insertionPolarity) continue
      for (const wire of propWires(diagram)) {
        if (!wireVisibleAt(diagram, wire, region)) continue
        out.push({ moveClass: 'spawn', step: { rule: 'atomSpawn', region, wire } })
      }
    }
  }
  if (classes.has('doubleCut')) {
    for (const region of regions) {
      out.push({
        moveClass: 'doubleCut',
        step: { rule: 'doubleCutIntro', sel: { region, regions: [], nodes: [], wires: [] } },
      })
    }
    for (const sel of atomicSelections) {
      out.push({ moveClass: 'doubleCut', step: { rule: 'doubleCutIntro', sel } })
    }
    for (const region of regions) {
      // doubleCutElim removes `region` itself, so the frame is excluded; the
      // annulus must hold exactly one child cut and no nodes.
      if (region === within) continue
      if (diagram.regions[region]!.kind !== 'cut') continue
      if (childCuts(diagram, region).length !== 1) continue
      if (nodesIn(diagram, region).length !== 0) continue
      out.push({ moveClass: 'doubleCut', step: { rule: 'doubleCutElim', region } })
    }
  }
  if (classes.has('iteration')) {
    for (const sel of atomicSelections) {
      const copiedCut = sel.regions[0]
      for (const target of regions) {
        if (!isAncestorOrEqual(diagram, sel.region, target)) continue
        if (copiedCut !== undefined && isAncestorOrEqual(diagram, copiedCut, target)) continue
        out.push({ moveClass: 'iteration', step: { rule: 'iteration', sel, target } })
      }
      try {
        out.push({ moveClass: 'iteration', step: deiterationStep(diagram, sel) })
      } catch (error) {
        // No exact justifying occurrence — deiteration of this selection is
        // simply not offered. Anything else is a real bug: rethrow.
        if (!(error instanceof RuleError)) throw error
      }
    }
  }
  if (classes.has('vacuity')) {
    for (const wireId of bareWires(diagram)) {
      out.push({ moveClass: 'vacuity', step: { rule: 'vacuity', direction: 'delete', assembly: bareWireDescription(diagram, wireId) } })
    }
    for (const region of regions) {
      out.push({ moveClass: 'vacuity', step: { rule: 'vacuity', direction: 'insert', assembly: bareWireAssembly(freshWireLabel(diagram), region, relSig([])) } })
    }
  }
  return out
}

function freshWireLabel(diagram: Diagram): WireId {
  let counter = 0
  while (diagram.wires[`genw${counter}`] !== undefined || diagram.nodes[`genw${counter}_end0`] !== undefined) {
    counter += 1
  }
  return `genw${counter}`
}
