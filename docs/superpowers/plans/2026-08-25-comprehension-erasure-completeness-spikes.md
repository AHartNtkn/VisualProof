# Comprehension and Erasure Completeness Spikes Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run production-shaped proof spikes that either establish the selected completeness architecture or identify its first precise false premise.

**Architecture:** Keep identity-boundary normalization, generalize structural induction to arbitrary inherited wires, and implement each compound constructor with one instantiation-evidence traversal whose generated endpoints are connected by isomorphism. Constructor theorems own all real validity and support work.

**Tech Stack:** Lean 4, Lake, VisualProof diagram/rule kernel.

**Spec:** `docs/superpowers/specs/2026-08-25-comprehension-erasure-completeness-spikes.md`

## Global Constraints

- Every spike is an owning production theorem; no synthetic test theorem or fixture is allowed.
- No new quotient, compiler datatype, derived relation, checker, or alternate proof authority.
- Use `RegionIso`/`OpenDiagramIso` for presentation and actual Step rules for non-isomorphic changes.
- Exactly one authoritative instantiation-evidence traversal per compound constructor.
- Every helper lands with an immediate production-theorem caller.
- No completeness source file may exceed 3,000 lines; split by one theorem responsibility before that boundary.
- Commit each GREEN task after its narrow check and `lake build` pass.

---

### Task 1: Generalized Structural Skeleton

**Files:**
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/Complete.lean`
- Modify or create focused Region-local theorem module under `VisualProof/Rule/Completeness/Comprehension/Structural/`

**Interfaces:**
- Consumes: existing generalized Atom, Identity, and Blank `SupportDerives` theorems.
- Produces: unrestricted mutual recursion motives and production statement `supportRegionDerives`.

- [x] State generalized Cut, Parallel, and Region constructor production theorems with `sorry` only in those owning theorem proofs.
- [x] Change all three mutual recursion motives to `SupportDerives` at arbitrary inherited wire contexts.
- [x] Make the `Region.mk` callback consume the generalized ItemSeq induction hypothesis through `supportRegionDerives`.
- [x] Confirm the recursion elaborates without a boundary-wire case.
- [x] Run `lake env lean VisualProof/Rule/Completeness/Comprehension/Structural/Complete.lean` and record the exact pass/fail classification.
- [x] Commit the GREEN structural skeleton.

### Task 2: Generalized Cut

**Files:**
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/Cut.lean`
- Reuse: `VisualProof/Rule/Completeness/Comprehension/Structural/Hosted.lean`
- Reuse: `VisualProof/Rule/Completeness/Comprehension/Telescope.lean`

**Interfaces:**
- Consumes: `SupportDerives body`, existing identity-boundary normalization, CutShape, `supportCutInstantiatedHosted`, and iso transport.
- Produces: `supportCutDerives` for arbitrary `body : Region wires` with no `wires = []` premise.

- [x] Put generalized `supportCutDerives` in RED with its final production statement.
- [x] Prove one Prop-valued mutual Cut factor theorem over the authoritative instantiation evidence, jointly returning edit, child evidence, validity, and endpoint isomorphisms.
- [x] Close selected-atom and nested-cut cases without inverse renaming, a second site traversal, endpoint uniqueness, or exact fresh-name equality.
- [x] Consume the factor and child induction hypothesis in generalized `supportCutDerives`.
- [x] Run `lake env lean VisualProof/Rule/Completeness/Comprehension/Structural/Cut.lean`, then `lake build`.
- [x] Record whether any failure was presentation, validity, evidence insufficiency, support, or roster related; correct only that cause and rerun.
- [x] Commit generalized Cut GREEN.

### Task 3: Generalized Parallel

**Files:**
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/Parallel.lean`
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/ParallelDerives.lean`

**Interfaces:**
- Consumes: head and tail `SupportDerives`, ParallelShape, Vacuity, and iso-aware telescope composition.
- Produces: `supportParallelDerives` at arbitrary inherited wires.

- [x] Put generalized `supportParallelDerives` in RED with no empty-wire premises.
- [x] Prove one Prop-valued factor traversal that returns the Parallel edit and both child instantiation witnesses together.
- [x] Handle the head-only boundary-wire support case with a real constructor-local Vacuity reconciliation.
- [x] Compose head and tail induction hypotheses with binder and conjunction presentation only up to isomorphism.
- [x] Run the narrow Lean checks for both Parallel modules, then `lake build`.
- [x] Record the exact result and commit generalized Parallel GREEN.

### Task 4: Generalized Arity and Region Locals

**Files:**
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/Arity.lean`
- Modify the focused Region-local theorem module from Task 1.

**Interfaces:**
- Consumes: child `SupportDerives`, Arity, Vacuity/hosted support, and typed context isomorphisms.
- Produces: generalized one-local Arity and GREEN `supportRegionDerives`.

- [x] Generalize the exposed-material canonicality and presentation lemmas from empty arguments to arbitrary `arguments`.
- [x] Put generalized `supportArityDerives` in RED.
- [x] Prove one selected-site factor that owns the Arity edit, child evidence, unary support pin, validity, and endpoint isomorphism.
- [x] Prove `supportRegionDerives` by folding locals from the ItemSeq induction hypothesis.
- [x] Run the narrow Lean checks for Arity and Region support, then `lake build`.
- [x] Record the exact result and commit generalized Arity/Region GREEN.

### Task 5: Structural and Comprehension Completion

**Files:**
- Modify: `VisualProof/Rule/Completeness/Comprehension/Structural/Complete.lean`
- Modify: `VisualProof/Rule/Completeness/Comprehension/Complete.lean`
- Modify: `VisualProof/Rule/Completeness/Comprehension.lean` only if public composition requires it.

**Interfaces:**
- Consumes: all generalized structural constructor theorems and existing normalization.
- Produces: GREEN `supportPatternDerives` and `Comprehension.complete`.

- [x] Replace every remaining constructor `sorry` in the structural recursion with its GREEN theorem.
- [x] Close `supportPatternDerives` by pure syntax-constructor dispatch.
- [x] Close internal and public Comprehension completeness from normalization plus structural derivation.
- [x] Run narrow checks, `lake build`, and the repository command-line axiom check.
- [x] Record the result and commit Comprehension completeness GREEN.

### Task 6: Erasure Reduction Spikes

**Files:**
- Modify or create focused modules under `VisualProof/Rule/Completeness/Erasure/`
- Modify the public Erasure completeness module only when the production composition is ready.

**Interfaces:**
- Consumes: `Exposure.equates`, Iteration, `Comprehension.complete`, guarded Ends absorption, and iso transport.
- Produces: verified duplication, two-site instantiation, guarded absorption, and ultimately Erasure completeness.

- [ ] Prove the exact Iteration freshening/pin-residue theorem needed by the exposed block.
- [ ] Prove one Iteration step reaches an endpoint isomorphic to two suitable instantiation blocks.
- [ ] Construct the two-site `Instantiates` witness and its quantified-region canonicality.
- [ ] Construct the positive `Ends.Absorb.ItemsGuard` and absorption step at binder-home depth.
- [ ] Compose exposure, Iteration, Comprehension, Ends, and endpoint isomorphism into `Relation.TransGen Step`.
- [ ] Run narrow checks, `lake build`, and the repository command-line axiom check.
- [ ] Record the result and commit Erasure completeness GREEN.
