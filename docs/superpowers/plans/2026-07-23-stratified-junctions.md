# Stratified Junctions — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development task-by-task. Steps use checkbox (`- [ ]`) syntax.

**Goal:** Replace the junction subsystem with the accepted stratified-space model: wire state = (T, b, τ) on X, crossings via canonical φ under the ordinary gate, zero auxiliary mechanisms.

**Contracts:** `docs/superpowers/specs/2026-07-23-junction-problem-statement.md` (§1.5 formal statement, §6 acceptance, §7 boundary) and `2026-07-23-phi-construction.md` (canonical φ, corridor Lemma 1′, step-on-X pseudocode, §6 inventory). Physics corpus binds throughout; paradigm frozen.

**Architecture:** State refactor first (topology as stored coordinate), then the sweep extension (ℓ_e ≥ 0 boundary + φ crossing), then deletions, then the re-derived tests, then the two front-loaded empirical verifications (crossing timescale; mid-transition looks → user).

## Global Constraints

- Strict descent untouched in meaning: every accepted move strictly lowers total E; no triggers/throttles/repair moves/carry policies — mechanism-count zero, audited at review.
- The elastica leg solver, its caches, barrier/clearance energies, and all law tests are load-bearing: keep verbatim/green.
- Explicit-path staging; full `npm run test:all` + tsc 0 at each task boundary (physics suite included from Task 3 on; Tasks 1–2 file-local + owned-set, `tsc-errors: N` recorded).
- No commits to `examples/*.json`; the untracked gallery script stays untracked.

---

### Task 1: Wire junction state = (T, b, τ)

**Files:** `src/view/engine.ts` (wire structure: explicit topology T — adjacency as stored data; branch positions; per-half-edge tangent angles; `mkEngine` seeds via soaptree, birth-only), `src/view/wires.ts`, carryOver (`engine.ts:456-473` era): carry T explicitly for surviving wires (keyed on wire identity, not branch count — kills diagnosed cause (a) structurally). Tests: engine/wires suites adapt; a new carry test: rebuild after a rewrite preserves T (the revised repro (a) from `junction-app-path.test.ts` goes green here or in Task 4).
- [ ] TDD per house rules; file-local green; commit `feat: junction state as (T,b,tau)`.

### Task 2: step on X — the boundary and the crossing

**Files:** `src/view/relax.ts` — per the φ doc's pseudocode: branch-DOF proposals respect ℓ_e ≥ 0 as feasible projection; a proposal driving through zero maps via φ (identity on intrinsic face data; re-expansion along the re-paired edge) and is evaluated under the same gate; deterministic DOF order resolves deep-face ties; fixed-point stop unchanged (a crossing is an ordinary accepted move).
- [ ] Unit tests: a hand-built two-topology fixture crosses when E decreases and refuses when it doesn't; drawing at the crossing sweep identical before/after at the crossing wire (Lemma 2's testable form); determinism (same trajectory bit-identical, cache on/off).
- [ ] Commit `feat: gated descent across strata via canonical phi`.

### Task 3: Deletions

**Files:** remove NNI machinery (`tryTopologyMove`, `nniAlternatives`, edge-trigger, `deferMoved`, `refaceCandidateNodes`), `reseedUnrepresentableBranches` (subsumed per φ doc — VERIFY by keeping `relax.test.ts` "no leg wraps" green on the frege fixtures; if it goes red, STOP and report: the subsumption claim fails empirically and the seeding question returns to the user), stored-adjacency rebuild paths. Grep gates: no trunk/NNI/trigger residue.
- [ ] Full suite green from here (physics included). Commit `refactor: delete discrete topology machinery`.

### Task 4: Acceptance tests re-derived (problem statement §6)

**Files:** rewrite `tests/physics/junction-app-path.test.ts`: (1) trajectory continuity — scripted drags incl. teleport, per-frame drawn displacement ≤ accepted DOF motion bound; crossing frames' drawings equal at the crossing wire up to solver resolution; (2) interactive restructuring — the rectangle drag crosses through ℓ_e = 0 and ends re-paired (asserting the passage, not optimality); (3) carry (Task 1's); (4) within-basin freedom — the bar tangent reaches its conditional optimum (0.419-rad target from the diagnosis); drop the cross-basin warm-vs-fresh repro. `junctions.test.ts` energy-law assertions adapt to the new state; all existing law tests stay green.
- [ ] Commit `test: stratified-junction acceptance per accepted semantics`.

### Task 5: Front-loaded empirical verification (the two named risks)

- [ ] **Timescale:** instrument (scratch, reverted) drag scenarios at app cadence; measure sweeps-to-crossing from boundary contact on rect4/bar5; report numbers.
- [ ] **Mid-transition looks:** render drag sequences (the gallery mechanism) spanning a full merge-pass-re-expand on rect4 and bar5 — deliver frames for the USER's visual ruling. No aesthetic test is written (ruled 2026-07-23); the frames are the deliverable.
- [ ] Full gates; whole-branch SDD review; ledger updated. STOP for the user's visual ruling before any polish.

## Verification

`npm run test:all` + tsc 0 + physics suite green; the four §6 acceptance tests green; mechanism-count audit at review = zero; the user's mid-transition ruling is the final gate.
