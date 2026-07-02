# Plan 11f: The Arithmetic Theorems (final — MVP-blocking)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bundle the user-demanded arithmetic sequence into the Frege theory as bare equations with FOLDED ℕ guards: plusAssoc, plusLeftUnit, plusRightUnit (conversion theorems), succShiftS and plusComm (genuine ℕ-induction). Replace the vacuous natRelation with inCutNat. Merge `plan-11-arithmetic` to main. This closes the user's MVP ruling: "without something at least this nontrivial, we cannot trust it's capable of real mathematics."

**Architecture:** Branch `plan-11-arithmetic` (final phase; HEAD b34ed34, 667/667). Every derivation already has a verified trace: conversion theorems in `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/conv-theorems.ts`; succShiftS (91 steps) and plusComm (49 steps) in `…/spike-scripts/spike4/` with full traces in the 11d plan doc's execution record. The 11e folded-guard proof (`tests/kernel/proof/folded-guard.test.ts`) established the statement pattern: theorems ship with folded `ℕ`-reference guards; derivations begin by iterating the folded ref and relUnfolding the COPY, and the ambient guard survives folded into the rhs.

**Statement-level decisions (settled with the user across Plans 11–11e; do not relitigate):**
- ℕ = inCutNat: the original natRelation with ONE token changed — the base line w0's scope moves from root to the bubble rB. The old root-scoped form is VACUOUS (∃w0 outside the cut is witnessable by a non-zero) and must not survive. The stored relation `nat` gets the inCutNat body; a structural non-vacuity guard test (the zero-evidence node and its line both INSIDE the guard structure — no top-level witness) is written FIRST and locks the encoding.
- Successor node in the relation body is `SUCC q`-shaped (post-11c the name canonicalizes to s0 — build with any name; the port discipline is dead).
- Bundled statements use FOLDED guards: succShiftS lhs = ref `nat`(m-line) ∧ SUCC-consumer node (boundary [wm, wn, wsn]); plusComm lhs = ref `nat`(a-line) ∧ ref `nat`(b-line) (boundary [wa, wb]); rhs in each = lhs + the applied equality pair on a shared output line. Guard-producing theorems (zeroIsNat, succNat, oneIsNat) END with a relFold so their statements are folded too.
- Conversion theorems are unguarded (their equations hold for arbitrary terms by βη) — statements unchanged from the verified specs.

---

### Task 1: inCutNat + non-vacuity guard + re-derived zeroIsNat / succNat / oneIsNat

**Files:** `src/theories/frege.ts` (natRelation body → inCutNat; the three derivations re-worked), `tests/theories/frege.test.ts`.

Spike-first INSIDE the task (scratch under /tmp, observe every step, then port): the derivations change for two reasons at once — the encoding fix (copies carry their zero line internally; the old severing/zero-deiteration steps drop per the spike3/spike4 lessons in the memory file and the 11d execution record) and the folded statements (each theorem's ℕ-producing side ends with `relFold`; each ℕ-consuming side starts by iterating the folded ref and relUnfolding the copy).
- **Guard test FIRST** (observed failing against the current vacuous body): the bundled `nat` relation's zero-evidence node lies strictly INSIDE the guard structure (not a child of the body root) and its line's scope is NOT the body root.
- zeroIsNat: `ZERO-evidence(wz) ⟹ folded nat(wz)` — derive the unfolded guard around wz (the lhs evidence is base-witness material; the kernel now has closedTermIntro + congruenceJoin for the manufacture steps), then relFold it.
- succNat: `folded nat(wn) ⟹ folded nat(wn) ∧ folded nat(w_{Sn})` shape per the existing statement's intent — unfold the iterated copy, run the (now shorter) dance, relFold the produced guard.
- oneIsNat: citations against the two re-derived theorems; folded refs make the citation matches exact.

- [ ] Guard test observed failing → inCutNat lands → guard test green; three theorems re-derived (each spike-first, refusals reported not papered over); all existing frege tests updated to the new statements; full suite + `npm run e2e` green (boot bundles these). Commit `plan 11f task 1: inCutNat; zeroIsNat/succNat/oneIsNat with folded guards`.

### Task 2: Conversion theorems

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Port `conv-theorems.ts` verbatim (verified recipes: plusAssoc = unfold ['fn','fn'] + ['fn','arg','fn','fn'], convert to the constant-free unfolded target built with app()/port(), fold ['arg','fn','fn'] then ['fn','fn']; units = 2 unfolds + convert to the bare variable) into `derivePlusAssoc`, `derivePlusLeftUnit`, `derivePlusRightUnit`, following the deriveOnePlusOne idiom.

- [ ] Failing presence/shape/verify tests → port → pass; full suite green. Commit `plan 11f task 2: plusAssoc, plusLeftUnit, plusRightUnit`.

### Task 3: succShiftS

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Adapt `spike4/succshift4.ts` (91 steps, trace in the 11d record) to the folded statement: prelude D0 = iterate the folded ref + relUnfold the copy (replacing the old iterate-guard-cut opening), then the trace as verified; lhs keeps the SUCC consumer (boundary [wm, wn, wsn]). Spike-first in scratch (the ids and one or two step shapes shift under the prelude), then port using the Task-1-era macros (`DerivationCursor`, `intro`, eExtract-style sequences as local helpers in frege.ts if not already shared).

- [ ] Spike adaptation observed green (checkTheorem) → ported → theorem present, boundary arity 3, rhs pair exact, theory verifies through the JSON road; full suite green. Commit `plan 11f task 3: succShiftS by induction (folded guard)`.

### Task 4: plusComm

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Adapt `spike4/pluscomm4.ts` (49 steps): lhs = two folded refs (boundary [wa, wb]); prelude unfolds only the A-side copy for the bubble instantiation; the FLAT parameterized comp (`PLUS x b̂ ⊸ PLUS b̂ x`, attachments [wb]) as verified; the succShiftS citation site assembles its occurrence from the AMBIENT folded b-ref (iterate it folded) + closedTermIntro SUCC — the folded lhs of Task 3's theorem should match directly. Derivation order in buildFregeTheory matters (Map insertion order is dependency order — succShiftS before plusComm).

- [ ] Spike adaptation observed green → ported → theorem present, rhs audit (two PLUS nodes sharing one output on wa/wb, zero other root nodes), theory verifies through JSON; full suite + e2e green. Commit `plan 11f task 4: plusComm by induction, citing succShiftS (folded guards)`.

### Task 5: Final review and merge

- [ ] Whole-branch adversarial review (independent agent) with mutation probes, minimum: (a) revert inCutNat's scope token — the non-vacuity guard must fail; (b) corrupt one step in each induction theorem — theory verification must fail; (c) swap plusComm's rhs pair wiring (q↔q_0 on one node) — a statement-shape test must fail; (d) re-run every prior review battery (congruence, headstrip, intro, comprehension params, ref/reldef) untouched-green. Every probe observed fail → revert → pass.
- [ ] Render sanity: the render harness (`render-thm.html/.ts`, scratch) pointed at the bundled plusComm — the lhs must show exactly two labeled ℕ lenses on the sheet and nothing else. Screenshot for the user.
- [ ] Plan-doc sync (this doc + ticking the remaining queue references), full suite + E2E green, **merge `plan-11-arithmetic` to main**, delete branch. Commit/merge messages per house convention.
