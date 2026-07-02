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

- [x] **MODIFIED (see execution record + memory UPDATE 10):** Guard test observed failing → inCutNat lands → guard test green. The three guard-producing theorems (zeroIsNat/succNat/oneIsNat) were NOT re-derived: they were proven UNDERIVABLE against inCutNat (producing a non-vacuous guard requires pinning the internal existential zero-witness to the external argument line, and every kernel mechanism lifts the base wire to root scope — the vacuity inCutNat forbids). They were DELETED as vacuous-only, not re-derived; the user ruled descope-and-ship (Tasks 2–4 take ℕ as hypothesis, unaffected). Citations retargeted to onePlusOne; full suite + `npm run e2e` green. Commit `plan 11f task 1 (modified)` 72544f7.

### Task 2: Conversion theorems

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Port `conv-theorems.ts` verbatim (verified recipes: plusAssoc = unfold ['fn','fn'] + ['fn','arg','fn','fn'], convert to the constant-free unfolded target built with app()/port(), fold ['arg','fn','fn'] then ['fn','fn']; units = 2 unfolds + convert to the bare variable) into `derivePlusAssoc`, `derivePlusLeftUnit`, `derivePlusRightUnit`, following the deriveOnePlusOne idiom.

- [x] Failing presence/shape/verify tests → port → pass; full suite green. Commit `plan 11f task 2: plusAssoc, plusLeftUnit, plusRightUnit` 78db234.

### Task 3: succShiftS

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Adapt `spike4/succshift4.ts` (91 steps, trace in the 11d record) to the folded statement: prelude D0 = iterate the folded ref + relUnfold the copy (replacing the old iterate-guard-cut opening), then the trace as verified; lhs keeps the SUCC consumer (boundary [wm, wn, wsn]). Spike-first in scratch (the ids and one or two step shapes shift under the prelude), then port using the Task-1-era macros (`DerivationCursor`, `intro`, eExtract-style sequences as local helpers in frege.ts if not already shared).

- [x] Spike adaptation observed green (checkTheorem) → ported → theorem present, boundary arity 3, rhs pair exact, theory verifies through the JSON road; full suite green. Commit `plan 11f task 3: succShiftS by induction (folded guard)` 99239e7 (92 steps).

### Task 4: plusComm

**Files:** `src/theories/frege.ts`, `tests/theories/frege.test.ts`.

Adapt `spike4/pluscomm4.ts` (49 steps): lhs = two folded refs (boundary [wa, wb]); prelude unfolds only the A-side copy for the bubble instantiation; the FLAT parameterized comp (`PLUS x b̂ ⊸ PLUS b̂ x`, attachments [wb]) as verified; the succShiftS citation site assembles its occurrence from the AMBIENT folded b-ref (iterate it folded) + closedTermIntro SUCC — the folded lhs of Task 3's theorem should match directly. Derivation order in buildFregeTheory matters (Map insertion order is dependency order — succShiftS before plusComm).

- [x] Spike adaptation observed green → ported → theorem present, rhs audit (two PLUS nodes sharing one output on wa/wb, zero other root nodes), theory verifies through JSON; full suite + e2e green. Commit `plan 11f task 4: plusComm by induction, citing succShiftS (folded guards)` 594d0e3 (50 steps).

### Task 5: Final review and merge

- [x] Whole-branch adversarial review (independent agent) with mutation probes — all four mandated probes observed fail → revert → pass; two additional statement-adequacy pins added (defect protocol). See execution record. Commit `plan 11f task 5: review battery additions` c90a93a; record `plan 11f: task 5 review record`.
- [ ] Render sanity: the render harness (`render-thm.html/.ts`, scratch) pointed at the bundled plusComm — the lhs must show exactly two labeled ℕ lenses on the sheet and nothing else. Screenshot for the user. **(team lead — not in independent-reviewer scope)**
- [ ] Plan-doc sync (this doc + ticking the remaining queue references), full suite + E2E green, **merge `plan-11-arithmetic` to main**, delete branch. Commit/merge messages per house convention. **(merge is the team lead's after verdict; plan-doc sync done here.)**

---

## Execution record — Task 5 final review (independent reviewer, 2026-07-02)

**Baseline observed:** HEAD 594d0e3, suite 670/670, tsc clean, e2e 3/3. Reviewer wrote none of the reviewed code.

### PART A — mutation probes (each: mutate → observe ≥1 fail → revert → observe pass)

| # | Mutation | Result | Caught by |
|---|----------|--------|-----------|
| 1 | `natRelation` base zero-line scope rB → root (revert the inCutNat one-token fix) | FAIL (9 frege tests) | `the bundled ℕ is inCutNat: zero-evidence inside the guard` — assertion (b) w0.scope ≠ root fails directly; also cascades the derivations |
| 2 | succShiftS final `e2 convert A1` target `PLUS s0 (SUCC s1)` → `PLUS s1 (SUCC s0)` | FAIL loudly at build/verify | step `e2 convert A1` (conversion): `… and 'PLUS s1 (SUCC s0)' are not βη-convertible` |
| 3 | plusComm `t6 left-shift` target args swapped (`s0,s1` → `s1,s0`) | FAIL loudly at build/verify | step `t6 left-shift` (conversion): not βη-convertible |
| 4 | plusComm `buildComp4` rhs pair wiring uncrossed (both nodes `PLUS x b̂`) | FAIL | derivation crashes at `nodeOnWire` (`no 's1'-on-'w0_0' node`) — see FINDING F1 |
| 5 | (none) re-run all prior review batteries untouched | PASS | congruence, headstrip, intro, comprehension-instantiate/abstract, ref-node, reldef, reldef-review, canonical-ports, polarity-matrix, equational-gates — full suite 670/670 |

All mutations fully reverted; `git diff src/` empty after Part A.

### PART B — findings and the added pins

**F1 (statement adequacy, plusComm rhs — the probe-4 gap made concrete).** The probe-4 mutation crashes the *derivation* (an incidental `nodeOnWire` guard), but the plusComm *statement-shape* test did NOT pin the crossing: a trivial reflexive `PLUS a b —o— PLUS a b` (two `PLUS s0 s1` nodes, shared output, boundary 2, two folded refs) passes every prior assertion. Verified with a synthetic uncrossed rhs: current assertions `{twoPairs, twoRootTerms, sharedOutput}` all true, i.e. reflexivity would certify as commutativity. **Fix:** crossing pin — the two nodes' `(s0-wire, s1-wire)` signatures must be exactly `{(wa, wb), (wb, wa)}`. Observed failing against the reflexive shape (synthetic) and against an in-harness flipped expectation (real rhs is `{w0,w1 ; w1,w0}`), passing clean.

**F2 (statement adequacy, succShiftS rhs — same class).** The two `has(...)` checks confirm the terms exist but not that they assert an *equality*: a variant with the two terms on unrelated output lines would pass. **Fix:** equality pin — the pair shares one output wire, and both nodes' m/n args ride `wm/wn`. Observed failing against an in-harness `.not.toBe` flip (the two genuinely share `r0_intro_fis_fis`), passing clean.

**Additional pins (same class, cheap closure):** plusComm lhs has zero root term nodes (hypothesis is exactly ℕ(a) ∧ ℕ(b)); nat body's only root-scoped wire is the boundary x-line (semantic non-vacuity beyond the structural guard). All in commit c90a93a.

**Confirmed adequate (no change needed):**
- Statement reads. plusComm lhs = two folded `nat` refs on distinct boundary lines, nothing else (2 nodes total). succShiftS lhs = folded `nat`(wm) + SUCC-consumer `SUCC s0` (s0=wn, out=wsn) = "nat(m) and a successor witness for n". succShiftS rhs pair = `PLUS m (SUCC n)` —o— `SUCC (PLUS m n)`, s0=wm s1=wn, shared output. plusComm rhs = crossed pair on shared output. Conversion theorems' lhs/rhs terms pinned by `soleTerm`.
- Folded guards. rhs ref-count pins (2 for plusComm, 1 for succShiftS) confirm the guards stay folded — a fully-unfolded rhs carries no ref node.
- Deleted theorems. `grep` for zeroIsNat/succNat/oneIsNat across src/tests/e2e = clean; only the plan-doc Task-1 description (historical) mentions them.
- Derivation hygiene (frege.ts). No console/TODO/debug; helpers `kOpen`/`eExtract`/`nodeOnWire`/`buildComp4` all used; `.find(...)!` and `nodeOnWire` throw loudly on absence; canonical port names (s0,s1,s2) and K-trick binder names (a,r,f,n,y) are construction inputs only, never read as semantic identity.
- checkTheorem per-step boundary survival. `checkTheorem` runs `replayProof(..., onStep)` asserting every lhs boundary wire survives after each step (theorem.ts:53–59); the frege derivations verify through `verifyTheory → checkTheorem` (store.ts:74); no bypass introduced.

**Final counts:** suite 670/670, tsc exit 0, e2e 3/3. `git diff src/` empty (all probes reverted); only `tests/theories/frege.test.ts` changed (the four pins, c90a93a).

**Verdict: ISSUES-FIXED-APPROVED.** The theorem layer is sound (checkTheorem pins every rhs against the replayed derivation); the two statement-adequacy gaps were test-only (they could not have shipped a false theorem, since checkTheorem forces the stored rhs to equal the derived diagram, but they left the door open to a *future* trivial theorem being mislabeled). Both are now pinned. DO NOT MERGE performed — merge left to the team lead.
