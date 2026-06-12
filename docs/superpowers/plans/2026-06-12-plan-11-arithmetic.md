# Plan 11: General Arithmetic Theorems (rooted-ℕ, congruence join, bare equations)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bundle five general arithmetic theorems — plusAssoc, plusLeftUnit, plusRightUnit, succShiftS, plusComm — into the Frege theory as *bare equations* (shared output lines), with the two induction theorems proved by genuine ℕ-induction. MVP-blocking per the user.

**Architecture:** Branch `plan-11-arithmetic` (already carries congruence join, 521/521 green). The canonical ℕ relation is REPLACED by rooted-ℕ (zero witness node at root) — the old encoding is vacuously true of everything and must not survive. All five derivations are already verified end-to-end by spike scripts preserved at `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/`; tasks port those constructions into `src/theories/frege.ts` and re-derive the three existing Frege theorems against the new statement.

**Tech stack:** Existing kernel + theory layer. No new dependencies.

**Executable specifications (run from project root, `npx tsx <script>`; all green as committed):**
- `conv-theorems.ts` — plusAssoc (5 steps), plusLeftUnit/plusRightUnit (3 steps each), checkTheorem green
- `rooted.ts` — bare succShift, 100 steps, wrapped milestone at 35; defines rootedNatRelation, kMat/eExtract macros, G0-porting, Cl-derivation, discharge, applied-form endgame
- `succshift-thm.ts` + `lib.ts` + `comp.ts` — parameterized module deriving succShiftS (the citable form)
- `pluscomm.ts` — self-contained: derives + checks succShiftS (100 steps) then bare plusComm (85 steps)
- `smoke.ts`, `p1.ts`, `p2.ts`, `p3.ts` — probes (conversion facts, citation-at-depth, comp instantiation, witness sharing)

**Statement-level decisions (settled with the user; do not relitigate):**
- Rooted-ℕ: `∃w0[ZERO(w0) ∧ ¬∃R[R(w0) ∧ Cl(R) ∧ ¬R(x)]]` — the ZERO node sits at ROOT on the root-scoped base line. The old natRelation (zero node inside the bubble) is vacuous; DELETE it, no dual encodings.
- Port discipline: the successor node in rooted-ℕ is `SUCC q`; fission/fusion force `q`/`q_0` names through every statement. Port names are matcher-visible statement identity.
- succShiftS lhs carries a SUCC consumer node (`SUCC q`: q@wn, out@wsn), boundary [wm, wn, wsn] — the bare-wire form is unciteable until Plan 12 fixes the matcher's bare-wire handling.
- plusComm lhs = two full rooted-ℕ with SEPARATE zero witnesses, boundary [wa, wb]; rhs adds `PLUS q q_0 —o— PLUS q_0 q` (q@wa, q_0@wb).

---

### Task 1: Derivation macro module

**Files:**
- Create: `src/theories/macros.ts`
- Test: `tests/theories/macros.test.ts`

The spike engine (`lib.ts`) contains build-time derivation helpers used by every Plan 11 derivation: a replay cursor (push step → replayProof → assert), `kMat` (K-trick materialization: conversion to `(λu.t)(s)`, fission `['arg']`, conversion back), and the live-extraction helper (extractSubgraph of a transformed copy → DiagramWithBoundary for insertion). Port these from `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/lib.ts` into `src/theories/macros.ts` with the repo's relative imports and naming conventions. These are theory-construction utilities (build-time only), exercised at boot by theory verification — they still get direct unit tests.

- [ ] **Step 1:** Write failing tests in `tests/theories/macros.test.ts`: (a) cursor pushes a doubleCutIntro and reports the updated diagram; (b) kMat materializes a closed term node at root AND inside a cut (any polarity), output on a fresh wire, K-attachment wires honored; (c) kMat with a free-port-carrying term attaches to the named existing wires. Run; observe failure (module absent).
- [ ] **Step 2:** Port the engine; run tests; observe pass.
- [ ] **Step 3:** `npx tsc --noEmit` and full `npx vitest run` green. Commit `plan 11 task 1: derivation macro module`.

### Task 2: Rooted-ℕ and re-derived zeroIsNat / succNat / oneIsNat

**Files:**
- Modify: `src/theories/frege.ts` (replace `natRelation` with the rooted form; adapt the three derivations)
- Test: `tests/theories/frege.test.ts` (existing assertions adapt; add a non-vacuity guard test)

This is the only task with real derivation work (the spike sketched but did not derive the three re-derivations). Copy `rootedNatRelation` from `comp.ts` (nz at ROOT on root-scoped w0; successor node `SUCC q`). Then re-derive, spike-first inside this task (scratch script under /tmp, observe each step, then port):
- **zeroIsNat** (`ZERO(wz) ⟹ ℕ(wz)`): per the spike sketch — the lhs root ZERO evidence serves as base witness material; insert base ATOM (open, stub→rB′, attached to wz) + closure into rB′; open-iterate the atom into cI; manufacture the second root witness via kMat + congruenceJoin merge (both primitives verified in `rooted.ts` b-phase).
- **succNat** (`ℕ(n) ⟹ ℕ(SUCC n)`): baseClAttached loses its bubble-internal ZERO (insert atom-only attached to the shared root w0; the lhs's root nz serves the rebuilt ℕ's witness). The iterated copy carries no ZEROᶜ so the old deiterate-ZEROᶜ step drops (~15 steps). Guarded-MP steps unchanged.
- **oneIsNat**: citations against the two re-derived theorems; the explicit-base-line selection rule still applies.

- [ ] **Step 1:** Write the failing non-vacuity guard test FIRST: assert the bundled ℕ relation has its ZERO node in the ROOT region with output on the base line (a structural assertion on `buildFregeTheory().relations` — this is the regression lock against the vacuous encoding). Observe it fail against current natRelation.
- [ ] **Step 2:** Replace natRelation with rootedNatRelation (delete the old body — no dual encodings). Re-derive the three theorems spike-first as above. All existing frege tests adapted to the new statements (statement shapes CHANGE; tests asserting old shapes are updated to assert the new correct shapes, never weakened).
- [ ] **Step 3:** Full suite + `npm run e2e` green (bundled theory shapes changed; E2E exercises boot). Commit `plan 11 task 2: rooted-ℕ; re-derive zeroIsNat/succNat/oneIsNat`.

### Task 3: Conversion theorems

**Files:**
- Modify: `src/theories/frege.ts`
- Test: `tests/theories/frege.test.ts`

Port `conv-theorems.ts` verbatim into three derivation functions (`derivePlusAssoc`, `derivePlusLeftUnit`, `derivePlusRightUnit`) following the deriveOnePlusOne idiom (unfold paths → applyConversion at build time → recorded certificate → folds). Exact recipes (verified): plusAssoc = unfold ['fn','fn'] + ['fn','arg','fn','fn'], convert to `app(app(PB,a), app(app(PB,b),c))` (PB = PLUS body), fold ['arg','fn','fn'] + ['fn','fn']; units = 2 unfolds + convert to bare `port('n')`.

- [ ] **Step 1:** Failing tests: each theorem present in `buildFregeTheory()`, lhs/rhs shapes (node terms, boundary arity), and the theory verifies through `loadTheory(theoryToJson(...))`.
- [ ] **Step 2:** Port; observe pass; full suite green. Commit `plan 11 task 3: plusAssoc, plusLeftUnit, plusRightUnit`.

### Task 4: succShiftS

**Files:**
- Modify: `src/theories/frege.ts`
- Test: `tests/theories/frege.test.ts`

Port the parameterized derivation from `succshift-thm.ts` (+ its comp builder from `comp.ts`) using Task 1's macros. Statement: lhs = rooted-ℕ(m) + SUCC-node (`SUCC q`: q@wn, out@wsn), boundary [wm, wn, wsn]; rhs = same + `PLUS q_0 (SUCC q)` —o— `SUCC (PLUS q_0 q)` on (wm, wn). 100 steps; the wrapped milestone (step 35) gets its own intermediate assertion in the derivation function.

- [ ] **Step 1:** Failing tests: theorem present, boundary arity 3, rhs pair shares one output wire, terms exact, theory verifies through the JSON road.
- [ ] **Step 2:** Port; observe pass; full suite green. Commit `plan 11 task 4: succShiftS by induction`.

### Task 5: plusComm

**Files:**
- Modify: `src/theories/frege.ts`
- Test: `tests/theories/frege.test.ts`

Port `pluscomm.ts` (85 steps; cites succShiftS at depth 4 — the citation requires succShiftS in the ProofContext, so derivation order inside buildFregeTheory matters: Map insertion order is dependency order). Statement: lhs = two full rooted-ℕ (separate witnesses), boundary [wa, wb]; rhs adds `PLUS q q_0` —o— `PLUS q_0 q` (q@wa, q_0@wb).

- [ ] **Step 1:** Failing tests: theorem present, rhs pair shape/wires exact, wa/wb endpoint counts 3/3, theory verifies through the JSON road (replay includes the in-proof citation).
- [ ] **Step 2:** Port; observe pass; full suite + `npm run e2e` green. Commit `plan 11 task 5: plusComm by induction, citing succShiftS`.

### Task 6: Final review and merge

- [ ] **Step 1:** Adversarial whole-branch review (inherit-model reviewer) with mutation probes, minimum set: (a) flip congruence.ts's cut-depth gate to `>=` — a soundness test must fail; (b) move rootedNatRelation's nz back into rB — the non-vacuity guard must fail; (c) drop one shared-free-port wire check in congruence — a refusal test must fail; (d) corrupt one plusComm step — theory verification must fail. Every probe observed fail → revert → pass.
- [ ] **Step 2:** Plan-doc sync (tick boxes, record deviations), full suite + E2E green, merge `plan-11-arithmetic` to main, delete branch.

---

**Deferred (recorded, not in this plan):** Plan 11b = head-stripping rule + WHNF/HNF tactic (user-approved). Plan 12 = polynomial matcher (then revisit bare-wire succShift restatement). Parameterized comprehension (flagged, awaiting user). Port-rename rule (cosmetic). Diagonal abstraction occurrences (#95).
