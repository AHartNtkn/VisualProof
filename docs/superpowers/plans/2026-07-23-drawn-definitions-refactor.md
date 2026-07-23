# Drawn Definitions Refactor — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Delete the body-node mechanism and all comprehension/substitution machinery built on it; implement drawn definitions (spec `2026-07-23-drawn-definitions-design.md`): comprehension intro/elim, relational congruence join, derived swaps, and the Eq library layer — with frege replaying green as the conservativity gauntlet.

**Architecture:** Kernel-first sweep in the pattern of the sig-wires plan: new rules land before deletions so replacements exist; the body kind then deletes across diagram/canonical/subgraph/codec/view; the comprehension UX subsystem (workspace/transactions/matches) deletes outright (its successor gestures are a later plan, gated on pending user rulings); frege and the macro conservativity suite are recast onto the new primitives; step-tag tables reconcile TS↔Lean.

**Tech stack:** TypeScript 5.5, Vitest 2; one Lean file touched (`Correspondence/StepTags.lean` + its count lemmas in `Rule/Step.lean`) — the full Lean rearchitecture remains Plan 2.

**Grounding inventory:** the deletion-surface survey (in-session, 2026-07-23): 27 src files + 39 test files touch the dying surface; per-file cites are reproduced in the task briefs below.

## Global Constraints

- Terminology: "atoms" never "application nodes"; derived swaps never "β"; the K constraint is "definition" or "constraint", never "body".
- No comprehension-specific machinery outside `comprehension.ts`'s two rules; convenience lives in the library (Eq lemmas + citation), never kernel rules.
- Explicit-path git staging only. Full `npm run test:all` + `npx tsc --noEmit` green at every task boundary from Task 5 onward (Tasks 1–4 gate file-locally + owned-set tsc, Plan-1 amended-gate style, recording `tsc-errors: N`).
- `npm run formal:tags` (TS↔Lean step-tag agreement) becomes part of the gate from Task 3 onward and must be GREEN at plan end — it is currently latently red.
- The bare vacuous intro/elim branch, iteration, wire-join, erasure, congruence-at-ι, matcher/exploreForm/citation machinery are load-bearing and must not regress.
- `examples/` regeneration churn: do not stage `examples/*.json` (Fix-6 hygiene handles them separately).

---

### Task 1: K-shape module + comprehension intro/elim

**Files:** Create `src/kernel/rules/comprehension.ts`, `tests/kernel/rules/comprehension.test.ts`.
**Interfaces — Produces:**
- `buildK(scope, sig, G: DiagramWithBoundary, params: readonly WireId[])` → the drawn K(R,G) fragment (outer cut, ∀x⃗ wires of sorts sig.args, two implication cut-pairs, R-atoms, two content copies spliced via `spliceSubgraphMapped`), returned as diagram-parts for intro.
- `applyComprehensionIntro(d, scope, sig, G, params, reservation?)` — fresh wire + drawn K, ANY polarity; params land on wires scoped at-or-outside (mkDiagram scope law is the gate).
- `recognizeK(d, wireId)` → certificate `{skeleton, gPlus, gMinus}` or refusal: cut-skeleton walk + boundary-pinned `exploreForm(gPlus) === exploreForm(gMinus)`.
- `applyComprehensionElim(d, wireId)` — requires tautological state: wire's only endpoints are its own K's two R-atom heads AND `recognizeK` passes; removes wire + K.
- [ ] Failing tests: intro at positive AND negative scope for rel() (blank G — the ∃P.P axiom form) and rel(ι,ι) with a param; elim round-trip restoring `exploreForm`; elim refusal when an extra atom rides the wire; elim refusal on drifted K (one copy double-cut-wrapped — the K-drift diagnostic case); param scope gate via mkDiagram.
- [ ] Implement; file-local green; owned tsc clean; commit `feat: comprehension intro/elim over drawn K`.

### Task 2: relational congruence join

**Files:** Extend `src/kernel/rules/congruence.ts` (or sibling `congruence-rel.ts` if the ι/rel split reads cleaner — follow the file's own structure), tests.
**Interfaces — Produces:** `applyRelCongruenceJoin(d, a, b, correspondence)` — two constrained wires of one sig; both `recognizeK` (Task 1); contents match under boundary correspondence (x⃗ positional, params on identical host wires — rule-9's shared-free-port condition verbatim); certificate = boundary-pinned `exploreForm` equality; cut-depth gate = rule-9's (congruence.ts:67-74 pattern); merge polarity-free; then deiterate the redundant K on the same certificate (single call → both effects, per spec).
- [ ] Failing tests: identical-content join discharges polarity-free (both parities); double-cut-variant contents REFUSE here (α-only rule) — then pass after in-place DC-elim inside one K (the worked spec §2.6 sequence as a test); mismatched params refuse; unconstrained wire falls through to ordinary wireJoin (untouched).
- [ ] Implement; green; commit `feat: relational congruence join (rule 9 at rel sigs)`.

### Task 3: step kinds + codecs + Lean tag reconciliation

**Files:** `src/kernel/proof/step.ts`, `proof/json.ts`, `proof/compose.ts`; `VisualProof/Correspondence/StepTags.lean` + count lemmas in `VisualProof/Rule/Step.lean`; `tests/kernel/proof/json.test.ts` etc.
- Add kinds `comprehensionIntro {scope, sig, content, params}`, `comprehensionElim {wireId}`, `relCongruenceJoin {a, b, correspondence}`; remove `bodyAttach`, `bodyDetach`, `unfold`, `fold`, and `vacuousIntro.body` (codec sites proof/json.ts:297-315,427-449; compose.ts:120-148). Dispatch to Task-1/2 rules.
- Lean: replace tags `comprehensionInstantiate/comprehensionAbstract/relUnfold/relFold` with the three new names; update `serializedAll_length` and the `all`/`all_nodup` lemmas (mechanical; statements only — Plan 2 proves soundness).
- [ ] Round-trip tests for the three new kinds (incl. content payload); decoding any dead kind fails loudly; `npm run formal:tags` GREEN (first time ever on this branch — record that in the commit body).
- [ ] Commit `feat: primitive comprehension steps; reconcile TS-Lean step tags`.

### Task 4: delete the body kind + dying rules

**Files (from the survey, all cites current at ad01c8d):** delete `src/kernel/rules/body.ts`, `src/kernel/rules/fold.ts` (move `diagonalize` to `src/kernel/diagram/subgraph/diagonalize.ts` — its only surviving consumer is `abstraction-matches.ts:6,186`, dying in Task 6; if nothing else imports it after Task 6, delete it then); strip `'body'` arms from `diagram.ts` (:30,98,137,147,191,358-383), `diagram/json.ts` (:26,177-180), `builder.ts` (:59), `canonical/explore.ts` (:124,183), `subgraph/{splice:171,extract:50,match:66,279-280}.ts`, `rules/doublecut.ts:17`, `rules/vacuous.ts` bodied branch (:16-19,44-61 body?,88-101) keeping bare intact, `rules/index.ts` exports.
- [ ] Tests: delete `body.test.ts`, `fold.test.ts`; strip bodied cases from `vacuous.test.ts` (:128-191) keeping bare cases (:63-97); kernel-diagram suites lose body-kind cases with inline no-successor comments where a scenario has no K-analogue, K-analogue tests otherwise (the wellformed body checks become K-shape tests → point to Task 1's suite).
- [ ] Gate: owned tsc clean; kernel suites green except knowingly-broken downstream (recorded count).
- [ ] Commit `refactor: delete body node kind and carrier rules`.

### Task 5: view + app mechanical strip; comprehension UX subsystem deletion

**Files:** view arms `engine.ts` (:38,102,188,207,401), `wires.ts` (:32,70), `paint.ts` (:200,242,269), `relax.ts` (:1499,1517), `app/hittest.ts` (:191,207,211), `app/edit.ts:31`, `interact/viewport.ts` (:292,303), `copy-planner.ts:518` + `'workspace'` destination machinery. DELETE OUTRIGHT (fix-list Fix 4, ratified): `relation-workspace.ts`, `relation-workspace-draft.ts`, `relation-transactions.ts`, `abstraction-matches.ts`, `interaction/named-relation.ts` (its `resolveNamedRelationInstantiation` emitted dead steps; `foldedComprehension` moves to the Task-7 library module), all `openComprehension`/`openAbstraction` routes in `moves.ts`/`proof-front.ts`/`shell.ts`, `actions.ts` descriptors `instantiate`/`abstractWrap`/`relUnfold`/`relFold`, and their tests (12 tests/app files per survey; e2e files are Fix-5's plan, leave red-listed in the report, excluded from gates via playwright config only if currently included — verify: they are NOT in vitest gates).
- The app temporarily has NO comprehension gestures (interaction successor = next plan, gated on the pending user rulings). `comprehension-macros.ts` is REWRITTEN (not deleted): `macroComprehensionInstantiate/Abstract` recast as the derived sequences over the new primitives — they are the conservativity oracles, test-only consumers.
- [ ] Full suite `npm run test:all` green + tsc 0 at end of this task (the temporary red window closes here).
- [ ] Commit `refactor: strip carrier UX; app awaits primitive gestures`.

### Task 6: conservativity recast

**Files:** `tests/app/comprehension-macros.test.ts` (~80 assertions recast: same scenarios, same `exploreForm` outcomes, driven through comprehensionIntro → derived swap sequences → comprehensionElim), `tests/kernel/formal/highlevel-alias-parity.test.ts` (:13,124 — recast off bodyAttach), `plan12-adversarial`, `folded-guard`, `define/library` test surfaces.
- The derived-swap helper (iterate K → join x⃗ → deiterate → DC-elim → erase) lives as a TEST/library utility, not a kernel rule.
- [ ] Every old scenario maps to a new-primitive derivation or carries an inline no-successor comment; suite green.
- [ ] Commit `test: conservativity of drawn definitions over carrier scenarios`.

### Task 7: the library layer + frege rewrite (the long pole)

**Files:** new `src/theories/equality.ts` (Eq_σ⃗ ambient definitions + swap-lemma theorem constructions per signature in use — proven IN-SYSTEM as recorded theorems, the E-layer bootstrap); `define.ts` gains the singleton-companion macro (auto K over one ref atom — absorb `foldedComprehension`); `theories/frege.ts` (942 lines): the 27 `unfold`/`fold` recorded actions become derived sequences or Eq-lemma citations; the induction comprehensions (G at :164,323-325,511) become drawn K via comprehensionIntro; `refoldPlus`/`refoldSucc`/guard machinery recast; `theories/macros.ts` in kind.
- OBLIGATION resolved here or BLOCKED loudly: citation at negative-parity occurrences (theorem.ts's forward⇒positive gate + backActions mechanism must carry the symmetric swap lemma; if the citation machinery cannot express it, report with the exact refusal — do not weaken the gate).
- [ ] `tests/theories/frege.test.ts` 14/14 green again (same theorem names, same statement assertions — the survey's census is the checklist); Eq/companion library unit tests; full suite + tags gate green.
- [ ] Commit `feat: Eq library and frege on drawn definitions`.

### Task 8: final sweep + whole-branch review gate

- [ ] Greps: no `'body'` node-kind residue (λ-term path `'body'` strings exempt — the survey's false-positive list); no dead step kinds; no `bodyAttach|bodyDetach|applyUnfold|applyFold` outside history comments; fix-list plan + ledger updated.
- [ ] Full gate: `test:all`, tsc, `formal:tags`, and the physics suite untouched (junction work must not regress: 1525+ count maintained).
- [ ] Whole-branch task review per SDD; then STOP — the interaction-gesture plan (spawn/join/cite gestures, K-collapse affordance, e2e rebuild) is a separate plan awaiting the two user rulings.

## Verification

Conservativity (Task 6) + frege 14/14 (Task 7) are the semantic gates; `formal:tags` green is the TS↔Lean reconciliation gate; the app builds and runs (`npm run app`) with edit-mode drawing and non-comprehension proving intact — comprehension gestures intentionally absent until the successor plan.
