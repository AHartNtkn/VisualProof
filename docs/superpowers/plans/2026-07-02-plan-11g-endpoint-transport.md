# Plan 11g: Closed-evidence endpoint transport — certifying concrete numerals

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** USER-ADMITTED (2026-07-02) kernel rule `endpointTransport`, restoring the guard-producing theorems (`zeroIsNat`, `succNat`, `oneIsNat`) non-vacuously in the relational theory — concrete numerals become certifiable, so the guarded arithmetic (`succShiftS`, `plusComm`) applies to actual numbers.

**Why a new rule (the wall, verified exhaustively in plan 11f):** inCutNat's base evidence lives INSIDE the guard bubble — that is exactly what makes ℕ non-vacuous — and every existing mechanism that identifies the external argument line with the internal base wire lifts the internal wire out of the bubble (congruenceJoin: cut-depth gate; wireJoin: merges to outer scope, breaking relFold arity; conclusion-atom routes: unseverable or guard-collapsing). Non-vacuity and base-case underivability were two sides of one mechanism; transport splits them by moving a single ENDPOINT while wires and quantifiers stay put.

**The rule.** `applyEndpointTransport(d, a, b, endpoint, certificate)`:
- `a`, `b` are TERM nodes co-resident in one region R; their terms are CLOSED (no free ports) and βη-equal by replayed certificate (conversion-style, fuel-free).
- `endpoint` is an existing endpoint (node+port) on `a`'s output wire, whose node lies at or inside R.
- Effect: that one endpoint moves to `b`'s output wire. Nothing else changes — no wire is created, deleted, or re-scoped; no region moves.
- Soundness (congruenceJoin class — locally-entailed equivalence, polarity-blind): within R, the two output wires provably carry the same closed value (⟦wireA⟧ = ⟦tA⟧ = ⟦tB⟧ = ⟦wireB⟧), so re-attaching a consumer that lives inside R across the two lines is an equivalence in both directions. Closedness gives zero binder entanglement: no capture, no scope interaction, hence no vacuity risk — the internal base wire keeps its bubble scope forever.
- Refusals (each with an instructive message + test): non-term nodes; open terms; failed certificate; evidence nodes in different regions; endpoint not on `a`'s output wire; endpoint's node outside R.

### Task 0: Spike — the rule closes zeroIsNat

Prototype the rule (scratch, kernel internals) and derive relational `zeroIsNat` end-to-end: lhs `Zero(z)`, boundary [wz]; rhs `nat(z) ∧ Zero(z)`. Sketch: build the nat body around z at positive polarity (doubleCutIntro / insertion-into-negative / vacuous-bubble moves), iterate the external Zero evidence into the guard bubble, transport the internal consumer endpoint onto the z-side line (or vice versa — spike decides the direction), relFold to the `nat` ref. Record the exact step list and every gate hit in this doc.

- [x] Spike green; findings recorded; scratch deleted (transplanted into frege.ts in Task 2).

**Spike findings (zeroIsNat, 12 steps, checkTheorem green first try).** Direction: build the guard body with the conclusion atom on the INTERNAL base line, then transport that conclusion endpoint onto the external z line. Exact trace:
1. `doubleCutIntro` empty at root → cutO ⊃ cutI (the ¬¬ scaffold; cutI becomes the ¬R conclusion cut).
2. `vacuousIntro` arity 1 wrapping {cutI} at cutO → guard bubble rB (cutO ⊃ rB ⊃ cutI). Absorbing cutI into rB is what avoids the "leftover empty cut collapses the guard" wall — there is no empty sibling cut.
3. `insertion` into rB (negative) of a closed pattern = a stub bubble (arity 1, binder-mapped → rB) holding `Zero(w0)` (zero ref), base atom `R(w0)`, and the closure cut `Cl(R)` (succ ref + two atoms). w0 is scoped in rB (non-vacuity preserved, untouched thereafter).
4. `iteration` of the base atom `R(w0)` from rB into cutI → conclusion `¬R(w0)`. Now the body is the tautological `¬∃R∃w0[Zero(w0)∧R(w0)∧Cl(R)∧¬R(w0)]` — valid, built by sound moves, conclusion on the base line.
5. `relUnfold` internal zero ref → ZEROp term node `z0` on w0; `relUnfold` external zero ref → ZEROp `zExt` on wz; `iteration` of zExt into rB → co-resident ZEROp `b` on wz. (Transport needs TERM nodes on both lines; the hypothesis Zero(z) is what supplies `b`.)
6. `endpointTransport(a=z0, b, endpoint=R-conclusion atom on w0)` → the conclusion moves from w0 to wz. Body is now EXACTLY natRelation(z): base `R(w0)` on the bubble-scoped w0, conclusion `¬R(z)` on the external line.
7. `deiteration` removes the iterated ZEROp copy `b` (justified by zExt at root).
8-9. `relFold` z0 → zero ref on w0; `relFold` zExt → zero ref on wz (restores Zero(z) for the rhs).
10. `relFold` the whole cutO subtree → `nat` ref on wz.

Result: `nat(z) ∧ Zero(z)`, boundary [wz]. The nat body (natRelation) is NEVER structurally altered — the non-vacuity guard is safe by construction. Transport is load-bearing: without step 6 the conclusion stays on w0 and the step-10 fold-to-nat refuses (occurrence ≠ natRelation).

**Rule details the spike fixed.** Transport moves ONE consumer endpoint from `a`'s output wire to `b`'s; `a`,`b` are co-resident CLOSED term nodes, βη-equal by certificate; the endpoint's node must lie at-or-inside their region R (locality of the entailed equality); refuses non-term/open/failed-cert/cross-region/shared-output/not-on-a's-wire/a's-own-output/consumer-outside-R. Polarity-blind (no gate), congruenceJoin soundness class.

### Task 1: The kernel rule

**Files:** `src/kernel/rules/transport.ts` (applyEndpointTransport + doc-comment with the soundness argument), `rules/index.ts`, proof step `{ rule: 'endpointTransport'; a; b; endpoint; certificate }` in `proof/step.ts` + `proof/json.ts` (serialization round-trip).
**Test:** `tests/kernel/rules/transport.test.ts` — the happy path, every refusal observed with its message, JSON round-trip, and a soundness-shaped probe: transport must NOT be admissible when either term is open (mutate the gate → test fails). Polarity-blindness: works at positive and negative regions alike.

- [x] Rule + step + tests green; full suite + tsc green. Commit. (`src/kernel/rules/transport.ts`, wired into `rules/index.ts`, `proof/step.ts`, `proof/json.ts`, `proof/compose.ts`; `tests/kernel/rules/transport.test.ts` — 12 tests: happy path, 9 refusals each with message observed, polarity-blindness, JSON round-trip, and the closedness gate-mutation probe verified fail→pass. Full suite 752/752 + tsc green.)

### Task 2: The guard-producing theorems

**Files:** `src/theories/frege.ts` — derive `zeroIsNat` (Zero(z) ⟹ nat(z) ∧ Zero(z)), `succNat` (nat(n) ∧ Succ(n,s) ⟹ nat(s) ∧ …), `oneIsNat` (composition), per the spike trace. Insert in dependency order before their consumers if any citation uses them.
**Test:** theory battery — checkTheorem green for the new theorems; the non-vacuity guard test still green (the nat body is UNCHANGED — transport must not have required touching it); a citation smoke test: `nat(1)` certified and fed into a `plusComm` citation.

- [x] Theorems green through the JSON road; suite + tsc green. Commit. (e2e left for the reviewer.)

**Task 2 findings.** All three guard-producers derived, folded relational statements, verified through `theoryToJson → loadTheory` (verifyTheory re-runs checkTheorem). `natRelation` was NOT touched — the non-vacuity guard test stays green.
- `deriveZeroIsNat` (12 steps): transport, as spiked above. Boundary [z].
- `deriveSuccNat` (19 steps): `nat(n) ∧ Succ(n,s) ⟹ Succ(n,s) ∧ nat(s)`, boundary [wn,ws]. Does NOT use transport. Fresh nat(s) skeleton; iterate nat(n) into the conclusion cut and `comprehensionInstantiate` its R with the skeleton's R (second-order MP, binder-parameter); **bridge the two bubble-scoped zero witnesses with `wireJoin`** — both are INTERNAL lines, so the merge keeps the outer bubble scope and never touches root, sidestepping the UPDATE-10 wall (which only bit relating the base to the EXTERNAL arg line). Deiterate the copy's base + closure → R(n); guarded MP (`iterate Cl → bind m=n,t=s via wireJoin → deiterate R(n) and the hypothesis Succ(n,s) → dcElim`) → R(s); fold to nat(s); erase the consumed nat(n). This confirms UPDATE 10's prediction that succNat is OK ("base inherited, never created").
- `deriveOneIsNat` (2 steps): composition — cite zeroIsNat forward on Zero(z), then succNat forward on nat(z) ∧ Succ(z,o). `Zero(z) ∧ Succ(z,o) ⟹ nat(o) ∧ Zero(z) ∧ Succ(z,o)`, boundary [wz,wo]. Certifies concrete nat(1). Smoke test: nat(o) from oneIsNat fed into a `plusComm` forward citation (Plus(o,b,sum) → Plus(b,o,sum)) green.

**Statement adjustments (flagged):** none — all three ship the intended relational statements. succNat and oneIsNat CONSUME/retain exactly as stated (succNat consumes nat(n), retains Succ; oneIsNat retains both premises and adds nat(o)).

### Task 3: Review + sync

- [ ] Independent adversarial review: mutation probes on every transport gate; verify no derivation path re-opens vacuity (the guard test is the sentinel); JSON replay of the new theorems.
- [ ] Plan-doc + memory sync (`plan11-arithmetic-spike-findings` gains the resolution).
