# Plan 11d: Closed-Term Introduction + Parameterized Comprehension

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The two user-approved kernel rules that unblock bare plusComm under the correct (inCutNat) encoding: closed-term introduction (fixes the seed wall — no rule could mint a term node in a positive region from a node-free sheet) and parameterized comprehension instantiation (fixes the nesting wall — induction predicates may reference ambient lines as parameters, making plusComm's comprehension flat).

**Architecture:** Branch `plan-11-arithmetic` (continues, post-11c: free-port names are canonical and non-semantic). One new rule module + one extension of comprehension instantiation, each with proof-layer wiring; then an in-tree spike verifying the flat plusComm route end-to-end before the theorem tasks get written.

**Soundness:**
- *Closed-term introduction:* every closed λ-term denotes an individual (its βη-class), so ∃x(x = t) is valid for closed t. Adding a valid, self-contained conjunct to ANY region is sound: in a positive region it is an equivalence (φ ⟺ φ ∧ ψ when ⊨ ψ); in a negative region it is subsumed by insertion. The K-trick (convert host t → `(λu.t)(s)`, fission, convert back) already derives exactly this whenever a host node exists — the rule removes the host requirement and replaces a three-step hack with one honest rule.
- *Parameterized comprehension:* instantiating ∀R φ(R) with R := λx⃗. ψ(x⃗, b⃗) for host lines b⃗ is textbook second-order comprehension with parameters. Mechanically the parameters are splice attachments — the same machinery insertion already trusts.

---

### Task 1: closedTermIntro rule (and the death of kMat)

**Files:**
- Create: `src/kernel/rules/intro.ts`
- Modify: `src/kernel/proof/step.ts` (variant `{ rule: 'closedTermIntro'; region: RegionId; term: Term }` + dispatch), `src/kernel/proof/json.ts` (ser/parse + roundtrip entry), `src/kernel/proof/compose.ts` (region remap; the term is host-id-free), `src/kernel/rules/index.ts`
- Modify: `src/theories/macros.ts` — DELETE `kMat` and its helpers entirely; the cursor gains a thin `intro(tag, region, term)` push wrapper if the ergonomics warrant it, otherwise callers push the step directly. No dual paths, no deprecation shims.
- Test: `tests/kernel/rules/intro.test.ts`, updates to `tests/theories/macros.test.ts` (kMat tests become intro tests asserting the same post-states), proof-layer test entries (json roundtrip, one replay test in step.test.ts)

`applyClosedTermIntro(d, region, term)`:
1. Region exists (structural, via the usual access pattern).
2. `freePorts(term)` is empty — refuse otherwise (`RuleError`: closed-term introduction requires a closed term). The term must also pass the same well-formedness the node validator enforces (mkDiagram re-checks; rely on it rather than duplicating).
3. Add one term node in `region` carrying `term`, with a fresh singleton output wire scoped at `region`. Nothing else changes. Result through `mkDiagram`.

No polarity gate — document why (header). Note the contrast in the rule comment: open terms must NOT be introducible this way (an open term's value depends on its argument lines; ∃x(x = t(ā)) is still valid, but the attachment plumbing is exactly what insertion/iteration regulate — the closed case is the one with zero entanglement).

- [x] **Step 1:** Failing tests: introduces `ZERO`-like closed term at root (positive) — node present, fresh singleton output wire at the region's scope, nothing else changed (node/wire/region counts); works inside a cut (negative) and inside a bubble; refuses an open term naming the gate; replay + json roundtrip + compose region-remap entries. Run, observe fail.
- [x] **Step 2:** Implement + wire the proof layer; observe pass.
- [x] **Step 3:** Replace every `kMat` use in `src/theories/macros.ts` and its tests with the rule; DELETE kMat. Full suite green, tsc clean. Commit `plan 11d task 1: closedTermIntro rule; kMat deleted`.

### Task 2: Parameterized comprehension instantiation

**Files:**
- Modify: `src/kernel/rules/comprehension.ts` (`applyComprehensionInstantiate` gains `attachments: readonly WireId[]`), `src/kernel/proof/step.ts` (the `comprehensionInstantiate` variant gains `readonly attachments: readonly WireId[]`), `src/kernel/proof/json.ts` (field + strict key check), `src/kernel/proof/compose.ts` (map attachments through iso.wires)
- Test: `tests/kernel/rules/comprehension-instantiate.test.ts`, `tests/kernel/rules/open-instantiate.test.ts` additions, proof-layer entries

Semantics: the comp's boundary is now `arity` argument stubs FOLLOWED BY the parameter wires, in order. Gates:
1. `comp.boundary.length === arity + attachments.length` (replaces the exact-arity check; the old error message generalizes — keep it precise about both numbers).
2. Every attachment wire exists and its scope encloses the region where the spliced copies land (the splice already validates enclosure; rely on it, but the rule must refuse a *count* mismatch itself).
3. Existing gates unchanged (proper enclosure of the bubble, binder map discipline for relation stubs).

Mechanically: where the instantiation splices a comp copy for each atom occurrence, the copy's trailing boundary wires splice onto `attachments` (same path insertion uses); the leading `arity` stubs splice onto the atom's argument wires exactly as today. All existing call sites pass `attachments: []` — update them; the JSON parser REQUIRES the field (no optional-field compatibility; stored bundled theories rebuild from source).

`applyComprehensionAbstract` does NOT gain parameters in this plan — out of scope, recorded in the deferred list (the abstraction direction needs its own occurrence-shape design).

- [x] **Step 1:** Failing tests: (a) instantiate a 1-ary bubble with a comp whose body references one parameter — the spliced copies' parameter ports land on the GIVEN host wire (assert wire identity, both for a root-scoped parameter and for one scoped at the bubble's parent); (b) count-mismatch refusals in both directions (too many/too few attachments) naming both numbers; (c) the flat plusComm comp shape from the spike — pair `PLUS x b`/`PLUS b x` with x the stub and b the parameter — instantiates into ℕ's bubble with copies riding the ambient b-line; (d) `attachments: []` reproduces every existing green instantiation (run the two existing test files); (e) json strict-key + roundtrip + compose wire-remap. Observe fail.
- [x] **Step 2:** Implement; observe pass; full suite + tsc green. Commit `plan 11d task 2: parameterized comprehension instantiation`.

### Task 3: Flat plusComm route spike (in-tree)

**Files:** `/tmp/spike4/` scripts only (nothing under src/ or tests/); findings preserved to `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/spike4/` at the end.

With both rules live: re-derive bare succShiftS against inCutNat using `closedTermIntro` in place of every kMat/zSeed maneuver (expect a SHORTER trace), then derive bare plusComm with the FLAT parameterized comp R(x) := pair `PLUS x b̂` —o— `PLUS b̂ x` (x = stub, b = parameter on the lhs's b-line): base fact manufacturable at root (closedTermIntro ZERO + ported pair via fission + congruenceJoin), closure cites succShiftS, discharge by iso as in spike3, final R(a) IS the bare pair. checkTheorem green on both; audit zero ZERO/SUCC nodes at root in plusComm's lhs/rhs beyond the equality pair. Report the exact traces (one line per step) — these become the theorem tasks' specs.

- [x] Spike green, scripts preserved, traces recorded in the report and appended to this plan doc.

### Task 4: Adversarial review

Mutation probes: (1) drop the closed-term gate (allow open terms) — a refusal test must fail, and write the soundness story for WHY open introduction with auto-fresh argument wires would still be valid but is deliberately excluded (zero-entanglement principle) — confirm no test depends on open introduction; (2) closedTermIntro wires the output at d.root instead of the target region — a scope test must fail; (3) parameterized splice attaches parameters in reversed order — the wire-identity test must fail; (4) drop the count gate — refusal tests must fail. Independent hunt: can closedTermIntro + congruenceJoin forge anything the K-trick could not already derive (argue from derivability-equivalence: the rule equals K-trick modulo host availability, and a host is always introducible in negative regions via insertion — the genuinely new power is positive-region-from-empty; write the validity argument in the review record); parameter wires crossing cut boundaries (enclosure gate observed); json strict-key rejection. Plan-doc sync + verdict.

- [x] APPROVED verdict recorded; plan-doc sync.

---

**Deferred (recorded):** comprehension abstraction with parameters; relation fold/unfold (Plan 11e); the arithmetic theorem implementations (Plan 11 final tasks — specs come from Task 3's traces).


---

## Task 4 execution record: adversarial review (2026-07-02)

Scope reviewed: `a8e09de` (closedTermIntro + kMat deletion), `7632e7c` (parameterized comprehension), `43a2983` (spike4 scripts — verified runnable only). Baseline before review: 618/618 tests, tsc clean.

### Part A: mandated mutation probes

Each probe: mutate -> run suite -> observe failures -> revert -> observe green. `git diff src/` empty after every probe.

| # | Mutation | Catching tests (observed failing) | Suite result |
|---|---|---|---|
| 1 | `intro.ts`: closed-term gate dropped; open terms allowed with an auto-fresh singleton wire per free port | `tests/kernel/rules/intro.test.ts` "refuses an open term, naming the closed-term gate and the offending free ports"; `tests/theories/macros.test.ts` "refuses an open term with the step named and leaves the cursor untouched" | 2 failed / 616 passed |
| 2 | `intro.ts`: output wire scoped at `d.root` instead of the target region | `intro.test.ts` "introduces inside a cut ... wire scoped at the cut"; `intro.test.ts` "introduces inside a bubble; wire scoped at the bubble"; `macros.test.ts` "introduces inside a cut (negative region)" | 3 failed / 615 passed |
| 3 | `comprehension.ts`: splice order reversed to `[...attachments, ...args]` | `comprehension-instantiate.test.ts` "splices the copy with its parameter port on the GIVEN host wire (root-scoped parameter)", "(parameter at the bubble parent)", and "attaches the SAME parameter wire to every copy" | 3 failed / 615 passed |
| 4 | `comprehension.ts`: combined count gate (`boundary.length === arity + attachments.length`) dropped | `comprehension-instantiate.test.ts` "rejects positive bubbles, non-bubbles, and arity mismatches, by name" and "refuses attachment-count mismatches in both directions, naming all three numbers" | 2 failed / 616 passed |

Probe 1 doubles as the no-dependence check: with open introduction ENABLED, exactly the two refusal tests fail and all 616 others pass — nothing in the suite or `src/` relies on open terms being introducible (grep: every `closedTermIntro` construction site is the cursor's `intro()` or a test/spike passing a closed term). Note on probe 3: the flat-plusComm shape test is symmetric under the stub/parameter swap (both boundary wires carry two freeVar ports), so it does not fire on the reversal; the three dedicated wire-identity/sharing tests are the mandated catchers and all fired.

### Soundness argument 1: why OPEN introduction would be valid yet is excluded

An open introduction with FRESH singleton argument wires per free port asserts ∃x∃y⃗(x = t(y⃗)) in the target region. That is VALID: pick any values for y⃗ (the domain of individuals is nonempty — closed terms denote), and t(y⃗) denotes an individual, so x exists. Positive region: conjoining a valid sentence is an equivalence. Negative region: subsumed by insertion. So the gate is NOT load-bearing for soundness of the fresh-wire form — probe 1's full-suite run (only refusal tests fail) confirms this empirically: no derivation becomes unsound or breaks when the gate is dropped.

It is excluded deliberately on the zero-entanglement principle: the moment the rule mints argument WIRES, it owns attachment plumbing — and which lines a new subgraph may ride is exactly what insertion (negative, arbitrary attachments) and iteration (copy inward along existing lines) regulate with polarity gates. An open intro that only ever creates fresh singleton wires is safe but redundant (fresh existentials say nothing); the dangerous variant — attaching to EXISTING lines, asserting x = t(a⃗) about specific individuals — is precisely insertion's gated territory. Keeping intro closed-only means the rule has zero interaction with the entanglement-regulating rules, so its soundness argument never needs a polarity case split over attachments. One rule, one job.

### Soundness argument 2: derivability-equivalence of closedTermIntro

Can closedTermIntro (+ congruenceJoin) derive anything not derivable before the rule existed?

- **Region containing at least one node:** the K-trick (convert host u -> `(λv. u) t`, fission at `['arg']`, convert back) already minted an arbitrary closed t on a fresh singleton wire, at ANY polarity — conversion and fission are equivalences. The rule is the K-trick minus the host requirement; post-states are identical (the deleted `kMat` tests were rewritten as `intro` tests asserting the SAME post-states, and spike4 still uses the literal K-expand/fission/K-restore sequence where a host exists, interchangeably with intro).
- **Node-free NEGATIVE region:** insertion draws ANY well-formed subgraph there, including exactly this node+wire shape. Observed: `tests/kernel/rules/intro.test.ts` "is subsumed by insertion in a negative region" (added by this review) inserts the empty-boundary pattern of one term node on a singleton output wire into a cut and asserts fingerprint identity with `applyClosedTermIntro`.
- **Node-free POSITIVE region:** genuinely new power — no prior rule could put the first node on an empty positive sheet (insertion is negative-only; iteration/conversion/fission need existing material). It is valid because closed terms denote: ∃x(x = t) is true in every model, and φ ⟺ φ ∧ ψ when ⊨ ψ. This is the seed-wall fix the plan exists for.
- **BUBBLE region (quantifier, not negation):** same validity argument — the conjunct is added inside the comprehension body uniformly, and a valid self-contained conjunct is inert under any quantifier prefix. The wire scoping there is pinned by "introduces inside a bubble; wire scoped at the bubble", which probe 2 confirmed fires on mis-scoping.

congruenceJoin adds nothing beyond this: joining two intro'd nodes requires a βη-conversion certificate between their terms, i.e. it only ever identifies terms already provably equal — the same joins were available on K-trick-minted nodes.

### Part B: independent hunt findings

- **Forged quantifier scope (parameters):** `comprehension-instantiate.test.ts` "refuses a parameter wire scoped INSIDE the bubble when copies land outside its scope" does exercise the cross-CUT case: the parameter wire is scoped at `h.cut(bub)` — a genuine cut inside the bubble — while the copy lands at the bubble itself, escaping the cut. The refusal comes from the splice's own enclosure gate (`splice.ts`: attachment wire scope must enclose the splice region), the same gate insertion trusts.
- **Open comp + parameters combined:** no existing test combined binder-stub rebinding with attachments. Added `open-instantiate.test.ts` "threads a parameter through an OPEN comp": one application with a relation stub bound to the enclosing bubble AND one parameter; asserts the copy's atom rebinds to `rOuter` and the copy's parameter port lands on the given host wire itself. Passes.
- **compose.ts attachment remap:** verified by reading `compose.test.ts` "maps comprehensionInstantiate parameter attachments through the iso" — the marker-first/marker-last construction makes the iso non-identity such that db's parameter-wire id names a DIFFERENT legal wire in da (the atom's arg wire, which also encloses the splice region); an unmapped id would not refuse but silently attach wrong, and only the fingerprint comparison catches it. Strong as-is; also the `mapStepIds` unit entry covers order preservation and unknown-id refusal. Not strengthened.
- **kMat deletion:** `grep -rn kMat src/ tests/` — zero hits. Spike-script private copies under `docs/` are by design.
- **JSON strict-key:** `json.test.ts` requires the `attachments` field (deleting it fails with "attachments must be an array"), rejects unknown fields on both `closedTermIntro` and `comprehensionInstantiate`. Verified in the commit diffs and green in the suite.
- **Spike4 scripts:** both run from the repo via `./node_modules/.bin/vite-node`; observed `succShiftS4 checkTheorem PASSED (91 steps)` and `plusComm4 checkTheorem PASSED (49 steps)` (content preserved as evidence, not reviewed as shipped code).

### Task 3 spike4 traces (theorem-task specs; durable home)

Scripts live in `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/spike4/`. Run: `./node_modules/.bin/vite-node <run-ss4.ts|run-pc4.ts>`. Observed traces, one line per step:

**succShiftS4 (`run-ss4.ts`):**

```
  D1 iterate guard (iteration): ok
  D2 instantiate G (comprehensionInstantiate): ok
  t1 iterate nSc (iteration): ok
  t1b iterate nSc (iteration): ok
  t2 sever wsC (wireSever): ok
  t3 sever ws2 (wireSever): ok
  t4 fuse nS2->F1sc (fusion): ok
  t5 fuse nS3->F2sc (fusion): ok
  t6 unfold PLUS (unfold): ok
  t6 unfold SUCCl (unfold): ok
  t6 unfold SUCCr (unfold): ok
  t6 left-shift (conversion): ok
  t6 fission (fission): ok
  t6 E fold PLUS (fold): ok
  t6 E fold SUCC (fold): ok
  t6 D fold SUCC (fold): ok
  t7 unfold SUCCo (unfold): ok
  t7 unfold PLUS (unfold): ok
  t7 unfold SUCCi (unfold): ok
  t7 left-shift (conversion): ok
  t7 fission (fission): ok
  t7 E fold SUCC (fold): ok
  t7 E fold PLUS (fold): ok
  t7 D fold SUCC (fold): ok
  t8 iterate IH pair (iteration): ok
  t9 cJ E1c=H1pc (congruenceJoin): ok
  t9b cJ E2c=H2pc (congruenceJoin): ok
  t11 deiterate E1c (deiteration): ok
  t11b deiterate E2c (deiteration): ok
  b1 intro M (closedTermIntro): ok
  b2 iterate M (iteration): ok
  b3 unfold PLUS (unfold): ok
  b3 unfold ZERO (unfold): ok
  b3 unfold SUCC (unfold): ok
  b3 convert to F2_0 form (conversion): ok
  b3 fold SUCC (fold): ok
  b3 fold PLUS (fold): ok
  b3 fold ZERO (fold): ok
  b4 fission ZERO out of M (fission): ok
  b4b fission ZERO out of Mp (fission): ok
  b5 cJ Z1=Z2 (congruenceJoin): ok
  b6 erase Z2 dup (erasure): ok
  A7 deiterate base conjunct (deiteration): ok
  c1 dcIntro (doubleCutIntro): ok
  c2 insert IH+SUCC (insertion): ok
  c3 intro seedB (closedTermIntro): ok
  c4 K-expand (conversion): ok
  c4 fission (fission): ok
  c4 K-restore (conversion): ok
  c4b K-expand (conversion): ok
  c4b fission (fission): ok
  c4b K-restore (conversion): ok
  c5 unfold PLUS (unfold): ok
  c5 unfold SUCCl (unfold): ok
  c5 unfold SUCCr (unfold): ok
  c5 left-shift (conversion): ok
  c5 fission (fission): ok
  c5 E fold PLUS (fold): ok
  c5 E fold SUCC (fold): ok
  c5 D fold SUCC (fold): ok
  c5b unfold SUCCo (unfold): ok
  c5b unfold PLUS (unfold): ok
  c5b unfold SUCCi (unfold): ok
  c5b left-shift (conversion): ok
  c5b fission (fission): ok
  c5b E fold SUCC (fold): ok
  c5b E fold PLUS (fold): ok
  c5b D fold SUCC (fold): ok
  c6 iterate IH pair (iteration): ok
  c7 cJ E1=H1p (congruenceJoin): ok
  c7b cJ E2=H2p (congruenceJoin): ok
  c7c cJ D1=D2 (congruenceJoin): ok
  c8 deiterate E1 (deiteration): ok
  c8b deiterate E2 (deiteration): ok
  c8c erase seedB (erasure): ok
  A8 deiterate Cl conjunct (deiteration): ok
  A9 dcElim cut1c (doubleCutElim): ok
  bare G(m) at root on wm: true
  e2 A1 K-expand (conversion): ok
  e2 A1 fission (fission): ok
  e2 A1 K-restore (conversion): ok
  e2 A2 K-expand (conversion): ok
  e2 A2 fission (fission): ok
  e2 A2 K-restore (conversion): ok
  e2 cJ A1=A2 (congruenceJoin): ok
  e2 sever oG (wireSever): ok
  e2 fuse F1m->A1 (fusion): ok
  e2 fuse F2m->A2 (fusion): ok
  e2 convert A1 (conversion): ok
  e2 convert A2 (conversion): ok
  e3 erase base fact (erasure): ok
  e3 erase Cl fact (erasure): ok
succShiftS4 checkTheorem PASSED (91 steps)
audit: lhs/rhs root ZERO nodes: 0 0 | lhs root nodes: 1 | rhs root nodes: 3
```

**plusComm4 (`run-pc4.ts`):**

```
  D1 iterate guard A (iteration): ok
  D2 instantiate R(x):=x+b -o- b+x (comprehensionInstantiate): ok
  t1 iterate nSc (iteration): ok
  t1b iterate nSc (iteration): ok
  t2 sever wsC (wireSever): ok
  t3 sever ws2 (wireSever): ok
  t4 fuse nS2->P1s (fusion): ok
  t5 fuse nS3->P2s (fusion): ok
  t6 unfold PLUS (unfold): ok
  t6 unfold SUCC (unfold): ok
  t6 left-shift (conversion): ok
  t6 fission (fission): ok
  t6 E fold PLUS (fold): ok
  t6 P1s fold SUCC (fold): ok
  t8 iterate IH pair (iteration): ok
  t9 cJ E1c=H1pc (congruenceJoin): ok
  t11 deiterate E1c (deiteration): ok
  b0 intro K-seed (closedTermIntro): ok
  b1 M=PLUS ZERO b K-expand (conversion): ok
  b1 M=PLUS ZERO b fission (fission): ok
  b1 M=PLUS ZERO b K-restore (conversion): ok
  b2 iterate M (iteration): ok
  b3 unfold PLUS (unfold): ok
  b3 unfold ZERO (unfold): ok
  b3 convert to b+0 (conversion): ok
  b3 fold PLUS (fold): ok
  b3 fold ZERO (fold): ok
  b4 fission ZERO out of M (fission): ok
  b4b fission ZERO out of Mp (fission): ok
  b5 cJ Z1=Z2 (congruenceJoin): ok
  b6 erase Z2 dup (erasure): ok
  A7 deiterate base conjunct (deiteration): ok
  c1 dcIntro (doubleCutIntro): ok
  c2 insert hyp pair+SUCC (insertion): ok
  c3 iterate guard B (iteration): ok
  c3b intro seedB (closedTermIntro): ok
  c4 mint SUCC(y) K-expand (conversion): ok
  c4 mint SUCC(y) fission (fission): ok
  c4 mint SUCC(y) K-restore (conversion): ok
  c5 cite succShiftS4 (theorem): ok
  c6 fission A2 (fission): ok
  c7 iterate IH pair (iteration): ok
  c8 cJ E2=H2p (congruenceJoin): ok
  c9 deiterate E2 (deiteration): ok
  c10 erase occurrence leftovers (erasure): ok
  A8 deiterate Cl conjunct (deiteration): ok
  A9 dcElim cut1c (doubleCutElim): ok
  e1 erase base fact (erasure): ok
  e2 erase Cl fact (erasure): ok
  pair output shared: true
plusComm4 checkTheorem PASSED (49 steps)
audit: lhs/rhs root nodes: 0 2 | wa endpoints lhs/rhs: 1 3 | wb endpoints lhs/rhs: 1 3
audit deltas (nodes/regions/wires): ss lhs 7/6/6 rhs 9/6/7 | pc lhs 12/11/8 rhs 14/11/9
audit: rhs root node terms are both PLUS s0 s1: true
```

### Verdict

**APPROVED.** All four mandated probes were caught by named tests and fully reverted (git diff of src/ empty). No soundness defect found in the independent hunt; the two coverage gaps identified (insertion-subsumption unobserved, open-comp+parameter combination untested) were closed by the review battery commit `plan 11d task 4: review battery additions`. Final state: 620/620 tests, tsc clean.
