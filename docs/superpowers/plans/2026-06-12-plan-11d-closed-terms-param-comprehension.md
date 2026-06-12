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

- [ ] **Step 1:** Failing tests: introduces `ZERO`-like closed term at root (positive) — node present, fresh singleton output wire at the region's scope, nothing else changed (node/wire/region counts); works inside a cut (negative) and inside a bubble; refuses an open term naming the gate; replay + json roundtrip + compose region-remap entries. Run, observe fail.
- [ ] **Step 2:** Implement + wire the proof layer; observe pass.
- [ ] **Step 3:** Replace every `kMat` use in `src/theories/macros.ts` and its tests with the rule; DELETE kMat. Full suite green, tsc clean. Commit `plan 11d task 1: closedTermIntro rule; kMat deleted`.

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

- [ ] **Step 1:** Failing tests: (a) instantiate a 1-ary bubble with a comp whose body references one parameter — the spliced copies' parameter ports land on the GIVEN host wire (assert wire identity, both for a root-scoped parameter and for one scoped at the bubble's parent); (b) count-mismatch refusals in both directions (too many/too few attachments) naming both numbers; (c) the flat plusComm comp shape from the spike — pair `PLUS x b`/`PLUS b x` with x the stub and b the parameter — instantiates into ℕ's bubble with copies riding the ambient b-line; (d) `attachments: []` reproduces every existing green instantiation (run the two existing test files); (e) json strict-key + roundtrip + compose wire-remap. Observe fail.
- [ ] **Step 2:** Implement; observe pass; full suite + tsc green. Commit `plan 11d task 2: parameterized comprehension instantiation`.

### Task 3: Flat plusComm route spike (in-tree)

**Files:** `/tmp/spike4/` scripts only (nothing under src/ or tests/); findings preserved to `docs/superpowers/plans/2026-06-11-plan-11-spike-scripts/spike4/` at the end.

With both rules live: re-derive bare succShiftS against inCutNat using `closedTermIntro` in place of every kMat/zSeed maneuver (expect a SHORTER trace), then derive bare plusComm with the FLAT parameterized comp R(x) := pair `PLUS x b̂` —o— `PLUS b̂ x` (x = stub, b = parameter on the lhs's b-line): base fact manufacturable at root (closedTermIntro ZERO + ported pair via fission + congruenceJoin), closure cites succShiftS, discharge by iso as in spike3, final R(a) IS the bare pair. checkTheorem green on both; audit zero ZERO/SUCC nodes at root in plusComm's lhs/rhs beyond the equality pair. Report the exact traces (one line per step) — these become the theorem tasks' specs.

- [ ] Spike green, scripts preserved, traces recorded in the report and appended to this plan doc.

### Task 4: Adversarial review

Mutation probes: (1) drop the closed-term gate (allow open terms) — a refusal test must fail, and write the soundness story for WHY open introduction with auto-fresh argument wires would still be valid but is deliberately excluded (zero-entanglement principle) — confirm no test depends on open introduction; (2) closedTermIntro wires the output at d.root instead of the target region — a scope test must fail; (3) parameterized splice attaches parameters in reversed order — the wire-identity test must fail; (4) drop the count gate — refusal tests must fail. Independent hunt: can closedTermIntro + congruenceJoin forge anything the K-trick could not already derive (argue from derivability-equivalence: the rule equals K-trick modulo host availability, and a host is always introducible in negative regions via insertion — the genuinely new power is positive-region-from-empty; write the validity argument in the review record); parameter wires crossing cut boundaries (enclosure gate observed); json strict-key rejection. Plan-doc sync + verdict.

- [ ] APPROVED verdict recorded; plan-doc sync.

---

**Deferred (recorded):** comprehension abstraction with parameters; relation fold/unfold (Plan 11e); the arithmetic theorem implementations (Plan 11 final tasks — specs come from Task 3's traces).
