# Plan 11b: Head-Stripping Rule + HNF/WHNF Tactic

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Two user-approved equational-reasoning additions: a head-stripping kernel rule (from an equation between head-normal terms with the same rigid head, conclude the pairwise argument equations) and a head-normalization tactic (compute HNF/WHNF and emit an ordinary certificate-carrying conversion step).

**Architecture:** Branch `plan-11-arithmetic` (continues). Term layer gains a head-reduction normalizer; rules layer gains `headStrip` mirroring `congruenceJoin`'s locally-entailed-addition pattern; the tactic is a thin helper over `applyConversion`.

**Binding design law (user): port names are never semantic and never user-visible.** This rule is specified name-blind: heads correspond by de Bruijn index (bound) or by WIRE (free); arguments pair by position. No gate, error message, or report may mention a port name.

**Soundness (the rule's comment must carry this):**
- *Decomposition:* for terms in head-normal form `λx₁…xₙ. h e₁…eₘ`, the head is rigid — no β/η step can consume it. By Church–Rosser, if two such terms with the same binder count, same head, and same argument count are βη-equal, every common reduct preserves the spine, so corresponding arguments are βη-equal as open terms, hence their prefix-closures are equal.
- *Polarity-blindness:* the rule ADDS the argument equations next to the two co-resident equation nodes. Locally-entailed addition is an equivalence (φ ⟺ φ ∧ ψ when φ ⊢ ψ within the region) — same justification as congruenceJoin, valid under any polarity.
- *Constant heads are not rigid* (definitionally transparent) and must be refused — `PLUS a b = PLUS b a` must never strip to `a = b`. Unfold first.

---

### Task 1: Head normalization in the term layer

**Files:**
- Create: `src/kernel/term/hnf.ts`
- Test: `tests/kernel/term/hnf.test.ts`

API:
- `headSpine(t: Term): { binders: number; head: { kind: 'bound'; index: number } | { kind: 'free'; name: string } | { kind: 'const'; constId: string } | { kind: 'redex' }; args: readonly Term[] }` — structural spine analysis, no reduction. `redex` when the spine head is a λ applied to something (or an η-contractible wrapper blocks the spine — define precisely: the head position is the leftmost-innermost application target under the binder prefix).
- `headNormalize(t: Term, fuel: number): { term: Term; steps: readonly ReductionStep[] }` — repeated HEAD β-steps (the spine redex only) until the head is bound/free/const, recording each step's path (the same `ReductionStep` the certificate checker consumes). Throws a plain `Error` naming the fuel on exhaustion (divergent head — loud, no silent partial result). No unfolding: a `const` head terminates normalization (the caller decides whether to unfold).
- `weakHeadNormalize(t: Term, fuel: number)` — same but stops without descending under the binder prefix (no reduction inside a top-level λ body unless the term is itself the redex spine). Document the difference in one sentence each.

- [x] **Step 1:** Failing tests: (a) `headSpine` on `\x. f x y` → binders 1, free head, 2 args; on `\x. x y` → bound head index 0; on `PLUS a b` → const head; on `(\u. u) y` → redex. (b) `headNormalize((\u. \v. u) a b)` reaches free head `a` with recorded steps that `checkConversion` accepts as the left half of a certificate against the result. (c) `headNormalize(Y-style divergent head, fuel 50)` throws mentioning fuel. (d) `weakHeadNormalize` stops at a λ that `headNormalize` would enter. Run, observe failure.
- [x] **Step 2:** Implement; observe pass; `npx tsc --noEmit` + full suite green.
- [x] **Step 3:** Commit `plan 11b task 1: head normalization (hnf/whnf) in the term layer`.

### Task 2: The conversion tactic

**Files:**
- Create: `src/app/tactics.ts`
- Test: `tests/app/tactics.test.ts`

`convertToHeadNormal(d: Diagram, node: NodeId, fuel: number): { diagram: Diagram; step: ProofStep }` and `convertToWeakHeadNormal(...)`: run the Task 1 normalizer on the node's term, build the certificate `{ leftSteps: steps, rightSteps: [] }`, return the applied `conversion` step (reuse `applyConversionByCertificate`; attachments `{}` — head reduction never adds free ports). Refuse loudly (plain `Error`) when the head is a constant: the message must say which constant and that unfold comes first — without mentioning any port name.

- [x] **Step 1:** Failing tests: tactic on a node with `(\u. u) y` rewrites the node to `y` and the step replays through `replayProof`; constant-head node refuses naming the constant; already-normal node refuses ("already in head-normal form") rather than emitting a no-op step.
- [x] **Step 2:** Implement; observe pass; suite green.
- [x] **Step 3:** Commit `plan 11b task 2: HNF/WHNF conversion tactic`.

### Task 3: headStrip kernel rule

**Files:**
- Create: `src/kernel/rules/headstrip.ts`
- Modify: `src/kernel/proof/step.ts` (variant `{ rule: 'headStrip'; a: NodeId; b: NodeId }` + dispatch), `src/kernel/proof/json.ts` (ser/parse + roundtrip enumeration), `src/kernel/proof/compose.ts` (node remap), `src/kernel/rules/index.ts`
- Test: `tests/kernel/rules/headstrip.test.ts` (+ one replay-level test in `tests/kernel/proof/step.test.ts`, one roundtrip entry in `tests/kernel/proof/json.test.ts`)

`applyHeadStrip(d: Diagram, a: NodeId, b: NodeId): Diagram`. Gates, in order, each a `RuleError` (except structural `DiagramError` from the access helpers):
1. `a !== b`; both term nodes; same region R.
2. The two output ports share ONE wire (this is what makes the pair an equation) — refuse otherwise.
3. Both terms pass `headSpine` with head kind `bound` or `free` (refuse `const`: "a defined constant head is not rigid; unfold it first", naming the constant; refuse `redex`: "not in head-normal form; apply the HNF tactic first").
4. Equal binder counts, equal argument counts (the certificate-free rule demands literal spine alignment; η-mismatched spines are the tactic's job to align first — refuse with counts in the message).
5. Heads correspond: both `bound` with equal index, or both `free` attached to the SAME wire (compare `wireAt(d, a, headPort)` vs `wireAt(d, b, headPort)` — never names).
6. For each argument position i, build the prefix-closures `λx₁…xₙ. aᵢ` and `λx₁…xₙ. bᵢ` (wrap with the same binder count n — de Bruijn indices into the prefix stay valid; free ports unchanged). Skip positions where the two closures are `termEq` AND every shared free port rides the same wire in both nodes (the equation is trivial — adding it is noise; this skip is exactness, not heuristic: the added conjunct would be derivable by one iteration).
7. For each remaining position: add two term nodes in R carrying the closures, each free port attached to the wire that port rides on the parent node (`wireAt`), and one fresh wire scoped at R shared by their outputs. The original nodes stay untouched.

Result passes `mkDiagram`. The rule never removes anything and never touches polarity — see the soundness comment obligations in the header.

- [x] **Step 1:** Failing tests, minimum: (a) strips `f a b —o— f a c` (f, a, b, c on wires; same f-wire, same a-wire) into ONE added equation pair for position 2 (position 1 skipped as trivial), closures correct, fresh wire scoped at R; (b) works identically inside a cut (polarity-blind); (c) bound-head case `\x. x a —o— \x. x b` strips under the binder with closures `\x. a`/`\x. b`; (d) refusals: outputs on different wires; const head (message names the constant); redex head; binder-count mismatch; arg-count mismatch; free heads on different wires; same node twice; (e) RuleError vocabulary. NO test may assert on a port name.
- [x] **Step 2:** Implement rule + proof-layer wiring; observe pass; suite + tsc green.
- [x] **Step 3:** Commit `plan 11b task 3: headStrip rule (rigid-head equation decomposition)`.

### Task 4: Review and plan-doc sync

- [x] **Step 1:** Adversarial review (inherit-model) with mutation probes: (a) allow const heads through gate 3 — a soundness test must fail; (b) compare free heads by name instead of wire — a test with same-named heads on different wires must fail; (c) drop the shared-output gate — a refusal test must fail. Each observed fail → revert → pass.
- [x] **Step 2:** Tick boxes, record deviations, full suite + E2E green. (Merge happens with Plan 11's final merge — same branch.)

---

## Execution record (2026-06-12)

All four tasks complete on `plan-11-arithmetic`: 556a055 (hnf), 4d21c83 (tactics), 09b207d (headStrip + wiring), 0dcc6a0 (review battery). Final state: 582/582 unit tests, tsc clean, E2E 3/3.

Deviations/resolutions: headSpine η-wrapper classified via the spine definition (no separate η head kind); WHNF const-refusal fires only when the constant blocked the normalizer (a top-level λ is already WHNF); all-trivial headStrip application is a no-op (pinned); json.test.ts step-kind enumeration gained the missing vacuousIntro/vacuousElim entries.

Review verdict APPROVED. All three mandated mutation probes caught by existing tests; review added 7 tests pinning the closure de Bruijn index law, the hnf fuel boundary, exotic redex spines, nested-cut wire scope, tactic port-trimming, json extra-key rejection, and compose remapping. Semantic note on record: headStrip is the first rule whose validity depends on equality-as-βη (rigid-head injectivity fails in arbitrary first-order models) — the intended semantic commitment of this system, per the user-approved design.
