# Second-Order to Higher-Order Lean Conversion Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the restored completed second-order Lean formalization into
the zero-signature, recursive-signature-wire higher-order calculus while
preserving its generic semantic verification architecture and proving the two
requested semantic completeness results.

**Architecture:** Begin only from the restored production tree at commit
`6693b04`. Replace its second-order vocabulary with the complete target
declaration surface before proving individual results. Preserve the established
rule → dispatcher → replay → checked theorem → verified theory soundness chain,
but replace every Lambda-, term-, equation-, bubble-, and monolithic-
comprehension-specific declaration. Formula expressiveness and primitive
derivability are separate capstones over the same all-model semantics.

**Tech Stack:** Lean 4.30/Lake; restored `VisualProof/` formalization; production
TypeScript formula and rule sources as correspondence authorities; Node.js
validation already owned by the repository.

## Global Constraints

- The implementation baseline is exactly commit `6693b04` for `VisualProof/`,
  `VisualProof.lean`, `lakefile.toml`, and `lean-toolchain`.
- `/tmp/vpa-current-lean-code-20260804-XO7NPu` is recovery material only. Do
  not copy declarations, helpers, APIs, or proof structure from it into the new
  development without deriving them independently from this plan and the
  governing specifications.
- Governing specification precedence is:
  1. `2026-07-25-zero-signature-hol-redesign-design.md` removes Lambda/terms,
     adds identity content, and requires all-model semantics;
  2. `2026-07-22-signature-indexed-wires-design.md` replaces second-order
     relation bubbles with recursive signature-indexed wires;
  3. `2026-07-29-primitive-wire-quantifier-rules-design.md` replaces durable
     monolithic relation substitution/comprehension steps with primitive wire
     rules and requires constructive redundancy in Lean.
- Later user clarifications control conflicts: preserve the generic completed
  second-order soundness architecture, but not second-order-specific theorems;
  prove soundness for every actual new rule; formula completeness means semantic
  expressiveness only; primitive completeness means direct substitution and
  comprehension are constructively reproducible by primitive steps; identity
  normalization is independent of primitive compiler adequacy.
- Lean RED is the owning production theorem declaration elaborating with
  `sorry`. GREEN is that same declaration with a kernel-checked proof and no
  `sorry`.
- Never create fixture modules, redundant `example` declarations, `#check`
  declarations, or separate test theorems to manufacture RED or GREEN.
- Delete invalid old theorem statements and proof bodies. Replace them with the
  strongest correct target statements using `sorry`; never weaken a statement
  to preserve a proof or remove a warning.
- Do not preserve obsolete structures through aliases, adapters, compatibility
  wrappers, re-exports, or parallel authorities.
- Do not introduce a mirrored TypeScript receipt type, allocation/provenance
  ledger, `Transport`/`inverseTransport` API, atlas/search fallback,
  redundancy-mismatch API, or per-primitive boundary theorem unless a final
  production theorem below directly requires it.
- Preserve ordered interfaces in the two places that own them: the inherited
  open replay/checked-theorem architecture and the final raw primitive-compiler
  adequacy theorem.
- Commit each validated task-owned slice. Preserve unrelated non-Lean worktree
  changes.

## Requested Outcomes and Owners

| ID | Required outcome | Final production owner |
|---|---|---|
| R1 | No Lambda/term/equation or relation-bubble authority remains; the calculus uses a nonempty base domain, recursive signatures, signature-indexed wires, and atom/ref/identity/cut content. | `VisualProof/Sig.lean`, `VisualProof/Model.lean`, `VisualProof/Diagram/Core.lean`, concrete diagram owners |
| R2 | Every actual higher-order production rule is sound in every full `Model`, and `applyStep_sound` exhaustively covers the exact production rule sum. | `VisualProof/Rule/Step.lean`, rule-family owners, `VisualProof/Rule/Soundness.lean` |
| R3 | The established generic proof-verification architecture remains sound over the new calculus. | `VisualProof/Proof/Replay.lean`, `VisualProof/Proof/Theorem.lean`, `VisualProof/Proof/Theory.lean` |
| R4 | Every supported ordinary typed HOL formula compiles to a diagram with equal denotation in every model/environment. | new production owners under `VisualProof/Formula/` |
| R5 | Every accepted direct relation substitution/grounding and comprehension/abstraction is constructively reproduced by a primitive relation-wire program with exact raw target and ordered-boundary correspondence. | new production owners under `VisualProof/Rule/WirePrimitive/` |

No task or public theorem may survive without mapping to R1–R5 or an immediate
dependency of one of these owners.

## Target Production Theorem Surface

Task 1 must state every applicable declaration below before proof work begins.

### R1 — Higher-order syntax and complete semantics

- Recursive `Sig := ι | rel (List Sig)` and its full recursive interpretation.
- A `Model` with a nonempty base carrier; every relational signature denotes
  the full Lean function space over recursively interpreted arguments.
- Intrinsic diagrams with signature-indexed local wires and only atom, ref,
  identity, and cut content. There is no separate relation-binder context.
- Concrete well-formedness, elaboration, denotation, exact occurrence/splice,
  open ordered boundary, and checked concrete isomorphism statements needed by
  R2–R5.
- Validity and entailment quantify over every full `Model`, not a canonical
  term model.

### R2 — Actual rule soundness

- Owning soundness theorems for production insertion/erasure,
  iteration/deiteration, double-cut introduction/elimination, vacuous-wire
  introduction/elimination, definitional fold/unfold, cited-theorem
  application, and every retained identity transformation.
- Owning soundness theorems for the primitive wire families from the July 29
  design: end merge/partition and delete/spawn; cut wrap/absorb; parallel
  split/fuse; arity shift/unshift; argument permute and duplicate/contract;
  argument drop/extend; apply/abstract formal; identity leaf/abstract; and any
  folded-ref leaf/abstract form required by the production rule inventory.
- `applyStep_sound` over the exact production `Step` sum, with one exhaustive
  constructor case delegating to each owning theorem.

### R3 — Preserved generic proof architecture

- `replay_sound` plus forward/backward specializations, structurally composing
  `applyStep_sound` across the dependent checked step chain while preserving
  the ordered open interface.
- `checkedTheorem_sound`, proving the implication between the exact registered
  left and right sides when their dual replays meet through the inherited
  ordered open concrete isomorphism.
- `verifiedTheory_sound`, proving every theorem in an ordered verified theory
  semantically valid, with citations restricted to the verified prior prefix.

### R4 — Formula semantic expressiveness

- A Lean source grammar corresponding to `src/formula/syntax.ts`: atom,
  conjunction, implication, and grouped existential/universal binders over
  recursive signatures, with typed lexical scope.
- Interpretation of source formulas in the same `Model` and environment used
  by diagram semantics.
- A total structural compiler for well-scoped formulas corresponding to
  `src/formula/diagram.ts`.
- Compiler well-formedness/elaboration, semantic preservation in every model,
  and the corollary that every supported formula has an equal-denoting diagram.

### R5 — Primitive derivability

- A structural primitive compiler from every accepted direct monolithic join
  input, terminating by a content/residual measure.
- `compiled_join_redundant`: the compiler succeeds and its primitive program's
  raw target is checked-concretely isomorphic to the raw direct-operation
  target, preserving every ordered boundary position and repeated alias.
- `compiled_sever_redundant`: the inverse-sequence result for every accepted
  direct sever input, with the same raw correspondence.
- Semantic corollaries derived from primitive-program soundness and the raw
  isomorphisms.

## Explicit Non-Requirements

- Porting any Lambda, term, equation, beta-eta, fusion/fission,
  congruence-at-ι, head-strip, inconsistent-cut, relation-bubble, binder-spine,
  or monolithic second-order comprehension theorem.
- Deductive completeness, Henkin/general models, parser correctness, UI
  correctness, library reconstruction, Frege arithmetic reconstruction, or a
  macro system.
- Making direct monolithic relation join/sever durable `Step` constructors;
  they remain specification operations used only by R5.
- Identity normalization in the statement, proof, landing, or import closure
  of R5.
- Insertion redundancy, ref-spawn/unfold conservativity, or additional
  primitive-completeness corollaries.
- Matching the discarded in-flight Lean module layout or helper APIs.

---

### Task 1: Replace the second-order declaration surface with the complete higher-order RED skeleton

**Requirements:** R1–R5.

**Files:**

- Create: `VisualProof/Sig.lean`, `VisualProof/Model.lean`.
- Replace target declarations in: `VisualProof/Diagram/Core.lean`,
  `VisualProof/Diagram/Semantics.lean`, `VisualProof/Diagram/Concrete/Core.lean`,
  `VisualProof/Diagram/Concrete/WellFormed.lean`, and the minimal concrete open,
  elaboration, occurrence, splice, and isomorphism owners required by R1–R5.
- Replace: `VisualProof/Rule/Step.lean`; create focused higher-order rule-family
  owners under `VisualProof/Rule/` and `VisualProof/Rule/WirePrimitive/`.
- Restate: `VisualProof/Rule/Soundness.lean`,
  `VisualProof/Proof/Replay.lean`, `VisualProof/Proof/Theorem.lean`, and
  `VisualProof/Proof/Theory.lean`.
- Create: minimal production owners under `VisualProof/Formula/`.
- Modify: `VisualProof.lean` and `lakefile.toml` only for production imports and
  targets.

**Interfaces:**

- Consumes: restored second-order owners at `6693b04`; the three governing
  specifications; production TypeScript `Sig`, `Formula`, and rule inventory.
- Produces: every final declaration in “Target Production Theorem Surface”
  elaborating with correct types; incomplete owning proofs are `sorry`.

- [ ] Inventory the restored public declarations and classify each as:
  structurally retained generic architecture, target declaration requiring a
  type-level restatement, or displaced second-order content.
- [ ] Replace `RelCtx := List Nat`, `RelVar`, Nat-only wire binding, and
  `LambdaModel` with recursive `Sig`, one signature-indexed binder discipline,
  and full `Model` interpretation.
- [ ] Replace the intrinsic and concrete item/node vocabularies with
  atom/ref/identity/cut and signature-indexed wires. Delete equation, term,
  bubble, binder, and relation-context declarations rather than adapting them.
- [ ] State the complete checked-diagram and semantic interfaces required by
  the final theorem surface. Remove any old proof body that no longer proves
  its strongest target statement.
- [ ] Replace the second-order `Step` sum with the exact production higher-order
  rule sum. Keep direct monolithic join/sever only as R5 specification
  operations outside `Step`.
- [ ] State every R2 rule-owned soundness theorem and exhaustive
  `applyStep_sound` with correct target quantification and `sorry` where
  incomplete.
- [ ] Restate the R3 replay, checked-theorem, and verified-theory declarations
  in the same dependency shape as the restored production owners, changing
  only types forced by R1/R2. Use `sorry` for invalidated proof bodies.
- [ ] State the R4 source formula, compiler, well-formedness, preservation, and
  expressiveness declarations.
- [ ] State the R5 compiler, join/sever redundancy, and semantic corollary
  declarations with universal accepted-input quantification and exact raw
  ordered-boundary correspondence.
- [ ] Delete restored fixture modules, redundant construction examples, and
  test theorems instead of converting them into target RED/GREEN evidence.
- [ ] Build the complete production umbrella. Record a declaration ledger in
  the task report mapping every remaining `sorry` to one final owner above.
- [ ] Commit the complete RED skeleton before proving any target theorem.

**Validation:** focused `lake env lean` on every changed owner; `lake build`;
`npm run formal:size`; exact scans proving no fixture/example/test theorem is
used as RED evidence; declaration ledger with no weakened or omitted owner.

---

### Task 2: Prove the higher-order semantic and checked-diagram core

**Requirements:** R1; prerequisite for R2–R5.

**Files:** target `Sig`, `Model`, `Diagram`, `Theory`, and concrete modules
created or restated by Task 1.

**Interfaces:**

- Consumes: Task 1 target types and RED semantic declarations.
- Produces: GREEN recursive signature interpretation, all-model denotation,
  checked diagram/elaboration, exact occurrence/splice, open ordered boundary,
  and concrete isomorphism results used by R2–R5.

- [ ] Prove every signature denotes a nonempty type and relational signatures
  denote full function spaces.
- [ ] Prove intrinsic denotation for atom/ref/identity/cut and local
  signature-indexed wires in every model/environment.
- [ ] Prove concrete well-formedness and elaboration preserve the target
  signature, port, scope, and boundary invariants.
- [ ] Port only generic context, occurrence, extraction, splice, renaming, and
  isomorphism arguments whose statements remain necessary to a final owner.
  Replace second-order binder/bubble cases; do not carry them as dead branches.
- [ ] Make every retained R1 theorem GREEN and delete unused semantic helpers
  outside the R2–R5 dependency closure.
- [ ] Commit the GREEN core.

**Validation:** focused owner builds; `lake build`; scans proving `Lambda`,
`equation`, `bubble`, `RelCtx`, and `RelVar` are absent from production
declarations; import/dependency evidence from each retained helper to R2–R5.

---

### Task 3: Prove every actual higher-order rule and exhaustive dispatcher sound

**Requirements:** R2.

**Files:** `VisualProof/Rule/Step.lean`, higher-order rule-family owners,
primitive rule owners, and `VisualProof/Rule/Soundness.lean`.

**Interfaces:**

- Consumes: Task 2 semantic core and Task 1 R2 declarations.
- Produces: GREEN rule-owned soundness for every production constructor and
GREEN exhaustive `applyStep_sound`.

- [ ] Prove structural insertion/erasure, iteration/deiteration, and double-cut
  soundness in the established contextual all-model style.
- [ ] Prove vacuous-wire, definitional fold/unfold, cited-theorem application,
  and every retained identity transformation sound. Identity normalization, if
  retained as a production transformation, owns a separate theorem.
- [ ] Prove the shared pointwise witness/context lemma licensed by full models
  for uniform wire primitives.
- [ ] Prove one owning production theorem for every primitive constructor,
  including both directions of each paired family and the actual gate matrix.
  A shared lemma is permitted only when every owning theorem directly cites it.
- [ ] Ensure public rule theorems quantify over checker-accepted production
  inputs and derive soundness; caller-supplied semantic truth, successful
  landing, inverse landing, or desired entailment is forbidden.
- [ ] Prove `applyStep_sound` by exhaustive pattern matching on the exact
  production `Step` sum. Its cases are the authoritative rule-coverage audit;
  do not create a second tag inventory to stand in for it.
- [ ] Commit the GREEN rule layer.

**Validation:** focused rule builds; `lake build`; `npm run formal:size`;
`#print axioms` for every rule owner and `applyStep_sound`; constructor-by-
constructor dependency audit with no obsolete second-order case.

---

### Task 4: Port the completed replay, checked-theorem, and verified-theory proofs

**Requirements:** R3; aggregates R2.

**Files:** `VisualProof/Proof/Replay.lean`, `VisualProof/Proof/Theorem.lean`,
`VisualProof/Proof/Theory.lean`.

**Interfaces:**

- Consumes: GREEN `applyStep_sound`, target checked open diagrams, ordered
  boundaries, definition semantics, and checked concrete isomorphism.
- Produces: GREEN `replay_sound`, directional replay corollaries,
  `checkedTheorem_sound`, and `verifiedTheory_sound`.

- [ ] Compare each Task 1 R3 declaration with its restored `6693b04` owner and
  record only the type substitutions forced by R1/R2.
- [ ] Prove replay sound by the restored structural induction: reflexivity for
  the empty program and composition of `applyStep_sound` with the induction
  hypothesis for a checked step.
- [ ] Preserve the registered ordered boundary through replay using the minimal
  checked-open interface already owned by the diagram core; do not introduce a
  general execution receipt or allocation/provenance layer.
- [ ] Prove `checkedTheorem_sound` from the exact registered sides, the forward
  and backward replay theorems, and their ordered endpoint concrete isomorphism.
- [ ] Prove checked theorem registration preserves context validity.
- [ ] Prove `verifiedTheory_sound` by the restored ordered-prefix induction and
  membership lookup argument.
- [ ] Confirm R3 depends on R2 and generic diagram semantics only—not formula
  expressiveness, R5, identity normalization, Lambda content, or a new checker
  architecture.
- [ ] Commit the restored GREEN proof chain.

**Validation:** focused proof-owner builds; structural diff/review against the
proof decomposition at `6693b04`; `lake build`; `#print axioms` for all R3
owners.

---

### Task 5: Formalize formula compilation and semantic expressiveness

**Requirement:** R4.

**Files:** production owners under `VisualProof/Formula/`; `VisualProof.lean`
for public imports.

**Interfaces:**

- Consumes: Task 2 `Sig`, `Model`, intrinsic/concrete diagrams, and denotation;
  `src/formula/syntax.ts` and `src/formula/diagram.ts` as correspondence
  authorities.
- Produces: GREEN formula compiler well-formedness, semantic preservation, and
  expressiveness theorems.

- [ ] Define the typed, well-scoped source formula grammar without parser spans,
  parser errors, source text, or UI behavior.
- [ ] Define source formula interpretation once in the same model/environment
  used by diagrams.
- [ ] Implement the total structural compiler: atoms map to applied relation
  wires; conjunction to same-region juxtaposition; implication to the existing
  cut construction; existential/universal groups to polarity-correct wire
  scopes.
- [ ] Prove the compiler constructs a well-formed/elaborable diagram and matches
  the production TypeScript AST cases.
- [ ] Prove semantic preservation by structural induction in every model and
  typed environment.
- [ ] Derive the expressiveness corollary: every supported well-scoped source
  formula has an equal-denoting diagram.
- [ ] Commit the GREEN formula capstone.

**Validation:** focused formula builds; AST-case correspondence audit; `lake
build`; `npm run formal:size`; `#print axioms` for preservation and
expressiveness. Do not claim deductive completeness or parser correctness.

---

### Task 6: Prove direct substitution and comprehension primitive-derivable

**Requirement:** R5.

**Files:** production compiler/program/adequacy owners under
`VisualProof/Rule/WirePrimitive/`; direct join/sever specification operations
under the narrowest appropriate rule namespace.

**Interfaces:**

- Consumes: Task 2 checked diagram/splice/isomorphism core and Task 3 primitive
  rule/program soundness.
- Produces: GREEN `compiled_join_redundant`, `compiled_sever_redundant`, and
  their semantic corollaries.

- [ ] Define direct monolithic join/sever as specification operations only;
  exclude them from the durable production `Step` sum.
- [ ] Implement the structural compiler by the July 29 residual cases: root-
  scoped internal wire, parallel root content, cut, empty residual, argument
  plumbing, fixed/ambient wire, formal application, identity, and folded ref.
- [ ] Prove termination from the specified lexicographic structural measure,
  with no caller-selected fuel.
- [ ] Prove `compiled_join_redundant` for every accepted direct join input. The
  theorem constructs compiler success and the raw checked concrete isomorphism;
  it does not assume either.
- [ ] Derive the accepted sever compiler by the reversed paired primitive
  sequence and prove `compiled_sever_redundant` without assuming an inverse
  landing.
- [ ] Prove positionwise ordered-boundary preservation for both raw adequacy
  theorems, including repeated aliases, without freezing a separate transport
  API into every primitive.
- [ ] Derive semantic corollaries solely from primitive-program soundness and
  raw isomorphism invariance.
- [ ] Audit both theorem declarations and import closures for absence of
  identity normalization, search, atlases, `redundancyMismatch`, assumed
  compiler output, or assumed inverse output.
- [ ] Commit the GREEN primitive-derivability capstone.

**Validation:** focused compiler/adequacy builds; termination and dependency
audit; `lake build`; `npm run formal:size`; `#print axioms` for both redundancy
owners and semantic corollaries.

---

### Task 7: Delete displaced second-order and non-authoritative infrastructure

**Requirements:** R1–R5 minimality.

**Files:** complete `VisualProof/` dependency closure and `VisualProof.lean`.

**Interfaces:**

- Consumes: final GREEN owners from Tasks 2–6.
- Produces: the smallest production library containing exactly the target
  calculus and direct dependencies of R1–R5.

- [ ] Compute the declaration/import closure of every final production owner.
- [ ] Delete the entire `VisualProof/Lambda/` subtree and every term/equation,
  beta-eta, fusion/fission, head-strip, inconsistent-cut, or Lambda-specific
  concrete matcher/isomorphism module.
- [ ] Delete relation-bubble, `RelCtx`/`RelVar`, binder-spine, monolithic
  comprehension, and second-order comprehension-soundness modules.
- [ ] Delete all fixture, example-only, source-substring correspondence,
  redundant tag, atlas/search, receipt/allocation/provenance, and compatibility
  modules outside the final dependency closure.
- [ ] Delete artificially weakened, extra redundancy, insertion redundancy,
  and ref-conservativity theorem statements rather than proving unrequested
  results.
- [ ] Preserve the generic R3 proof owners and ordered theorem interface.
- [ ] Minimize `VisualProof.lean` and Lake targets to production owners only.
- [ ] Commit the clean target library.

**Validation:** dependency closure report; absent-source scans for every
displaced authority; clean `lake build`; `npm run formal:size`; no Lean fixture,
redundant `example`, `#check`, or test theorem used for RED/GREEN.

---

### Task 8: Final conformance and completion audit

**Requirements:** R1–R5.

**Files:** all final production owners, plan, goal charter, board, and task
reports.

**Interfaces:**

- Consumes: committed outputs of Tasks 1–7.
- Produces: direct evidence that the restored second-order baseline has been
  coherently converted and no discarded implementation model remains.

- [ ] Map every retained public theorem and module to R1–R5 or an immediate
  dependency. Delete anything without a valid owner.
- [ ] Verify the final theorem surface is GREEN: no `sorry`, `admit`, project
  `axiom`, or artificially weakened replacement remains.
- [ ] Print/check axioms for every actual rule owner, `applyStep_sound`,
  `replay_sound`, `checkedTheorem_sound`, `verifiedTheory_sound`, formula
  preservation/expressiveness, both primitive redundancy theorems, and their
  semantic corollaries.
- [ ] Verify exhaustive rule constructor coverage and absence of Lambda,
  term/equation, bubble, second-order comprehension, fixtures, monolithic
  durable join/sever, and discarded in-flight authority paths.
- [ ] Verify R5's declarations and complete import closure are independent of
  identity normalization.
- [ ] Run the authoritative gates:

  ```bash
  lake clean
  lake build
  npm run formal:size
  npm test
  npm run typecheck
  npm run e2e
  git diff --check
  git status --short
  ```

- [ ] Repair every fixable in-repository failure, rerun until green, append
  conformance to the implementation foundation record, and commit the audit.

## Completion Oracle

Completion requires direct kernel evidence for all five outcomes:

1. the production Lean calculus contains recursive signature-indexed wires and
   atom/ref/identity/cut content, with no Lambda, term/equation, or bubble
   authority;
2. every actual production rule is sound in all full models and
   `applyStep_sound` exhaustively covers the exact rule sum;
3. the preserved replay, checked-theorem, and verified-theory chain is GREEN
   over the new calculus;
4. every supported ordinary HOL formula has a semantically equal diagram; and
5. every accepted direct relation substitution/comprehension has a checked
   primitive program with the exact raw target and ordered boundary up to
   checked concrete isomorphism, independently of identity normalization.

The temporary in-flight backup, historical task receipts, old checkmarks,
passing source scans, fixture results, or absence of `sorry` in weakened
statements do not satisfy this oracle.
