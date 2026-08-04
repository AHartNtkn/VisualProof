# Higher-Order Diagram Calculus Lean Completion Plan

> **Execution:** Use `superpowers:executing-plans` or
> `superpowers:subagent-driven-development`. Lean development follows the global
> theorem-driven RED/GREEN rule: RED is the owning production declaration
> elaborating with `sorry`; GREEN is that same declaration proved without
> `sorry`. Do not create fixture modules, redundant examples, `#check`
> declarations, or test theorems to manufacture either state.

**Goal:** Finish the Lean conversion of the completed second-order diagram
calculus into the actual higher-order, signature-indexed-wire calculus; prove
the actual higher-order rules sound in the established all-models style; prove
the existing ordinary formula compiler semantically preserving and expressive;
and prove direct relation substitution/comprehension constructively derivable
from the primitive relation-wire rules.

**Architecture:** Preserve the completed second-order formalization's generic
semantic verification chain: rule-owned soundness, exhaustive
`applyStep_sound`, replay soundness, checked-theorem soundness, and ordered
verified-theory soundness. Port those declarations and proof shapes to the
higher-order types and all-model semantics without retaining second-order rule
content or inventing a replacement receipt/transport architecture. The source-
formula compiler and primitive derivability compiler own their additional
requested production theorems.

**Tech stack:** Lean 4/Lake, the repository's existing TypeScript formula and
kernel sources as correspondence authorities, Node.js/Vitest for mechanical
cross-language checks already justified by the formalization.

## Controlling requirements and provenance

| ID | Required outcome | Controlling evidence |
|---|---|---|
| R1 | Remove the Lambda-expression and beta-eta formalization rather than porting it. | Original refactor request; `2026-07-25-zero-signature-hol-redesign-design.md`, Sections 1 and 3. |
| R2 | Replace second-order quantifier bubbles by recursive-signature wires and prove every actual higher-order rule sound against complete/all-model semantics in the established style. | Original refactor request; `2026-07-22-signature-indexed-wires-design.md`; zero-signature redesign Section 3; latest user clarification. |
| R3 | Formalize semantic preservation/coverage of the existing ordinary formula-to-diagram compiler. This is language expressiveness, not deductive completeness. | Zero-signature redesign Section 4; existing `src/formula/syntax.ts` and `src/formula/diagram.ts`; latest user clarification. |
| R4 | Prove direct relation substitution/grounding and comprehension/abstraction reproducible by primitive relation-wire steps. | `2026-07-29-primitive-wire-quantifier-rules-design.md`, especially “Completeness” and “Lean strategy”; latest user clarification. |
| A1 | Preserve the completed generic rule/replay/theorem/theory soundness architecture, adapting only types and dependencies displaced by the higher-order conversion. | Original instruction to stay as close as possible to the completed second-order formalization; production reference commit `6693b04`; latest user clarification. |

No task may be added without citing one of R1–R4/A1 or demonstrating a direct
logical dependency of an R1–R4/A1 production theorem. Implementation convenience, an incumbent module,
a former plan checkbox, a TypeScript receipt shape, or an existing helper is
not controlling evidence.

## Explicit non-requirements

The following are not completion criteria and must not be rebuilt or promoted
into theorem statements:

- second-order Lambda, term, equation, bubble, beta-eta, fusion/fission,
  head-strip, inconsistent-cut, or monolithic bubble-comprehension theorems;
- deductive completeness, Henkin semantics, normalization of source formulas,
  parser correctness, UI correctness, theory-library reconstruction, or a
  macro system;
- a replacement replay, theorem-checker, or verified-theory architecture when
  the established second-order proof shape can be ported;
- Lean/TypeScript receipt representation equality;
- a `Transport`, `inverseTransport`, atlas, search, redundancy-mismatch,
  provenance, allocation, or interface API as an outcome in its own right;
- per-primitive transported-boundary theorems;
- insertion redundancy or ref-spawn/unfold conservativity as additional
  primitive-completeness theorems;
- identity normalization in the statement, proof, landing, or boundary
  correspondence of direct substitution/comprehension adequacy.

Ordered-boundary preservation remains required in the two places where the
established specifications already put it: the inherited open replay/checked-
theorem interface and R4's raw primitive-compiler correspondence. This does
not require matching TypeScript receipts, inverse transports, or per-primitive
boundary APIs.

The required aggregate `applyStep_sound` theorem closes R2 over the exact
production rule sum. It establishes exhaustive rule coverage without requiring
proof replay, theorem checking, theory verification, or theorem boundaries.

Identity normalization may retain its own soundness theorem if it is an actual
production transformation. It remains a separate mechanism and may not be used
to weaken or finish the R4 compiler theorem.

## Required final production theorem surface

Task 1 must make every applicable declaration below exist and elaborate before
new proof work continues. Existing declarations may be retained only after
their statements are checked against this surface.

### Higher-order rule soundness (R2)

- Soundness of the actual structural operations: insertion/spawn, erasure,
  iteration, deiteration, double-cut introduction/elimination, vacuous-wire
  introduction/elimination, definitional fold/unfold, and cited-theorem
  application.
- Soundness of the actual identity transformations retained by production.
- Soundness of generic signature-indexed wire partition/merge.
- Soundness of every durable primitive family:
  ends delete/spawn, cut wrap/absorb, parallel split/fuse, arity
  shift/unshift, argument permute, duplicate/contract, drop/extend,
  apply/abstract formal, identity leaf/abstract, and folded-ref
  leaf/abstract.
- `applyStep_sound` over the exact durable production rule sum, exhaustively
  delegating every constructor to its owning rule theorem.

### Generic proof verification (A1)

- `replay_sound` and its forward/backward specializations, structurally
  composing `applyStep_sound` over the dependent checked step chain while
  preserving the ordered open interface.
- `checkedTheorem_sound`, deriving the implication between the exact registered
  left and right sides from their dual replays and ordered endpoint concrete
  isomorphism.
- `verifiedTheory_sound`, deriving every registered theorem's semantic validity
  from ordered definitions and a theorem chain restricted to the verified
  prior prefix.

### Direct substitution/comprehension derivability (R4)

- `compiled_join_redundant`: every accepted direct relation-content join
  produces an accepted primitive program whose raw target is checked-concretely
  isomorphic to the raw direct-operation target, preserving every ordered
  boundary position and repeated alias.
- `compiled_sever_redundant`: the corresponding theorem for every accepted
  direct relation-content sever.
- Semantic corollaries deriving the direct operations from primitive-program
  soundness. These corollaries quantify over accepted direct-operation inputs,
  not already-successful compiler outputs.

### Formula compiler semantics and expressiveness (R3)

- A Lean source-formula grammar corresponding to the production TypeScript
  `Formula` AST, with typed lexical binding and interpretation in the same
  `Model` used by diagrams.
- A total structural compiler on well-scoped typed formulas.
- A well-formedness/elaboration theorem for its output if the compiler
  constructs a raw concrete diagram.
- One semantic preservation theorem: compiling a source formula yields a
  diagram with the same truth value in every `Model` and environment.
- The expressiveness corollary: every supported source formula has such a
  diagram. This is the requested semantic completeness claim.

## Current evidence, not inherited completion

- The Lambda subtree and concrete bubble authority appear absent.
- Recursive signatures, all-model semantics, and many actual rule-soundness
  theorems are present and currently build.
- The two universal primitive compiler redundancy declarations and their
  semantic corollaries are RED, not GREEN.
- The existing aggregate `applyStep_sound` declaration is part of R2 and must
  be revalidated against the exact production rule sum. Replay,
  checked-theorem, and verified-theory soundness were present in the completed
  second-order production tree at `6693b04` and are part of A1.
- Commit `38f3529` deleted all three former proof modules during the semantic-
  core replacement. Commit `acbb107` rebuilt only replay using new receipt,
  allocation, provenance, and transport structures; it did not restore the
  checked-theorem or verified-theory owners.
- The formula semantic preservation/coverage formalization is absent.
- Historical task receipts, prior checkmarks, fixture-based validation, and
  absence of `sorry` in an artificially weakened theorem do not establish
  completion under this plan.

No task below starts as complete. Each must be revalidated against its owning
production theorem and the provenance table.

---

### Task 1: Establish the complete honest RED skeleton

**Requirement:** R1–R4, A1.

**Primary files:**

- Modify only the current owners under `VisualProof/Diagram` and
  `VisualProof/Rule` needed to state the final theorem surface.
- Restore the minimal generic proof owners under `VisualProof/Proof/` using
  commit `6693b04` as the structural reference.
- Create the minimal Lean formula modules under `VisualProof/Formula/`.
- Modify `VisualProof.lean` only for production imports.

- [ ] Inventory every current public theorem and classify it as an exact final
  obligation, a private helper directly used by one, or displaced.
- [ ] State every missing production declaration from “Required final
  production theorem surface” with its strongest correct quantification and
  `sorry`. In particular, retain or restate honest `applyStep_sound`,
  `replay_sound`, `checkedTheorem_sound`, and `verifiedTheory_sound`, and add
  formula compiler, formula preservation, and formula expressiveness
  declarations.
- [ ] Keep the accepted-input `compiled_join_redundant` and
  `compiled_sever_redundant` declarations. They must produce the compiler
  success equality and raw checked concrete isomorphism with direct
  positionwise ordered-boundary preservation.
- [ ] Delete artificially weakened, obsolete, or non-required production
  declarations, including insertion redundancy.
- [ ] Delete invalid proofs together with their old statements; do not preserve
  them under aliases or adapters. Delete `ProofStep.receipt` and its plan-only
  hierarchy unless an R1–R4/A1 production theorem directly requires that exact
  structure. Correct statements remain RED with `sorry`.
- [ ] Confirm the complete production skeleton elaborates. The expected RED
  evidence is exactly the `sorry` warnings on incomplete owning declarations.
  No fixture or example is permitted.
- [ ] Commit the skeleton before proving another theorem.

**Validation:** focused `lake env lean` on every changed owner, `lake build`,
`npm run formal:size`, and a declaration ledger mapping each `sorry` to one
final theorem above.

---

### Task 2: Conform the higher-order semantic and checked-diagram core

**Requirement:** R1, R2; prerequisite for R3/R4/A1.

- [ ] Prove the live syntax contains recursive signatures, signature-indexed
  wire binding, atom/ref/identity/cut content, and no Lambda term, equation,
  relation-bubble, or second-order binder authority.
- [ ] Prove `Model` gives a nonempty individual carrier and full recursively
  interpreted higher-order function spaces, and diagram validity quantifies
  over every such model.
- [ ] Revalidate concrete well-formedness, elaboration, open ordered boundaries,
  definitions, exact occurrence validation, splice semantics, and concrete
  isomorphism only to the extent cited by the final R2–R4/A1 theorems.
- [ ] Reuse green current results only where their statements are
  substantively identical. Delete second-order-specific lemmas and any
  plan-created generalization not cited by a final owner.
- [ ] Prove the current durable Lean rule inventory covers the actual
  production TypeScript rule discriminants. This is a validation of R2
  coverage, not a second tag authority or a requirement to mirror payload
  representations.
- [ ] Make every retained semantic-core theorem GREEN.

**Validation:** `lake build`; exact source scans for displaced Lambda/bubble
declarations; direct import/dependency evidence from each retained helper to a
final theorem owner.

---

### Task 3: Prove every actual higher-order rule sound

**Requirement:** R2.

- [ ] Revalidate or prove the structural rule theorems: production spawn and
  insertion forms, erasure, iteration/deiteration, double cuts, vacuous wires,
  fold/unfold, and cited theorem replacement.
- [ ] Revalidate or prove every actual identity transformation. Keep its
  normalization theorem separate from direct substitution/comprehension
  compiler adequacy.
- [ ] Revalidate or prove generic signature-indexed wire partition/merge over
  the weakest semantic structure that supports the rule.
- [ ] Revalidate or prove all primitive content, argument, formal, identity,
  and folded-ref pairs. A shared witness lemma is permitted only if these
  owning production theorems directly cite it.
- [ ] Ensure each public theorem quantifies over the production-accepted rule
  input and derives soundness; caller-supplied semantic truth, successful
  landing, transport, or inverse evidence is forbidden.
- [ ] Ensure every actual rule has its own owning soundness theorem.
- [ ] Make `applyStep_sound` GREEN by exhaustive delegation over the exact
  production rule sum. Its proof must expose any missing or obsolete rule
  constructor rather than relying on a second tag inventory.

**Validation:** focused owner builds followed by `lake build` and
`npm run formal:size`; theorem dependency inspection proving
`applyStep_sound` covers all durable rule constructors exactly once and no
obsolete second-order rule is covered.

---

### Task 4: Prove primitive derivability of direct substitution and comprehension

**Requirement:** R4.

- [ ] Keep the direct relation-content join/sever implementations solely as
  specification operations. They are not durable proof-step constructors.
- [ ] Audit the structural compiler against the design cases: root-scoped
  internal wire, parallel root content, cut, empty residual, argument
  plumbing, fixed/ambient wire, formal application, identity, and folded ref.
  Retain only helpers directly cited by the constructive adequacy proof.
- [ ] Prove termination from a structural measure with no caller-selected
  fuel.
- [ ] Prove `compiled_join_redundant` from every accepted direct join input.
  The theorem itself constructs the successful primitive program and returns
  its exact raw isomorphism to the raw direct target.
- [ ] Derive sever by the checked inverse primitive sequence and prove
  `compiled_sever_redundant` from every accepted direct sever input.
- [ ] State ordered-boundary preservation representation-independently and
  directly in both final theorems. Preserve order and repeated aliases.
- [ ] Prove the semantic corollaries solely from primitive-program soundness
  and the raw isomorphisms.
- [ ] Confirm neither theorem nor its import closure references identity
  normalization, search, atlas selection, `redundancyMismatch`, an assumed
  compiled result, or an assumed inverse landing.

**Validation:** focused compiler builds, theorem dependency/import audit,
`lake build`, and `npm run formal:size`.

---

### Task 5: Restore the established replay, theorem, and theory soundness chain

**Requirement:** A1; aggregates R2.

**Structural authority:** `VisualProof/Proof/Replay.lean`,
`VisualProof/Proof/Theorem.lean`, and `VisualProof/Proof/Theory.lean` at commit
`6693b04`.

- [ ] Compare each former production declaration with the new higher-order
  types. Record the minimal substitutions forced by recursive signatures,
  `Model`, `CheckedDefinitions`, the new `ProofStep`, and the current checked-
  diagram/concrete-isomorphism interfaces. Preserve every unaffected theorem
  meaning and proof decomposition.
- [ ] Rebuild the dependent proof program and replay operation in the former
  shape: one checked step followed by a continuation indexed by its actual
  result. Preserve the ordered open interface needed by theorem sides. Do not
  make allocation totals, provenance, mirrored receipts, or a general
  transport API part of the proof object unless a retained A1 theorem cannot
  be stated from the checked diagram and isomorphism interfaces without it.
- [ ] Make `replay_sound` and its forward/backward specializations GREEN by
  structural composition of `applyStep_sound` in every `Model`. Do not add a
  second soundness assumption or rule inventory.
- [ ] Restore `CheckedTheorem` with the exact registered left and right sides,
  their forward/backward replays, and their ordered endpoint concrete
  isomorphism. Make `checkedTheorem_sound` GREEN by the same dual-replay
  composition as the former proof.
- [ ] Restore ordered theorem registration and `VerifiedTheorems`: definitions
  are already dependency ordered, and each theorem may cite only the verified
  prior theorem prefix. Make `verifiedTheory_sound` GREEN by the same induction
  and lookup argument as the former proof.
- [ ] Confirm the restored theorem meanings contain no Lambda-era carrier,
  term, equation, bubble, beta-eta, or second-order rule content. Confirm the
  proofs do not depend on R4 primitive compiler adequacy or identity
  normalization.

**Validation:** focused builds of the three proof owners; declaration and proof-
dependency comparison with `6693b04`; `#print axioms` for `replay_sound`,
`checkedTheorem_sound`, and `verifiedTheory_sound`; `lake build`; and
`npm run formal:size`.

---

### Task 6: Formalize formula compilation and semantic expressiveness

**Requirement:** R3.

**Correspondence authority:** `src/formula/syntax.ts`,
`src/formula/diagram.ts`, and the graph constructors they call.

- [ ] Define the production source `Formula` grammar in Lean with typed lexical
  binding corresponding to the TypeScript AST: atom, conjunction,
  implication, and existential/universal binder groups over recursive
  signatures. Formalize the AST/compiler boundary, not parsing spans, parser
  errors, UI behavior, or text parsing.
- [ ] Define source-formula interpretation in the same `Model` and typed
  environment used by diagram semantics.
- [ ] Define the structural compiler corresponding to the existing production
  translation: atoms, same-region conjunction, cut-based implication, and
  polarity-correct wire scopes for quantifiers.
- [ ] Prove the compiler constructs a well-formed/elaborable diagram. If the
  Lean compiler targets intrinsic diagrams directly, prove the exact
  correspondence needed to the production concrete construction rather than
  inventing a second compiler authority.
- [ ] Prove the owning semantic preservation theorem by structural induction
  on the source formula.
- [ ] Derive the expressiveness theorem: every supported well-scoped formula
  has a diagram with equal denotation in every model/environment.
- [ ] Do not claim proof-system completeness, completeness for syntax absent
  from the production `Formula` AST, or correctness of the TypeScript parser.

**Validation:** focused formula module builds, correspondence scan against the
TypeScript AST cases, `lake build`, and `npm run formal:size`.

---

### Task 7: Delete displaced and plan-only infrastructure

**Requirement:** R1–R4/A1 minimality and the prohibition on extra requirements.

- [ ] Compute the declaration and import closure of the final production
  theorems. Classify every remaining Lean module as a final owner or a helper
  directly referenced by one.
- [ ] Delete all unreferenced fixture, atlas, search, transport, inverse,
  redundancy-mismatch, generalized-shape, allocation, provenance, and receipt
  modules/declarations created only to satisfy the displaced plan. Do not keep
  aliases, adapters, compatibility wrappers, or umbrella imports.
- [ ] Preserve the restored A1 replay, checked-theorem, verified-theory, and
  ordered-interface owners. Delete parallel or replacement proof architectures
  and any allocation, provenance, receipt, or transport layer not directly
  required by A1, R2, or R4.
- [ ] Delete obsolete second-order-specific modules/declarations and any
  invalid old proofs not already removed by Task 1.
- [ ] Delete theorem statements for insertion redundancy and ref
  conservativity unless they are ordinary soundness lemmas directly required
  by a live production rule. Their former status as completion-plan tasks is
  not authority.
- [ ] Ensure no fixture module, redundant example, or test theorem remains for
  Lean RED/GREEN development.
- [ ] Minimize `VisualProof.lean` to the production library and required public
  theorem owners.

**Validation:** dependency closure report; absent-path/source scans; clean
`lake build`; `npm run formal:size`.

---

### Task 8: Final conformance and completion audit

**Requirement:** R1–R4, A1.

- [ ] Verify the provenance table against the final source and prove every
  retained public theorem/task maps to a requested outcome or direct
  prerequisite.
- [ ] Verify the complete final theorem surface is GREEN: no `sorry`, `admit`,
  project `axiom`, or artificially weakened replacement remains.
- [ ] Print/check axioms for every actual rule-owned soundness theorem,
  `applyStep_sound`, `replay_sound`, `checkedTheorem_sound`,
  `verifiedTheory_sound`, primitive join/sever adequacy and semantic
  corollaries, formula semantic preservation, and formula expressiveness.
- [ ] Verify exact actual-rule coverage and absence of Lambda, bubble,
  second-order comprehension, fixture, identity-retarget, monolithic durable
  step, and plan-only authority paths.
- [ ] Verify primitive compiler adequacy's declaration and import closure are
  independent of identity normalization.
- [ ] Run the authoritative full gates:

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

- [ ] Repair in-repository failures, rerun until green, append conformance to
  the implementation foundation record, and commit only task-owned work.

## Completion oracle

The work is complete only when all four requested outcomes are directly
proved:

1. no Lambda or quantifier-bubble formalization remains;
2. every actual higher-order rule is sound in complete/all-model semantics,
   `applyStep_sound` exhaustively covers the exact production rule sum, and
   the established replay/checked-theorem/verified-theory chain is sound;
3. the existing source-formula compiler has a kernel-checked semantic
   preservation/expressiveness theorem; and
4. every accepted direct relation substitution/comprehension is reproduced by
   a checked primitive relation-wire program with exact raw target and ordered
   boundary correspondence, independently of identity normalization.

Passing tests, matching names, prior receipts, or completion of only the
primitive compiler does not satisfy this oracle.
