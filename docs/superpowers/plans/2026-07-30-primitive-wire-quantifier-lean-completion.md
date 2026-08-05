# Macro-Free Higher-Order Diagram Calculus Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the completed second-order Lean formalization into the requested signature-indexed higher-order diagram calculus, prove every actual primitive rule sound, preserve meta-level derivation/result soundness without first-class citation, prove higher-order formula semantic expressiveness, and prove primitive derivability of direct substitution and comprehension.

**Architecture:** The authoritative formal core has recursive `Sig`, full-model assignments, and atom/identity/cut diagrams. Definitions, refs, fold/unfold, and citation are a separate macro system and do not appear in Lean's diagram content or primitive `Step`; checked theorems and verified theories remain meta-level certificates built only from primitive replay. Every production owner is first classified against both the complete second-order implementation at `2bddfe4` and the abandoned signature-indexed implementation at `/tmp/vpa-current-lean-code-20260804-XO7NPu`. Completed predecessor constructions and proofs are ported; greenfield work is permitted only for an exact responsibility absent or honestly unfinished in both.

**Tech Stack:** Lean 4.30, Lake, Node.js repository gates, GoalBuddy persistent state, Git.

## Global Constraints

- The affected Lean system is macro-free: no `.ref`, `DefinitionEnv`, `VerifiedDefinitions`, definition interpretation, ref rules, fold/unfold, or citation step.
- A theorem is never a first-class diagram-calculus input. `TheoremSchema`, `CheckedTheorem`, and `VerifiedTheory` are meta-level statements and certificates only.
- Intrinsic and concrete content is exactly atom, identity, and cut.
- Equality formulas are well typed only at one shared recursive signature.
- Formula completeness is existential semantic expressiveness; it selects no public compiler.
- Direct substitution/comprehension completeness is existential primitive derivability, independent of identity normalization, canonicalization, compilation, and macros. Identity leaf/abstraction remain two of the nineteen relation-wire primitives needed for identity-node content; they are not identity-normalization rules.
- Exactly three explicit identity equivalences exist: degeneracy, one-point collapse, and same-region fusion. There is no Lean canonicalizer.
- Use theorem-driven Lean RED/GREEN. RED is the owning production theorem with `sorry`; GREEN is that theorem with a kernel-checked proof.
- Definitions never use `sorry`. Do not create fixture modules, redundant `example`, `#check`, or synthetic test theorems.
- Preserve mathematical kernels from the temporary backup only when a current production owner directly requires the same responsibility; never restore receipts, normalization, provenance, transport, search, atlases, or fixtures.
- Before modifying any production declaration or adding any proof helper, record
  its exact SO and higher-order predecessor declarations, the mathematical
  kernel retained, the representation-only cases to remove, and the target
  current owner. Apply the same comparison retrospectively to already-GREEN
  current owners: passing compilation does not establish that independent
  reconstruction was necessary or equivalent. A failed port must identify the
  exact predecessor theorem and the incompatible hypothesis or conclusion
  before any new construction is introduced.
- Audit and port the complete mathematical dependency chain, not only the
  terminal theorem with the matching name. Raw candidates, factorization,
  compiler simulation, semantic ledgers, inverse constructions, and denotation
  lemmas in either predecessor remain completed work even when their historical
  wrapper module is excluded. Missing current lower layers must be adapted from
  that work; they are not greenfield helpers.
- Commit each validated task-owned slice and keep the worktree clean.

## Predecessor Provenance Gate

The durable owner-by-owner audit is
`docs/goals/primitive-wire-quantifier-lean-completion/notes/temporary-backup-salvage-map.md`.
Its controlling classifications are:

| Responsibility | Classification |
|---|---|
| Current signature/model/intrinsic semantics, checked graph core, selection, removal, separately audited non-iteration operation definitions, vacuous-wire soundness, direct relations, and exhaustive dispatcher | Retain GREEN; iteration-owned declarations require the replacement below |
| Canonical extraction | Port the SO carrier layout; already GREEN in the current tree |
| Structural insertion, erasure, iteration/deiteration, and double-cut soundness | Select one coherent completed predecessor per owner. Iteration uses the completed abandoned signature-indexed HO extraction, raw-splice/insertion, factorization, equivalence, and soundness chain. The SO tree supplies localized current-representation facts only. The current `copySelection` operation is a displaced bespoke replacement. Other structural owners retain their separately audited bases. |
| Atom spawn and identity insertion soundness | Adapt the completed higher-order structural-insertion proof |
| Three explicit identity-equivalence soundness owners | Port the completed higher-order canonicalizer transformation proofs without the canonicalizer |
| Nineteen wire-primitive soundness owners | Port the completed higher-order primitive owners |
| Replay, checked-theorem, verified-theory, and primitive-program soundness | Mechanical ports of completed predecessor inductions |
| Formula semantic expressiveness | Genuinely new theorem; neither predecessor has this responsibility |
| Direct substitution/comprehension adequacy | Port the completed higher-order residual, plumbing, inversion, termination, and landing cases as proof-local existential witnesses, not compiler definitions; prove the current-input bridge (including empty alias-identity requests), failure-free totality, and exact landing |

---

## Required Outcome Matrix

| ID | Required outcome | Direct owners |
|---|---|---|
| R1 | Recursive signatures, full models, and macro-free atom/identity/cut diagrams with checked concrete semantics | `VisualProof/Sig.lean`, `VisualProof/Model.lean`, `VisualProof/Diagram/**` |
| R2 | Every actual primitive rule is all-model sound and exact `Step` coverage is exhaustive | `VisualProof/Rule/**` |
| R3 | Primitive derivations replay soundly; checked theorem and verified theory certificates are sound without citation | `VisualProof/Proof/**` |
| R4 | Every typed higher-order formula has some semantically equivalent diagram | `VisualProof/Formula/**` |
| R5 | Every valid direct substitution/comprehension has some primitive derivation with exact raw ordered-boundary correspondence | `VisualProof/Rule/WirePrimitive/**` |

No declaration, module, test, or completion criterion survives without mapping to R1–R5 or being an immediate dependency of one of these owners.

### Task 1: Rebuild the complete macro-free RED skeleton

**Files:**
- Modify: `VisualProof/Diagram/Core.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof/Diagram/Context.lean`
- Modify: `VisualProof/Diagram/Concrete/**`
- Delete the obsolete typed module: `VisualProof/Diagram/Concrete/Elaboration/Simulation.lean`, only after retaining every generic semantic-simulation responsibility required by current structural soundness
- Delete: `VisualProof/Theory/Definition.lean`
- Modify: `VisualProof/Theory/Semantics.lean`
- Modify: `VisualProof/Rule/Core.lean`
- Modify: `VisualProof/Rule/Operations.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Structural/**`
- Modify: `VisualProof/Rule/WirePrimitive/**`
- Modify: `VisualProof/Proof/**`
- Modify: `VisualProof/Formula/Soundness.lean`
- Modify: `VisualProof.lean`
- Modify: `docs/goals/primitive-wire-quantifier-lean-completion/**`

**Interfaces:**
- Consumes: recursive `Sig`, full `Model`, existing checked concrete graph and primitive operation kernels.
- Produces: complete macro-free definitions and the complete honest RED theorem surface for R1–R5.

- [x] **Step 1: Replace intrinsic diagram definitions with the exact content vocabulary**

  Define unindexed intrinsic owners:

  ```lean
  mutual
    inductive Region : List Sig → Type
      | mk {context} (locals : List Sig)
          (items : ItemSeq (context ++ locals)) : Region context
    inductive Item : List Sig → Type
      | atom {arguments} (head : RelationWire context arguments)
          (values : Vars context arguments) : Item context
      | identity {signature} (ports : List (Var context signature)) : Item context
      | cut (body : Region context) : Item context
    inductive ItemSeq : List Sig → Type
      | nil : ItemSeq context
      | cons (head : Item context) (tail : ItemSeq context) : ItemSeq context
  end
  ```

  Remove the obsolete `definitions` parameter from `Region`, `Item`, `ItemSeq`, `OpenDiagram`, `ConcreteDiagram`, `OpenConcreteDiagram`, and checked wrappers.

- [x] **Step 2: Replace diagram semantics with direct full-model semantics**

  Make `denoteRegion`, `denoteItem`, `denoteItemSeq`, and `denoteOpen` accept only `model`, diagram/context data, and assignments. Delete `DefinitionEnv` and every ref branch. Preserve existential local-wire semantics and the equality semantics of identity ports.

- [x] **Step 3: Migrate concrete graph infrastructure**

  Remove `CNode.ref` and every ref case from port typing, well-formedness, occurrence, extraction, removal, copying, splicing, renaming, elaboration, and concrete isomorphism. The old `Concrete/Elaboration/Simulation.lean` file is not definition-environment congruence: it owns the generic graph-to-intrinsic semantic-simulation architecture used by structural and modal soundness. Delete its obsolete lambda/binder/named/definition representation, but port or specialize every simulation responsibility directly required by a current owner.

- [x] **Step 4: Replace the primitive rule vocabulary with the exact 31 constructors**

  Define `RuleKind` and `RuleInput` without `ProofContext`:

  ```lean
  inductive RuleKind
    | atomSpawn | identityInsert
    | identityDegeneracy | identityCollapse | identityFusion
    | erasure | iteration | deiteration | doubleCutIntro | doubleCutElim
    | vacuousIntro | vacuousElim
    | wireJoin | wireSever | cutWrap | cutAbsorb
    | parallelSplit | parallelFuse | endsDelete | endsSpawn
    | arityShift | arityUnshift | argPermute
    | argDuplicate | argContract | argDrop | argExtend
    | applyFormal | abstractFormal | identityLeaf | identityAbstract
  ```

  Delete `refSpawn`, cited theorem, unfold/fold, `refLeaf`, and `refAbstract` from input types, operations, interfaces, `Step`, soundness declarations, primitive tags, programs, and adequacy inputs.

  Define the direct-adequacy predicate as the nineteen wire primitives plus
  vacuous introduction/elimination. It includes `identityLeaf` and
  `identityAbstract`; it excludes identity insertion and the three identity
  normalization equivalences.

- [x] **Step 5: Rebuild meta-level proof certificates without registries or citation**

  Keep `TheoremSchema` as an unindexed meta-level pair of checked open diagrams with an ordered interface. Define primitive `Proof.Program` without context; define `CheckedTheorem (schema : TheoremSchema)` from two primitive programs and a `CheckedIso`; define `VerifiedTheorems` as a collection of independently checked schemas, never a prior-prefix context. Do not retain the old phantom definition-signature index on any of these declarations.

  ```lean
  structure CheckedTheorem (schema : TheoremSchema) where
    leftMeet rightMeet : CheckedOpenDiagram
    leftReplay : Program .forward schema.left leftMeet
    rightReplay : Program .backward schema.right rightMeet
    meet : CheckedIso leftMeet rightMeet
  ```

  Delete registration, context validity, definitions, and prior-citation fields.

- [x] **Step 6: State the exact RED theorem surface**

  Retain GREEN proofs whose statements survive definitionally or migrate mechanically. Use `sorry` only for the final owning statements whose proofs remain incomplete: all actual rule owners, exhaustive `applyStep_sound`, replay/check/theory soundness, formula expressiveness, primitive program soundness, and two direct adequacy theorems.

- [x] **Step 7: Compile and audit the skeleton**

  Run focused `lake env lean` checks on every changed owner, then:

  ```text
  lake build
  npm run formal:size
  rg -n '\.ref|DefinitionEnv|VerifiedDefinitions|interpretDefinitions|refSpawn|refLeaf|refAbstract|applyUnfold|applyFold|citedTheorem|RuleInput\.theorem' VisualProof docs/goals/primitive-wire-quantifier-lean-completion
  rg -n 'sorry' VisualProof
  git diff --check
  ```

  The displaced-model scan must return no Lean authority. Every `sorry` row must map to an owning production theorem in the RED ledger.

- [x] **Step 8: Commit the corrected RED skeleton**

  Stage only the macro-free reconstruction and corrected persistent-plan artifacts, then commit with `refactor(lean): remove macro system from calculus`.

### Task 2: Prove the macro-free semantic and checked-diagram core GREEN

**Files:**
- Modify: `VisualProof/Diagram/**`
- Modify: `VisualProof/Model.lean`
- Modify: `VisualProof/Theory/Semantics.lean`

**Interfaces:**
- Consumes: Task 1 macro-free types and RED owners.
- Produces: GREEN denotation, renaming, context, elaboration, occurrence, the
  lossless extraction witness contract, removal, boundary, and
  concrete-isomorphism owners used by R2–R5. Current extraction/copy
  implementations remain candidates subject to Task 3's declaration-level
  comparison; Task 2 compilation did not establish their equivalence to the
  structural predecessor closure.

- [x] **Step 1: Port intrinsic algebra and context proofs**

  Remove only the obsolete ref/definition cases from the existing GREEN recursion. Preserve atom, identity, cut, existential-local, renaming, and parity proofs.

- [x] **Step 2: Port checked concrete transformation proofs**

  Migrate occurrence, the lossless `Extraction` witness contract, removal, and
  isomorphism proofs to the three-constructor `CNode`. Do not weaken invariants
  or introduce alternate checkers. Do not claim that the witness contract alone
  constructs an extraction. Operation-specific extraction, copy/splice, and
  factorization owners are selected in Task 3 by comparing their complete
  predecessor closures; Task 2 does not freeze a replacement operation.

- [x] **Step 3: Prove elaboration and ordered-boundary invariance**

  Keep the single production elaborator. Prove its completeness and `CheckedIso.denote_iff` directly for the macro-free semantics, including repeated ordered-boundary aliases.

- [x] **Step 4: Validate and commit Task 2**

  Run focused owner builds, `lake build`, `npm run formal:size`, `#print axioms` through a temporary audit file outside the repository, displaced-model scans, and `git diff --check`. Commit with `feat(lean): prove macro-free semantic core`.

### Task 3: Prove every actual rule and exhaustive dispatcher sound

**Files:**
- Modify: `VisualProof/Rule/Soundness/Core.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`
- Modify: `VisualProof/Rule/Soundness/Identity.lean`
- Modify: `VisualProof/Rule/Soundness/WirePrimitive.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: directly required `VisualProof/Diagram/**` proof helpers only

**Interfaces:**
- Consumes: Task 2 GREEN semantics and the exact 31-constructor production sum.
- Produces: one GREEN all-model owner per constructor and exhaustive GREEN `applyStep_sound`.

- [ ] **Step 1: Port established structural soundness**

  Before changing a structural owner, audit its operation and complete proof
  dependency closure declaration-by-declaration against both predecessors.
  Select one predecessor architecture and port that operation, factorization,
  semantic closure, and terminal theorem together. A current declaration is
  retained only when the comparison proves substantive equivalence; successful
  compilation and an existing consumer are not evidence of equivalence.

  For iteration, the selected architecture is the completed abandoned
  signature-indexed HO implementation: `CheckedExtraction`, site and relative
  frames, `ConcreteSpliceAttachment`, `InsertionCompilation`, `spliceRaw`, the
  required `Factorization*` kernels, intrinsic containment, and
  `CheckedOrdinaryIteration.equivalence`/`.sound` form one proof architecture.
  Port that chain coherently. Remove obsolete definition/reference, macro,
  normalization, provenance, transport, and checker packaging only where it is
  not a mathematical owner consumed by the terminal theorem.

  Consult the SO tree only for localized current-representation facts. Do not
  combine its selection/copy/compiler-route proof architecture with the selected
  HO chain or introduce an adapter between them. Reassess current extraction,
  copy, compiler-simulation, semantic, and `SiteFrame` declarations against the
  HO chain declaration-by-declaration. Retain a declaration only when the audit
  establishes the exact HO predecessor and downstream terminal use. If an exact
  selected HO declaration cannot be adapted, stop and record its precise
  statement and incompatible hypothesis or conclusion before writing an
  alternative.

  The declaration audit is
  `docs/goals/primitive-wire-quantifier-lean-completion/notes/iteration-declaration-audit.md`.
  It records that the earlier SO-predecessor selection and broad-family reuse classification were false:
  `copySelection` and its copied-fragment simulation are a bespoke operation and
  proof closure, not localized HO ports. Delete that path, then fill the audit
  declaration-by-declaration while porting the exact HO operation and terminal
  chain. No current extraction, semantic, or contraction helper is retained
  merely because it served the displaced operation.

  Port the other structural owners from their separately selected, recorded
  predecessor closures. Adapt the abandoned higher-order
  `StructuralInsertionReceipt.sound` kernel for `atomSpawn_sound` and
  `identityInsert_sound`; preserve already validated erasure and vacuous owners;
  and apply the same single-basis rule before completing deiteration or double
  cut.

- [ ] **Step 2: Complete vacuous-wire and identity soundness**

  Preserve the existing GREEN vacuous owners. Port degeneracy, one-point collapse, and same-region fusion from the abandoned tree's `IdentityNormalizationCore`, three candidate well-formedness modules, and `dropDegenerate_sound`, `collapseOnePoint_sound`, and `fuseSameRegion_sound`. Retain only the explicit transformation kernels; do not formalize canonicalizer enumeration, orchestration, repetition, or transport.

- [ ] **Step 3: Prove all primitive wire families**

  Port the completed higher-order owners from `WirePrimitive/Partition.lean`,
  `Content.lean`, `ArgumentsArity.lean`, `ArgumentsPermute.lean`,
  `ArgumentsCore.lean`, `ArgumentsDropExtend.lean`, and `Leaves.lean`: wire
  join/sever, cut wrap/absorb, parallel split/fuse, end delete/spawn, arity
  shift/unshift, argument permute/duplicate/contract/drop/extend, formal
  apply/abstract, and identity leaf/abstract. Their proof source includes the
  lower raw and semantic closure inventoried in the durable provenance map:
  `Concrete/WirePartition*`, `Concrete/WirePrimitive/Content*`,
  `Concrete/WirePrimitive/Arguments*`, and
  `Concrete/WirePrimitive/Leaves*`. Every current public owner derives its
  gates and candidate from accepted production input. Adapt only the
  construction, factorization, inverse, ledger, and denotation lemmas actually
  consumed by those terminal proofs; do not independently re-prove missing
  lower layers or recreate their discarded wrappers.

- [ ] **Step 4: Prove exhaustive aggregate soundness**

  Retain the current GREEN `applyStep_sound` exact pattern match over all 31 `Step` constructors, then revalidate it after every individual owner is GREEN. Do not maintain a second rule inventory as a substitute for this coverage theorem, and do not claim system-wide soundness while any delegated owner remains RED.

- [ ] **Step 5: Validate and commit Task 3**

  Run focused family builds, exact constructor-to-owner coverage, axiom audits for every owner and `applyStep_sound`, full build and size gates, displaced-model scans, and `git diff --check`. Commit with `feat(lean): prove primitive rule soundness`.

### Task 4: Prove primitive replay, checked theorem, and verified theory sound

**Files:**
- Modify: `VisualProof/Proof/Replay.lean`
- Modify: `VisualProof/Proof/Theorem.lean`
- Modify: `VisualProof/Proof/Theory.lean`

**Interfaces:**
- Consumes: Task 3 GREEN `applyStep_sound` and Task 2 GREEN `CheckedIso.denote_iff`.
- Produces: GREEN replay, checked-theorem, and verified-theory soundness without citation.

- [ ] **Step 1: Prove replay sound by induction**

  Mechanically port the complete SO replay induction to the simpler current dependent program. The nil case is reflexivity. The cons case composes the current step's `applyStep_sound` result with the tail induction hypothesis, respecting forward/backward ordered interfaces. Do not restore the old executable open-step checker or receipt transport.

- [ ] **Step 2: Prove checked theorem sound**

  Port the complete SO `checkedTheorem_sound` kernel: compose the left primitive replay, meeting-diagram checked isomorphism, and right primitive replay. The statement quantifies over every full model and contains no proof context or definition environment. Delete the old registration/citation suffix.

- [ ] **Step 3: Prove verified theory sound**

  Port and simplify the complete SO verified-theory induction so every stored schema is sound from its own `CheckedTheorem` certificate. Do not add registration or prior-prefix citation.

- [ ] **Step 4: Validate and commit Task 4**

  Run focused builds, axiom audits, full gates, citation-absence scans, and `git diff --check`. Commit with `feat(lean): prove primitive replay certificates`.

### Task 5: Prove higher-order formula semantic expressiveness

**Files:**
- Modify: `VisualProof/Formula/Syntax.lean`
- Modify: `VisualProof/Formula/Semantics.lean`
- Modify: `VisualProof/Formula/Soundness.lean`

**Interfaces:**
- Consumes: macro-free intrinsic diagrams and full-model semantics.
- Produces: GREEN existential `Formula.semantically_complete`.

- [ ] **Step 1: Validate the source language and semantics**

  Keep typed atom, same-signature equality, conjunction, implication, and grouped existential/universal quantification. Ensure equality's two operands share one implicit `signature` index.

- [ ] **Step 2: Prove existential diagram expressiveness**

  Prove:

  ```lean
  theorem semantically_complete (formula : Formula context) :
      ∃ (diagram : OpenDiagram)
        (boundary : diagram.boundary.signatures = context),
        ∀ (model : Model) (assignment : Assignment model context),
          formula.denote model assignment ↔
            denoteOpen model diagram (boundary ▸ assignment)
  ```

  This theorem is genuinely new: neither predecessor contains the formula language or this expressiveness responsibility. The proof may construct a witness internally, but no translator is a public correctness requirement.

- [ ] **Step 3: Validate and commit Task 5**

  Run focused builds, axiom audit, full gates, scans for compiler/definition dependencies, and `git diff --check`. Commit with `feat(lean): prove formula expressiveness`.

### Task 6: Prove primitive program soundness and direct-operation foundations

**Files:**
- Modify: `VisualProof/Rule/WirePrimitive/Direct.lean`
- Modify: `VisualProof/Rule/WirePrimitive/Program.lean`
- Modify: directly required primitive operation owners

**Interfaces:**
- Consumes: Task 3 rule owners and Task 4 primitive replay.
- Produces: GREEN primitive-program soundness and exact macro-free direct substitution/comprehension relations.

- [ ] **Step 1: Remove macro dependencies from direct inputs**

  Direct substitution and comprehension inputs relate checked open diagrams and exact raw occurrence/boundary data only. They contain no ref body, stored definition, compiler state, identity-normalization mechanism, canonicalizer, or search result. Their primitive basis includes identity leaf/abstraction for identity-node content but excludes identity insertion and degeneracy/collapse/fusion.

- [ ] **Step 2: Prove primitive program soundness**

  Mechanically adapt the completed abandoned `runPrimitiveProgram_sound` induction (or the equivalent SO replay composition) to `WirePrimitive.Program`; discharge each cons using the corresponding Task 3 owner and the primitive tag proof.

- [ ] **Step 3: Validate and commit Task 6**

  Run focused builds, constructor audits, full gates, displaced-model scans, and `git diff --check`. Commit with `feat(lean): prove primitive program foundations`.

### Task 7: Prove primitive derivability of direct substitution and comprehension

**Files:**
- Modify: `VisualProof/Rule/WirePrimitive/Adequacy.lean`
- Modify: directly required primitive construction helpers only

**Interfaces:**
- Consumes: Task 6 direct relations/program soundness and completed primitive operations.
- Produces: GREEN existential direct-substitution and direct-comprehension derivability with exact raw ordered boundaries.

- [ ] **Step 1: Prove direct substitution derivability**

  For every valid direct substitution input, exhibit a primitive program and a target whose raw checked diagram corresponds exactly to the direct output, including positional ordered-boundary aliases. Port the residual, plumbing, connective, leaf, termination, and landing cases from the abandoned `Compiler.lean`/`CompilerTermination.lean` as proof-local existential witness construction; do not port or recreate a compiler definition or API. Prove that current `attachment_alias` makes the predecessor's `identityRequests` empty, then prove the missing current-input bridge, failure-free totality, and exact landing.

- [ ] **Step 2: Prove direct comprehension derivability**

  For every valid direct comprehension input, exhibit the corresponding primitive program and exact raw target. Reuse the completed reversed-sever construction cases and SO occurrence/extraction/removal kernels internally. Identity leaf steps reverse to identity abstraction when the pattern contains identity nodes; no identity insertion, identity-normalization rule, canonicalizer, definition/ref operation, public compiler, or normalization dependency occurs.

- [ ] **Step 3: Validate and commit Task 7**

  Run focused builds, axiom audits, dependency scans, full gates, and `git diff --check`. Commit with `feat(lean): prove primitive direct adequacy`.

### Task 8: Run final conformance and completion audit

**Files:**
- Modify: `docs/goals/primitive-wire-quantifier-lean-completion/state.yaml`
- Modify: `docs/goals/primitive-wire-quantifier-lean-completion/goal.md`
- Modify: `docs/goals/primitive-wire-quantifier-lean-completion/notes/temporary-backup-salvage-map.md`
- Modify: `.superpowers/sdd/2026-07-30-primitive-wire-quantifier-lean-completion/**`

**Interfaces:**
- Consumes: Tasks 1–7.
- Produces: direct evidence that R1–R5 and all negative architecture constraints hold.

- [ ] **Step 1: Audit the final declaration and import surface**

  Recheck every public theorem/module against the two-predecessor provenance ledger and R1–R5. Delete unused helpers and all displaced macro, Lambda, bubble, normalization, receipt, provenance, transport, search, atlas, or fixture authority. No final owner may be labeled genuinely new without an explicit absence finding in both predecessors.

- [ ] **Step 2: Audit RED/GREEN and axioms**

  Require no `sorry`, `admit`, or project axiom. Run `#print axioms` for every final owner from a temporary file outside the repository; only Lean's accepted foundational axioms may remain.

- [ ] **Step 3: Run complete gates**

  ```text
  lake build
  npm run formal:size
  npm test
  npm run typecheck
  git diff --check
  node /home/ahart/.codex/plugins/cache/goalbuddy/goalbuddy/0.4.2/skills/goal-prep/scripts/check-goal-state.mjs docs/goals/primitive-wire-quantifier-lean-completion/state.yaml
  ```

- [ ] **Step 4: Record conformance and commit completion**

  Append `<conformance>` to the active foundation record, record direct R1–R5 evidence and gate outputs on the board, verify a clean worktree, and commit with `feat(lean): complete higher-order diagram formalization`.

## Completion Oracle

The plan is complete only when all eight tasks are complete; the final atom/identity/cut calculus and exact 31-rule primitive sum are GREEN; primitive replay, checked theorem, and verified theory certification are GREEN without citation; formula expressiveness and both direct derivability theorems are GREEN; displaced macro and implementation-only authorities are absent; and every Task 8 gate passes.
