# Context-Free Primitive Rule System Implementation Plan

**Status:** Complete and validated on 2026-08-05.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make primitive rule execution, soundness, replay, and theorem certification context-free while retaining theorem schemas solely as meta-level certified results.

**Architecture:** The object-level calculus owns a closed twelve-constructor `Step` type and a context-free `applyStep`. Every primitive soundness theorem proves its result directly, and replay composes those theorems without ambient hypotheses. The proof layer separately owns `TheoremSchema`, `CheckedTheorem`, and verified collections of checked schemas; no theorem data flows back into primitive execution.

**Tech Stack:** Lean 4, Lake, Git.

## Global Constraints

- Previously established theorems are never primitive step content.
- `ProofContext` must not exist in primitive rules, programs, replay, soundness, checked-theorem certification, or verified-theory certification.
- Retained primitive rules must not require `context.Valid`.
- Bound second-order relation variables and quantifier bubbles remain unchanged.
- Existing primitive definitions and proof kernels are adapted in place; no replacement semantics or synthetic validation theorem is introduced.
- Every definition is complete; `sorry` is prohibited.
- Validation uses production theorems, focused builds, the full build, trust audit, source scans, and diff hygiene.

---

### Task 1: Close the primitive rule inventory

**Files:**
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Correspondence/StepTags.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: existing primitive payloads and `Diagram.CheckedDiagram`.
- Produces: `Step (input : Diagram.CheckedDiagram)`, a twelve-element `StepTag.all`, and context-free `Step.tag`.

- [x] **Step 1: Remove theorem data from the primitive owner**

Keep only calculus data in `VisualProof.Rule.Step`: remove the theorem tag, theorem error, `Direction`, `TheoremSchema`, `ProofContext`, `PinnedOccurrence`, `TheoremPayload`, `theoremSidesMatch`, and the theorem constructor. Preserve `selectedFragment` and every declaration used by retained comprehension or iteration rules.

- [x] **Step 2: Define the context-free primitive step type**

The resulting signature is:

```lean
inductive Step (input : Diagram.CheckedDiagram)
  | boundRelationSpawn ...
  | wireJoin ...
  | erasure ...
  | wireSever ...
  | iteration ...
  | deiteration ...
  | doubleCutIntro ...
  | doubleCutElim ...
  | comprehensionInstantiate ...
  | comprehensionAbstract ...
  | vacuousIntro ...
  | vacuousElim ...

def Step.tag : Step input → StepTag
```

Set `StepTag.all_length` to `12`; keep `StepTag.all_nodup`, `StepTag.mem_all`, semantic modes, and `Step.tag_mem_all` kernel-checked.

- [x] **Step 3: Update serialized correspondence and imports**

Make `Correspondence.StepTags` exhaustive over the same twelve tags. The umbrella module must import only current rule owners.

- [x] **Step 4: Build the primitive type surface**

Run:

```bash
lake build VisualProof.Rule.Step VisualProof.Correspondence.StepTags
```

Expected: both targets elaborate; failures may only be downstream API migrations named by later tasks.

### Task 2: Make execution and primitive soundness context-free

**Files:**
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`
- Modify: `VisualProof/Rule/Soundness/WireJoin.lean`
- Modify: `VisualProof/Rule/Soundness/Iteration/DeiterationSemantic.lean`
- Modify: `VisualProof/Rule/Soundness/HighLevel.lean`
- Modify: `VisualProof/Rule/Soundness/All.lean`
- Remove the citation-only rule implementation owner from the module graph.

**Interfaces:**
- Consumes: `Step input`, retained primitive operation functions, and their existing proof kernels.
- Produces: context-free `applyStep`, `SuccessfulStepSound`, `SuccessfulReceiptSound`, every rule-family terminal soundness theorem, and exhaustive `applyStep_sound`.

- [x] **Step 1: Replace the dispatcher and soundness contracts**

Use these context-free interfaces:

```lean
def applyStep (orientation : Orientation)
    (input : CheckedDiagram) (step : Step input) :
    Except StepError (StepReceipt input)

def SuccessfulStepSound (orientation : Orientation)
    (input output : CheckedDiagram) (step : Step input) : Prop

def SuccessfulReceiptSound (orientation : Orientation)
    (input : CheckedDiagram) (step : Step input)
    (receipt : StepReceipt input) : Prop
```

Their semantic quantification begins directly with `∀ model`; no validity premise occurs.

- [x] **Step 2: Adapt shared proof combinators**

Remove the context argument and validity binder from `SuccessfulReceiptSound.of_equivalence`, `.of_forward`, `.of_backward`, `.of_realized_operational`, and `.closed`. Preserve their mathematical conclusions and proof bodies.

- [x] **Step 3: Adapt every retained terminal rule theorem**

Remove `ProofContext` parameters, `context.Valid` binders, and validity plumbing from bound-relation spawn, wire join, erasure, sever, iteration, deiteration, double-cut, comprehension, and vacuous-rule soundness. Do not change their operations, witnesses, semantic statements, or substantive proof kernels.

- [x] **Step 4: Restrict high-level soundness to retained rules**

`HighLevel.lean` must own only comprehension soundness and its actual dependencies. No theorem replacement, pinned theorem occurrence, citation polarity, theorem matching, or citation simulation declaration remains in its module graph.

- [x] **Step 5: Make aggregate soundness exhaustive**

The terminal theorem is:

```lean
theorem applyStep_sound
    {orientation : Orientation}
    {input : Diagram.CheckedDiagram} {step : Step input}
    {receipt : StepReceipt input}
    (happly : applyStep orientation input step = .ok receipt) :
    SuccessfulReceiptSound orientation input step receipt
```

Its cases are exactly the twelve `Step` constructors.

- [x] **Step 6: Build aggregate soundness**

Run:

```bash
lake build VisualProof.Rule.Soundness.All
```

Expected: the complete primitive soundness dependency closure passes.

### Task 3: Make programs and replay context-free

**Files:**
- Modify: `VisualProof/Proof/Replay.lean`

**Interfaces:**
- Consumes: `Step input`, `applyStep orientation input step`, and `applyStep_sound`.
- Produces: context-free `Program`, `replay`, `replayClosed`, and replay soundness theorems.

- [x] **Step 1: Remove context from execution types**

Use these interfaces:

```lean
def applyOpenStep (orientation : Orientation)
    (input : OpenProofState) (action : Step input.diagram) :
    Except StepError OpenProofState

inductive Program (orientation : Orientation) : OpenProofState → Type

def replay (orientation : Orientation) :
    (input : OpenProofState) → Program orientation input →
    Except StepError OpenProofState
```

`replayClosed` is the corresponding empty-boundary specialization.

- [x] **Step 2: Remove validity from replay soundness**

`applyOpenStep_sound`, `replay_sound`, `forward_replay_sound`, and `backward_replay_sound` quantify over a model and assignments directly. Their proofs compose the context-free `applyStep_sound` result.

- [x] **Step 3: Build replay**

Run:

```bash
lake build VisualProof.Proof.Replay
```

Expected: replay and both orientations of replay soundness pass without a context argument.

### Task 4: Keep theorem schemas and certification meta-level

**Files:**
- Create: `VisualProof/Proof/Schema.lean`
- Modify: `VisualProof/Proof/Theorem.lean`
- Modify: `VisualProof/Proof/Theory.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: checked open diagrams and context-free replay.
- Produces: meta-level `TheoremSchema`, `TheoremSchema.Valid`, `CheckedTheorem`, `checkedTheorem_sound`, `VerifiedTheorems`, `VerifiedTheory`, and membership soundness.

- [x] **Step 1: Give schemas a meta-level owner**

Define in `VisualProof.Proof.Schema`:

```lean
structure TheoremSchema where
  left : Diagram.CheckedOpenDiagram
  right : Diagram.CheckedOpenDiagram
  sameBoundaryArity : left.val.boundary.length = right.val.boundary.length

def TheoremSchema.Valid (schema : TheoremSchema) (model : Model) : Prop :=
  ∀ args, schema.left.denote model args →
    schema.right.denote model
      (args ∘ Fin.cast schema.sameBoundaryArity.symm)
```

- [x] **Step 2: Make checked theorem certification independent**

Use:

```lean
structure CheckedTheorem where
  schema : TheoremSchema
  forwardFinish : OpenProofState
  backwardFinish : OpenProofState
  forwardProgram : Program .forward (theoremSideState schema.left)
  backwardProgram : Program .backward (theoremSideState schema.right)
  forwardReplay : replay .forward ... = .ok forwardFinish
  backwardReplay : replay .backward ... = .ok backwardFinish
  meet : OpenConcreteIso forwardFinish.asCheckedOpen.val
    backwardFinish.asCheckedOpen.val

theorem checkedTheorem_sound (checked : CheckedTheorem) :
    checked.schema.Valid model
```

No registration operation or citation theorem exists.

- [x] **Step 3: Make verified theories collections of certified results**

Keep the established ordered collection shape, but make each appended item an independent `CheckedTheorem`:

```lean
inductive VerifiedTheorems : List TheoremSchema → Type
  | empty : VerifiedTheorems []
  | append {prior} (verified : VerifiedTheorems prior)
      (checked : CheckedTheorem) :
      VerifiedTheorems (prior ++ [checked.schema])
```

Prove indexed and membership soundness by induction over the certified collection, never by constructing or validating a context.

- [x] **Step 4: Build certification**

Run:

```bash
lake build VisualProof.Proof.Theorem VisualProof.Proof.Theory
```

Expected: checked-theorem and verified-theory soundness pass without ambient assumptions.

### Task 5: Validate the authoritative boundary and commit

**Files:**
- Modify: `VisualProof/Audit.lean`
- Modify: `docs/superpowers/plans/2026-08-05-remove-theorem-citation-and-proof-context.md`

**Interfaces:**
- Consumes: the completed context-free calculus and certification pipeline.
- Produces: authoritative trust output, completed plan record, atomic commit, and clean worktree.

- [x] **Step 1: Update the trust audit**

Audit `applyStep_sound`, replay soundness, `checkedTheorem_sound`, and `verifiedTheory_sound`. The audit must not reference theorem application or citation.

- [x] **Step 2: Run focused and full builds**

Run:

```bash
lake build VisualProof.Rule.Soundness.All
lake build VisualProof.Proof.Replay
lake build VisualProof.Proof.Theorem
lake build VisualProof.Proof.Theory
lake build VisualProof.Correspondence.StepTags
lake build VisualProof.Audit
lake build
```

Expected: every target succeeds.

- [x] **Step 3: Run exact source audits**

Run:

```bash
rg -n 'ProofContext|context\.Valid|applyTheorem|theoremSidesMatch|TheoremPayload|theoremIndex|citation_sound|citationPolarity|StepTag\.theorem|unknownTheorem' VisualProof VisualProof.lean -g '*.lean'
rg -n '\bsorry\b|\badmit\b|^axiom\b|^constant\b' VisualProof -g '*.lean'
rg -n '^(namespace (.*Examples|Examples)|example\b)|#(check|eval|reduce|guard)' VisualProof -g '*.lean'
git diff --check
```

Expected: all `rg` commands return no matches and `git diff --check` succeeds.

- [x] **Step 4: Record conformance and commit**

Append the foundation-record conformance section, mark every plan checkbox complete, stage only task-owned files, and commit:

```bash
git add VisualProof VisualProof.lean docs/superpowers/plans/2026-08-05-remove-theorem-citation-and-proof-context.md
git commit -m "refactor(lean): make primitive rules context-free"
git status --porcelain
```

Expected: the commit succeeds and the final status is empty.
