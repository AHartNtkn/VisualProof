# Definition/Reference Macro Removal Implementation Plan

**Status:** Complete. The full library and trust audit build, the source audits
are empty, and the retained public rule inventory has thirteen constructors.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Make the Lean calculus definition-free: diagrams, rules, semantics, and proof checking retain bound second-order relations and quantifier bubbles but contain no definition/reference macro representation or index.

**Architecture:** Reconstruct the type graph at its intrinsic root so `Region`, `Item`, checked diagrams, rules, and proofs are no longer parameterized by a definition signature. Preserve the existing bound-relation, structural, comprehension, theorem-application, replay, and soundness proof kernels by mechanically retyping them against the smaller syntax. Give generic theorem replacement its own production owner and expose exactly the remaining rule inventory through `applyStep_sound`.

**Tech Stack:** Lean 4.30, Lake, repository `VisualProof` library, kernel axiom audit.

## Global Constraints

- Bound second-order relation variables (`RelCtx`, `RelVar`) and quantifier bubbles remain.
- N-ary identity nodes and their semantics remain.
- The theorem-application/replay/checking architecture remains, but it has no definition registry or interpreted named environment.
- No compatibility aliases, phantom signature parameters, named constructors, definition indices, fold/unfold paths, or parallel semantic authorities remain.
- Every production definition is complete; `sorry` is permitted only for an owning production theorem during a genuine RED phase, and this refactor introduces no synthetic theorem.
- No fixture modules, anonymous examples, redundant construction checks, or source-level `#check`/`#eval` validation.

---

### Task 1: Reconstruct the intrinsic calculus and semantics

**Files:**
- Rename: `VisualProof/Theory/Signature.lean` → `VisualProof/Theory/Relation.lean`
- Modify: `VisualProof/Diagram/Core.lean`
- Modify: `VisualProof/Diagram/Boundary.lean`
- Modify: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/Context.lean`
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/ContextReachability.lean`
- Modify: `VisualProof/Diagram/ContextPathIsomorphism.lean`
- Modify: `VisualProof/Diagram/RenamingIsomorphism.lean`
- Remove: `VisualProof/Theory/Definition.lean`
- Remove: `VisualProof/Theory/Semantics.lean`

**Interfaces:**
- Consumes: `Model`, `RelCtx`, and `RelVar`.
- Produces: `Region wires rels`, `Item wires rels`, `ItemSeq wires rels`, `OpenDiagram arity`, and denotation functions with no named environment.

- [x] **Step 1: Establish the bound-relation owner**

Keep only the independent bound-relation vocabulary:

```lean
namespace VisualProof.Theory

abbrev RelCtx := List Nat

structure RelVar (ctx : RelCtx) (arity : Nat) where
  index : Fin ctx.length
  hasArity : ctx.get index = arity

end VisualProof.Theory
```

- [x] **Step 2: Retype intrinsic syntax without a definition signature**

Use this constructor inventory:

```lean
mutual
  inductive Region : Nat → RelCtx → Type
    | mk {wires : Nat} {rels : RelCtx} (localWires : Nat)
        (items : ItemSeq (wires + localWires) rels) : Region wires rels

  inductive Item : Nat → RelCtx → Type
    | atom : RelVar rels arity → (Fin arity → Fin wires) → Item wires rels
    | identity : (arity : Nat) → (Fin arity → Fin wires) → Item wires rels
    | cut : Region wires rels → Item wires rels
    | bubble : (arity : Nat) → Region wires (arity :: rels) → Item wires rels

  inductive ItemSeq : Nat → RelCtx → Type
    | nil : ItemSeq wires rels
    | cons : Item wires rels → ItemSeq wires rels → ItemSeq wires rels
end
```

- [x] **Step 3: Retype boundary, renaming, contexts, and isomorphisms**

Erase the definition-only parameter from every declaration in the listed diagram modules. Remove only the constructor branches corresponding to named content. Preserve atom, identity, cut, bubble, wire-renaming, relation-renaming, context, open-boundary, isomorphism, and algebra theorem bodies, adjusting constructor arities mechanically.

- [x] **Step 4: Retype denotation**

The semantic interface becomes:

```lean
def Relation (D : Type u) (arity : Nat) := (Fin arity → D) → Prop
def RelEnv (D : Type u) : RelCtx → Type u

mutual
  def denoteRegion (model : Model) (env : Fin outer → model.Carrier)
      (rels : RelEnv model.Carrier relCtx) : Region outer relCtx → Prop
  def denoteItem (model : Model) (env : Fin wires → model.Carrier)
      (rels : RelEnv model.Carrier relCtx) : Item wires relCtx → Prop
  def denoteItemSeq (model : Model) (env : Fin wires → model.Carrier)
      (rels : RelEnv model.Carrier relCtx) : ItemSeq wires relCtx → Prop
end

def denoteOpen (model : Model) (diagram : OpenDiagram arity)
    (args : Fin arity → model.Carrier) : Prop
```

The `atom` branch uses `RelEnv.lookup`; the `bubble` branch existentially extends `RelEnv`; identity, cut, and conjunction retain their current meanings.

- [x] **Step 5: Validate the intrinsic layer**

Run:

```bash
lake build VisualProof.Diagram.Semantics VisualProof.Diagram.Algebra VisualProof.Diagram.OpenIsomorphism
rg -n 'NamedRel|NamedEnv|\.named\b|\bsignature\b' VisualProof/Theory/Relation.lean VisualProof/Diagram -g '*.lean'
```

Expected: focused build succeeds; the scan returns no macro vocabulary or definition-only parameter in intrinsic diagram modules.

- [x] **Step 6: Include the intrinsic boundary in the atomic task commit**

```bash
git add VisualProof/Theory VisualProof/Diagram
```

### Task 2: Reconstruct concrete diagrams and elaboration

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Core.lean`
- Modify: `VisualProof/Diagram/Concrete/WellFormed.lean`
- Modify: `VisualProof/Diagram/Concrete/Open.lean`
- Modify: `VisualProof/Diagram/Concrete/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Concrete/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Concrete/Semantics.lean`
- Modify: every `.lean` module under `VisualProof/Diagram/Concrete/Elaboration/`
- Modify: every `.lean` module under `VisualProof/Diagram/Concrete/Matcher/`
- Modify: `VisualProof/Diagram/Concrete/Occurrence.lean`
- Modify: `VisualProof/Diagram/Concrete/OccurrenceEmbedding.lean`
- Modify: `VisualProof/Diagram/Concrete/OccurrenceExtraction.lean`
- Modify: `VisualProof/Diagram/Concrete/OccurrenceSelection.lean`
- Modify: every `.lean` module under `VisualProof/Diagram/Concrete/Subgraph/`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Interfaces:**
- Consumes: the macro-free intrinsic interfaces from Task 1.
- Produces: `CheckedDiagram`, `CheckedOpenDiagram`, `checkWellFormed`, elaboration, matching, extraction, and splicing without a signature argument.

- [x] **Step 1: Reduce concrete constructors and well-formedness**

Use:

```lean
inductive CNode (regions : Nat)
  | atom (region binder : Fin regions)
  | identity (region : Fin regions) (arity : Nat)

structure ConcreteDiagram.WellFormed (d : ConcreteDiagram) : Prop where
  root_is_sheet : d.RootIsSheet
  only_root_is_sheet : d.OnlyRootIsSheet
  all_regions_reach_root : d.AllRegionsReachRoot
  atom_binders_are_bubbles : d.AtomBindersAreBubbles
  atom_binders_enclose : d.AtomBindersEnclose
  endpoints_are_valid : d.EndpointsAreValid
  endpoints_are_nodup : d.EndpointsAreNodup
  wire_endpoints_are_disjoint : d.WireEndpointsAreDisjoint
  required_ports_are_covered : d.RequiredPortsAreCovered
  wire_scopes_enclose : d.WireScopesEnclose

abbrev CheckedDiagram := { d : ConcreteDiagram // d.WellFormed }
def checkWellFormed (d : ConcreteDiagram) : Except WFError CheckedDiagram
```

Remove the named-reference validation predicate and error constructor. Preserve every other well-formedness field and checker branch.

- [x] **Step 2: Retype checked/open/isomorphism APIs**

Remove the signature argument from `CheckedDiagram`, `CheckedOpenDiagram`, well-formedness transport, and all concrete/open isomorphism theorems. Preserve their proof bodies modulo the shorter records.

- [x] **Step 3: Retype elaboration and semantic simulation**

Remove the concrete named-node compiler branch and its relation lookup helper. Retype all compiler contexts and outputs to the Task 1 intrinsic types. Preserve bound-atom compilation through bubble binders and all identity/cut/bubble cases.

- [x] **Step 4: Retype matcher, occurrence, extraction, and splice modules**

Remove named-node matching cases. Erase the signature argument from checked operations and proof records, including `extractChecked`, `decomposeChecked`, `spliceChecked`, and their soundness/completeness theorems. Preserve existing graph, boundary, quotient, attachment, compiler, and semantic proof kernels.

- [x] **Step 5: Validate the concrete layer**

Run:

```bash
lake build VisualProof.Diagram.Concrete VisualProof.Diagram.Concrete.Matcher VisualProof.Diagram.Concrete.Subgraph
rg -n 'namedReference|NamedReference|\.named\b|\| named\b|\bsignature\b' VisualProof/Diagram/Concrete -g '*.lean'
```

Expected: all focused targets succeed and the scan is empty.

- [x] **Step 6: Include the concrete boundary in the atomic task commit**

```bash
git add VisualProof/Diagram/Concrete.lean VisualProof/Diagram/Concrete
```

### Task 3: Reduce the rule inventory and establish theorem ownership

**Files:**
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Structural/SpawnCore.lean`
- Modify: `VisualProof/Rule/Structural/SpawnOpen.lean`
- Modify: `VisualProof/Rule/Structural/SpawnTransport.lean`
- Modify: `VisualProof/Rule/Structural/Semantics.lean`
- Modify: `VisualProof/Rule/Structural.lean`
- Modify: `VisualProof/Rule/Comprehension.lean`
- Modify: `VisualProof/Rule/Comprehension/Semantics.lean`
- Rename: `VisualProof/Rule/Named.lean` → `VisualProof/Rule/Theorem.lean`
- Remove: `VisualProof/Rule/NamedReference.lean`
- Remove: `VisualProof/Rule/Named/ReferencePattern.lean`

**Interfaces:**
- Consumes: macro-free checked diagrams and semantics.
- Produces: theorem-only `ProofContext`, thirteen `StepTag`/`Step` constructors, generic theorem replacement, and retained rule operations.

- [x] **Step 1: Make theorem schemas and proof contexts definition-free**

Use:

```lean
structure TheoremSchema where
  left : Diagram.CheckedOpenDiagram
  right : Diagram.CheckedOpenDiagram
  sameBoundaryArity : left.val.boundary.length = right.val.boundary.length

structure ProofContext where
  theorems : List TheoremSchema
```

- [x] **Step 2: Reduce the serialized and typed rule inventories**

`StepTag.all` and `Step` must contain exactly:

```lean
boundRelationSpawn
wireJoin
erasure
wireSever
iteration
deiteration
doubleCutIntro
doubleCutElim
comprehensionInstantiate
comprehensionAbstract
theorem
vacuousIntro
vacuousElim
```

Set `StepTag.all_length` to `13` and keep the typed inventory identical to this list.

- [x] **Step 3: Retain only bound-relation spawning**

Remove `applyRelationSpawn` and all concrete named-node construction/proofs. Preserve `applyBoundRelationSpawn` and its operation, receipt, success, realization, and semantic theorems with signature-free checked types.

- [x] **Step 4: Establish theorem application as the generic replacement owner**

In `VisualProof/Rule/Theorem.lean`, retain `PinnedOccurrence` replacement/reassembly machinery, `TheoremPayload`, `applyTheorem`, its success/realization/completeness results, and theorem-citation polarity lemmas. Exclude every declaration whose statement mentions named references, definitions, fold, or unfold.

- [x] **Step 5: Retype structural and comprehension operations**

Erase the definition-only parameter and named-node cases. Preserve all bound atom, identity, cut, bubble, wire, modal, iteration, deiteration, and comprehension definitions and existing production theorem statements.

- [x] **Step 6: Validate rule operations**

Run:

```bash
lake build VisualProof.Rule.Step VisualProof.Rule.Structural VisualProof.Rule.Comprehension VisualProof.Rule.Theorem
rg -n 'relationSpawn|relUnfold|relFold|NamedReference|namedReference|VerifiedDefinitions|definitionEntry|\.named\b|\bsignature\b' VisualProof/Rule/Step.lean VisualProof/Rule/Structural VisualProof/Rule/Comprehension.lean VisualProof/Rule/Comprehension VisualProof/Rule/Theorem.lean
```

Expected: focused builds succeed and the scan is empty.

- [x] **Step 7: Include the rule boundary in the atomic task commit**

```bash
git add VisualProof/Rule
```

### Task 4: Retype the complete soundness closure

**Files:**
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Soundness/All.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`
- Modify: `VisualProof/Rule/Soundness/WireJoin.lean`
- Modify: `VisualProof/Rule/Soundness/HighLevel.lean`
- Modify: every `.lean` module under `VisualProof/Rule/Soundness/AttachmentAliasSemantic*`
- Modify: every `.lean` module under `VisualProof/Rule/Soundness/Comprehension/`
- Modify: every `.lean` module under `VisualProof/Rule/Soundness/Iteration/`
- Modify: every `.lean` module under `VisualProof/Rule/Soundness/Modal/`

**Interfaces:**
- Consumes: the thirteen-constructor `Step`, theorem-only `ProofContext`, and macro-free denotation.
- Produces: all retained terminal soundness theorems and exhaustive `applyStep_sound`.

- [x] **Step 1: Retype semantic contracts**

Use:

```lean
def TheoremSchema.Valid (schema : TheoremSchema) (model : Model) : Prop :=
  ∀ args : Fin schema.left.val.boundary.length → model.Carrier,
    schema.left.denote model args →
      schema.right.denote model (args ∘ Fin.cast schema.sameBoundaryArity.symm)

structure ProofContext.Valid (context : ProofContext) (model : Model) : Prop where
  theorems : ∀ index : Fin context.theorems.length,
    (context.theorems.get index).Valid model
```

Retype `SuccessfulStepSound`, `SuccessfulReceiptSound`, locality, and boundary-parametric contracts by removing the interpreted definition environment.

- [x] **Step 2: Retype retained proof kernels mechanically**

Across the listed soundness modules, remove `signature`, `named`, and `interpretDefinitions` arguments. Remove only named-node and definition-rule cases. Keep the existing proof term for every bound-relation, identity, cut, bubble, wire, modal, iteration, deiteration, comprehension, attachment, and theorem-application result whenever elaboration accepts the mechanically shortened statement.

- [x] **Step 3: Make aggregate soundness exhaustive over thirteen rules**

`applyStep_sound` must case-split on exactly the thirteen remaining `Step` constructors and discharge each with its existing terminal rule-family theorem. There are no cases for relation-definition spawn, fold, or unfold.

- [x] **Step 4: Validate soundness**

Run:

```bash
lake build VisualProof.Rule.Soundness.All
rg -n 'interpretDefinitions|NamedEnv|VerifiedDefinitions|relationSpawn|relUnfold|relFold|\.named\b|\bsignature\b' VisualProof/Rule/Soundness.lean VisualProof/Rule/Soundness -g '*.lean'
```

Expected: terminal aggregate soundness succeeds and the scan is empty.

- [x] **Step 5: Include soundness in the atomic task commit**

```bash
git add VisualProof/Rule/Soundness.lean VisualProof/Rule/Soundness
```

### Task 5: Retype replay, checked theorems, and verified theories

**Files:**
- Modify: `VisualProof/Proof/Replay.lean`
- Modify: `VisualProof/Proof/Theorem.lean`
- Modify: `VisualProof/Proof/Theory.lean`

**Interfaces:**
- Consumes: theorem-only `ProofContext`, macro-free `Step`, and aggregate soundness.
- Produces: replay, checked theorem registration, and verified theory soundness without definitions or a signature parameter.

- [x] **Step 1: Retype replay**

Use `Program (context : ProofContext) (orientation : Orientation) (input : OpenProofState)` and make replay entailment quantify over `model` and boundary arguments only. Preserve the current induction and `applyStep_sound` use.

- [x] **Step 2: Retype checked theorems**

Use `CheckedTheorem (context : ProofContext)` and preserve forward/backward finishing proofs. Registration updates only `context.theorems`; there is no definitions field or preservation theorem for it.

- [x] **Step 3: Retype verified theories**

Use:

```lean
inductive VerifiedTheorems : List TheoremSchema → Type
  | empty : VerifiedTheorems []
  | append {prior : List TheoremSchema}
      (verified : VerifiedTheorems prior)
      (checked : CheckedTheorem verified.context) :
      VerifiedTheorems (prior ++ [checked.schema])

structure VerifiedTheory where
  theorems : List TheoremSchema
  verification : VerifiedTheorems theorems
```

State `verifiedTheory_sound` and membership soundness directly for every `Model`.

- [x] **Step 4: Validate proof checking**

Run:

```bash
lake build VisualProof.Proof.Replay VisualProof.Proof.Theorem VisualProof.Proof.Theory
rg -n 'VerifiedDefinitions|interpretDefinitions|definitions|NamedEnv|\bsignature\b' VisualProof/Proof -g '*.lean'
```

Expected: proof targets succeed and the scan is empty.

- [x] **Step 5: Include proof checking in the atomic task commit**

```bash
git add VisualProof/Proof
```

### Task 6: Align aggregate exports, correspondence, and trust audit

**Files:**
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `VisualProof/Correspondence/StepTags.lean`

**Interfaces:**
- Consumes: all completed macro-free modules.
- Produces: the public library surface, serialized thirteen-tag inventory, and trust audit.

- [x] **Step 1: Align exports and serialized names**

Export `VisualProof.Theory.Relation` and `VisualProof.Rule.Theorem`. Do not export definition, definition semantics, named-reference, or reference-pattern modules. Make `serializedName`, injectivity, length, and no-duplicates proofs cover exactly the thirteen current tags.

- [x] **Step 2: Align the trust audit**

Audit retained principal theorems only:

```lean
#print axioms VisualProof.Diagram.iso_denotation
#print axioms VisualProof.Diagram.Region.denote_spliceAt
#print axioms VisualProof.Diagram.denoteItem_identity
#print axioms VisualProof.Rule.applyComprehensionInstantiate_sound
#print axioms VisualProof.Rule.applyTheorem_sound
#print axioms VisualProof.Rule.applyStep_sound
#print axioms VisualProof.Proof.checkedTheorem_sound
#print axioms VisualProof.Proof.verifiedTheory_sound
#print axioms VisualProof.Diagram.Matcher.findOccurrences_sound
#print axioms VisualProof.Diagram.Matcher.findOccurrences_completeFor
```

- [x] **Step 3: Run decisive conformance scans**

Run:

```bash
rg -n 'VerifiedDefinitions|interpretDefinitions|NamedRel|NamedEnv|\.named\b|\| named\b|NamedReference|namedReference|relationSpawn|relUnfold|relFold|definitionEntry|definition\?' VisualProof -g '*.lean'
rg -n '\bsignature\b' VisualProof -g '*.lean'
rg -n '\bsorry\b|\badmit\b|^axiom\b|^constant\b' VisualProof -g '*.lean'
rg -n '^(namespace (.*Examples|Examples)|example\b)|#(check|eval|reduce|guard)' VisualProof -g '*.lean'
```

Expected: all four scans are empty.

- [x] **Step 4: Verify preserved higher-order relation syntax**

Run:

```bash
rg -n 'RelCtx|RelVar|\| atom\b|\| bubble\b|bubble_denotes_exists|boundRelationSpawn' VisualProof/Theory/Relation.lean VisualProof/Diagram/Core.lean VisualProof/Diagram/Semantics.lean VisualProof/Diagram/Concrete/Core.lean VisualProof/Rule/Step.lean
```

Expected: the scan shows bound relation variables, intrinsic/concrete atoms, bubbles, existential bubble semantics, and bound-relation spawning.

- [x] **Step 5: Run authoritative builds and hygiene checks**

Run:

```bash
lake build
lake build VisualProof.Audit
git diff --check
git status --short
```

Expected: both builds succeed, the audit reports only accepted Lean axioms, diff checking passes, and only task-owned changes are present.

- [x] **Step 6: Commit the completed public surface**

```bash
git add VisualProof VisualProof.lean docs/superpowers/plans/2026-08-05-remove-definition-reference-macros.md
git commit -m "refactor(lean): complete definition-free calculus"
git status --porcelain
```

Expected: final status is empty.
