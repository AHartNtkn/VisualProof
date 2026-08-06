# Recursive Rewrite Authority Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make recursive open diagrams, relational rules, and structural semantics the mathematical authority, with flat diagrams, matching, and execution certified separately by representation and refinement theorems.

**Architecture:** `VisualProof.Diagram` owns recursive syntax, ordered open boundaries, renaming, isomorphism, contexts, and denotation. `VisualProof.Rule` owns proposition-valued rule families, their union `Step`, and semantic proofs stated only over recursive diagrams. `VisualProof.Concrete` owns flat data and algorithms; `VisualProof.Refinement` proves that checked representations, matches, and executions realize `Step`.

**Tech Stack:** Lean 4, Lake, the existing `VisualProof` library.

## Global Constraints

- TypeScript is outside the implementation, planning, and validation scope.
- Use ordinary names inside namespaces. Do not create symbol names prefixed with `Direct`, `Directed`, `Abstract`, or `Recursive` merely to distinguish layers.
- `Region` is the sole recursive syntax and the owner of recursive semantic arguments. `OpenDiagram` is a thin, nonrecursive mathematical boundary object: it records ordered boundary positions and their surjection onto the ambient wire classes of one closed-relation-context `Region`.
- Bound-wire renaming, boundary order, and repeated boundary aliases remain explicit. Boundary positions are occurrences; aliases never identify or reorder positions.
- A rule-specific theorem owns Region-level mathematics whenever removing boundary arguments and assignments leaves its premise and proof unchanged. Boundary-visible conclusions are then obtained through one generic open-body lift; do not create one bespoke open semantic proof per compiler or rule case.
- Keep genuinely open claims open: boundary quotient and alias laws, open substitution, boundary-preserving isomorphism, theorem interfaces, and concrete boundary transport. Do not mechanically convert every `denoteOpen` theorem to `denoteRegion`.
- Every rule family is a `Prop` relation. `Rule.Step` is the exhaustive inductive union of those family relations, not an executor request, result, trace, or closure.
- `Step.sound` states the required implication explicitly by orientation. It does not use a wrapper whose name encodes direction.
- `Step.sound` and every family soundness theorem must have a dependency closure containing no concrete diagram, matcher, executor, error, receipt, trace, carrier-numbering, or compiler declaration.
- Local rules use typed context decomposition modulo recursive diagram isomorphism. Context soundness must account for cut polarity; arbitrary contexts are not assumed monotone.
- Iteration, substitution, comprehension, and any other simultaneous or whole-diagram rule retain their simplest mathematical relation. They are not forced through one universal replacement relation.
- `Represents`, matcher correctness, and execution correctness live only in `VisualProof.Refinement`.
- Representation and execution completeness are proved with explicit quantifiers over requests and targets; rejection correctness applies only to fully specified domain-invalid requests, never resource or infrastructure failures.
- Do not encode or assert a fixed number of rules. Coverage is by `Step` constructors and family soundness cases.
- Follow theorem-driven RED/GREEN: complete every definition in an owning theorem's dependency closure; introduce `sorry` only in that theorem proof; compile RED; replace it with a kernel-checked proof; compile GREEN; commit.
- Do not preserve the execution-indexed rule model through aliases, adapters, compatibility modules, or re-exports.

## Target Module Ownership

| Module | Responsibility |
|---|---|
| `VisualProof/Diagram/Core.lean` | Finite recursive `Region`, `Item`, and `ItemSeq` syntax |
| `VisualProof/Diagram/Boundary.lean` | Thin nonrecursive `OpenDiagram`, ordered positions, and repeated-alias assignment |
| `VisualProof/Diagram/Rename.lean` | Bound-wire and boundary renaming/substitution |
| `VisualProof/Diagram/Isomorphism.lean` | Structural isomorphism and alpha-renaming laws |
| `VisualProof/Diagram/Semantics.lean` | Structural recursive denotation plus the single generic Region-to-open semantic lift |
| `VisualProof/Diagram/Context.lean` | Region-level typed one-hole contexts, filling, cut polarity, semantic transport |
| `VisualProof/Diagram/Occurrence.lean` | Relational occurrence as context decomposition modulo isomorphism |
| `VisualProof/Rule/Relation.lean` | Shared relation shape and orientation, with no execution data |
| `VisualProof/Rule/{Primitive,Structural,Identity,Erasure,Iteration,Substitution,Comprehension,Quantifier}.lean` | Mathematical rule-family relations and witnesses |
| `VisualProof/Rule/Step.lean` | Inductive union of the rule-family relations |
| `VisualProof/Rule/Soundness.lean` | Per-family imports and exhaustive `Step.sound` |
| `VisualProof/Concrete/{Diagram,Occurrence,Match,Step}.lean` | Flat checked representation, search, requests, receipts, errors, execution |
| `VisualProof/Refinement/{Represents,Match,Step}.lean` | Representation laws, matcher correctness, execution correctness |
| `VisualProof/Proof/{Replay,Theorem}.lean` | Proof programs that consume concrete execution plus refinement and abstract soundness |

## Existing Theorem Disposition

| Existing theorem family | Final ownership |
|---|---|
| Boundary representatives, alias consistency, boundary assignments, open substitution, and `OpenDiagramIso` denotation | Remain in the open-diagram kernel; their subject is the ordered-position-to-wire-class quotient |
| `denote_replaceOpenBody_mono` and `denote_replaceOpenBody_iff` in concrete splice tracing | Move their implementation-independent content beside `denoteOpen` as the single generic unchanged-boundary lift from Region implication/equivalence |
| `regionIso_fill_denotation` and its cast variant in concrete splice tracing | Move the general statement into recursive context/isomorphism algebra; it is Region mathematics despite its current location |
| `positive_erasure_sound`, `negative_insertion_sound`, identity join/sever, ancestor copy, contextual contraction, double-cut, and vacuous-bubble laws in `Rule/Structural/Semantics.lean` | Reuse as Region-level mathematical owners; family soundness derives from them |
| `comprehensionInstantiate_sound` and `comprehensionAbstract_context_sound` | Reuse as Region/context-level comprehension owners |
| `diagonalize_denotation` | Split into abstract Region substitution/diagonalization, the generic open substitution theorem, and concrete diagonal-representation refinement |
| Iteration `wholeOpen_equiv`, `sameSite_*`, contraction, route, and anchor theorems that first prove a `bodyEquiv` | Extract the declarative Region-level iteration law; retain open compiler conclusions only as refinement corollaries |
| `DirectionalBoundaryWitness`, heterogeneous `denoteOpen_lift`, rule-specific boundary witnesses, and compiled open-source equivalences | Keep under refinement ownership because they compare positional interfaces, alias partitions, or concrete compiler products |
| `TheoremSchema.Valid` and the final checked-theorem statement | Keep genuinely open, but make represented recursive open diagrams their operands and derive validity through replay refinement plus `Step.sound` |
| Concrete elaboration, compiler simulation, boundary witnesses, splice/reassembly equivalences, receipts, and replay | Keep boundary-visible, but move under concrete/refinement ownership; they certify an abstract step rather than define rule soundness |

The migration test is semantic, not textual: if deleting `args`, `boundary`, and `BoundaryAssignment` leaves the real hypothesis and proof unchanged, the owning theorem belongs over `Region`. If a theorem compares ordered arguments, alias partitions, or boundary transport, its open statement is genuine.

Do not mechanically replace the conclusion of every existing open theorem. For each rule family, introduce one declarative Region-level owner, derive any unchanged-interface open corollary through the generic lift, and retain specialized compiler-facing open theorems only when they prove representation or boundary transport. The migration is broad across rule families but narrow in new mathematics; iteration and splice contain the largest repeated open proof towers.

---

### Task 1: Stabilize recursive diagrams, isomorphism, and structural semantics

**Files:**
- Modify: `VisualProof/Diagram/Core.lean`
- Modify: `VisualProof/Diagram/Boundary.lean`
- Modify: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Extract generic lemmas from: `VisualProof/Diagram/Concrete/Subgraph/Splice/Trace.lean`

**Interfaces:**
- Consumes: existing `Region`, `Item`, `ItemSeq`, `OpenDiagram`, `BoundaryAssignment`, and `denoteOpen`.
- Produces: the final recursive syntax; thin open-interface completion; structural `Isomorphic`; open-diagram isomorphism; renaming, substitution, freshness, denotation invariance, and one generic Region-to-open semantic lift.

- [ ] **Step 1: Make the mathematical identities explicit in the existing recursive syntax**

Keep `Region`, `Item`, and `ItemSeq` finite and structurally recursive. Keep `OpenDiagram.boundary : Fin arity → Fin externalClasses`; do not replace it with a set or map. Add the general alias law:

```lean
theorem BoundaryAssignment.equal_of_alias
    (assignment : BoundaryAssignment d D)
    (h : d.boundary i = d.boundary j) :
    assignment.args i = assignment.args j
```

Order is already intrinsic in the `Fin arity` domain. Do not add any quotient, `Finset`, sorting, or deduplication of boundary positions.

Add the boundary-preserving body replacement used by occurrence filling and generic semantic lifting:

```lean
def OpenDiagram.withBody
    (diagram : OpenDiagram arity)
    (body : Region diagram.externalClasses []) : OpenDiagram arity := {
  diagram with body := body
}
```

`withBody` is not recursive syntax and introduces no second context type. It preserves the existing ordered boundary and alias partition exactly.

- [ ] **Step 2: Complete renaming and substitution definitions before RED**

Ensure `Rename.lean` contains total definitions for bound-wire renaming, relation-variable renaming, boundary substitution, support, freshness, and capture avoidance. Definitions must recurse on `Region`/`Item`/`ItemSeq` and must not call concrete elaboration or canonicalization.

- [ ] **Step 3: RED/GREEN structural isomorphism laws**

Own these production theorem shapes in `Isomorphism.lean`:

```lean
theorem Isomorphic.refl (d : Region wires rels) : Isomorphic d d
theorem Isomorphic.symm : Isomorphic a b → Isomorphic b a
theorem Isomorphic.trans : Isomorphic a b → Isomorphic b c → Isomorphic a c

theorem Isomorphic.rename
    (h : Isomorphic a b) :
    Isomorphic (a.rename wires rels) (b.rename wires rels)

theorem Isomorphic.substitute
    (h : Isomorphic a b) :
    Isomorphic (a.substitute σ) (b.substitute σ)
```

For each owning theorem: introduce only its proof as `by sorry`, compile the file, confirm the remaining `sorry` is that theorem proof, then replace it with the kernel proof and recompile.

- [ ] **Step 4: RED/GREEN denotation invariance**

Keep denotation defined by mutual structural recursion in `Semantics.lean`. Prove:

```lean
theorem Isomorphic.denote_iff
    (h : Isomorphic a b)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteRegion model env rels a ↔ denoteRegion model env rels b

theorem OpenDiagramIso.denote_iff
    (h : OpenDiagramIso source target)
    (model : Model)
    (args : Fin arity → model.Carrier) :
    denoteOpen model source args ↔ denoteOpen model target args
```

`OpenDiagramIso` must preserve boundary positions pointwise or carry an explicit `Fin` equivalence used to transport `args`; alias equality alone cannot authorize a permutation.

- [ ] **Step 5: Extract the single generic open-body lift**

Move the mathematical content of the current `denote_replaceOpenBody_mono` and `denote_replaceOpenBody_iff` out of concrete splice tracing and prove it once beside open semantics:

```lean
theorem OpenDiagram.denote_body
    (h : ∀ env,
      denoteRegion model env PUnit.unit before →
        denoteRegion model env PUnit.unit after) :
    denoteOpen model (diagram.withBody before) args →
      denoteOpen model (diagram.withBody after) args

theorem OpenDiagram.denote_body_iff
    (h : ∀ env,
      denoteRegion model env PUnit.unit before ↔
        denoteRegion model env PUnit.unit after) :
    denoteOpen model (diagram.withBody before) args ↔
      denoteOpen model (diagram.withBody after) args
```

Every unchanged-interface rule lift uses these theorems. Rule-specific compiler certificates, splice traces, and boundary reconstructions may prove their Region premise or target representation, but they do not re-prove this semantic passage.

- [ ] **Step 6: Validate and commit**

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Isomorphism.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/OpenIsomorphism.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/Semantics.lean
lake build
git diff --check
```

Commit:

```bash
git add VisualProof/Diagram/Core.lean VisualProof/Diagram/Boundary.lean VisualProof/Diagram/Rename.lean VisualProof/Diagram/Isomorphism.lean VisualProof/Diagram/OpenIsomorphism.lean VisualProof/Diagram/Semantics.lean
git commit -m "Establish recursive diagram semantics"
```

### Task 2: Define contexts and relational occurrence evidence

**Files:**
- Modify: `VisualProof/Diagram/Context.lean`
- Create: `VisualProof/Diagram/Occurrence.lean`
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `Region`, `OpenDiagram`, `Isomorphic`, `OpenDiagramIso`, and structural denotation.
- Produces: Region-level `DiagramContext.fill`, `Occurrence`, isomorphism transport, capture laws, and polarity-aware semantic transport.

- [ ] **Step 1: Complete one-hole filling and polarity definitions**

Retain the recursive `DiagramContext` shape. It contains only recursive frames and a Region hole; do not add boundary positions or an `OpenContext`. The open interface is attached once, after filling, by `OpenDiagram.withBody` from Task 1.

```lean
inductive Polarity
  | positive
  | negative

def DiagramContext.polarity (context : DiagramContext ow hw or hr) : Polarity :=
  if context.cutDepth % 2 = 0 then .positive else .negative
```

- [ ] **Step 2: RED/GREEN context isomorphism and capture laws**

Prove:

```lean
theorem DiagramContext.fill_iso
    (h : Isomorphic a b) :
    Isomorphic (context.fill a) (context.fill b)

theorem OpenDiagram.withBody_fill_iso
    (h : Isomorphic a b) :
    OpenDiagramIso
      (host.withBody (context.fill a))
      (host.withBody (context.fill b))

theorem DiagramContext.fill_fresh
    (h : FreshFor name body) :
    FreshFor name (context.fill body)
```

Do not assert that implication is preserved by every context.

- [ ] **Step 3: RED/GREEN polarity-aware semantic transport**

Prove the explicit theorem, without a direction-named wrapper:

```lean
theorem DiagramContext.denote_fill
    (context : DiagramContext ow hw or hr)
    (h : ∀ env rels,
      match context.polarity with
      | .positive => denoteRegion model env rels before →
          denoteRegion model env rels after
      | .negative => denoteRegion model env rels after →
          denoteRegion model env rels before) :
    ∀ outerEnv outerRels,
      match context.polarity with
      | .positive =>
          denoteRegion model outerEnv outerRels (context.fill before) →
          denoteRegion model outerEnv outerRels (context.fill after)
      | .negative =>
          denoteRegion model outerEnv outerRels (context.fill after) →
          denoteRegion model outerEnv outerRels (context.fill before)
```

- [ ] **Step 4: Define occurrence as relational decomposition evidence**

In `Occurrence.lean`:

```lean
structure Occurrence
    (pattern : Region holeWires holeRels)
    (host : OpenDiagram arity) : Prop where
  context : DiagramContext host.externalClasses holeWires [] holeRels
  host_iso : OpenDiagramIso host
    (host.withBody (context.fill pattern))
  polarity : Polarity
  polarity_eq : polarity = context.polarity
```

Add isomorphism transport theorems for host and pattern. Do not prove occurrence uniqueness; automorphisms may yield multiple valid decompositions.

- [ ] **Step 5: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Context.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/Occurrence.lean
lake build
git diff --check
git add VisualProof/Diagram/Context.lean VisualProof/Diagram/Occurrence.lean VisualProof/Diagram/Algebra.lean VisualProof.lean
git commit -m "Define recursive diagram occurrences"
```

### Task 3: Replace execution-indexed steps with relational rule infrastructure

**Files:**
- Create: `VisualProof/Rule/Relation.lean`
- Replace: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: recursive open diagrams, contexts, occurrences, and isomorphism.
- Produces: `Orientation`, `Rule`, `Contextual`, and an execution-free `Step` relation.

- [ ] **Step 1: Define the shared relation shapes**

```lean
namespace VisualProof.Rule

inductive Orientation
  | forward
  | backward

abbrev Rule :=
  {arity : Nat} → Orientation → OpenDiagram arity → OpenDiagram arity → Prop

def Contextual
    (local : ∀ {wires rels},
      Orientation → Region wires rels → Region wires rels → Prop)
    (orientation : Orientation)
    (source target : OpenDiagram arity) : Prop :=
  ∃ wires rels before after
    (occurrence : Occurrence before source),
      local orientation before after ∧
      occurrence.polarity =
        (match orientation with
         | .forward => .positive
         | .backward => .negative) ∧
      OpenDiagramIso target
        (source.withBody (occurrence.context.fill after))
```

Define the legality relation in the same module:

```lean
def Allowed : Orientation → Polarity → Prop
  | .forward, .positive => True
  | .backward, .negative => True
  | _, _ => False
```

- [ ] **Step 2: Define the family-level union**

Replace the current `Step (input : CheckedDiagram)` with:

```lean
inductive Step :
    Orientation → OpenDiagram arity → OpenDiagram arity → Prop
  | primitive : Primitive orientation source target → Step orientation source target
  | structural : Structural orientation source target → Step orientation source target
  | identity : Identity orientation source target → Step orientation source target
  | erasure : Erasure orientation source target → Step orientation source target
  | iteration : Iteration orientation source target → Step orientation source target
  | substitution : Substitution orientation source target → Step orientation source target
  | comprehension : Comprehension orientation source target → Step orientation source target
  | quantifier : Quantifier orientation source target → Step orientation source target
```

Do not add tags, inventories, semantic modes, requests, errors, receipts, selections, or concrete witnesses to this module.

- [ ] **Step 3: Add isomorphism closure**

```lean
theorem Step.iso
    (hs : OpenDiagramIso source source')
    (h : Step orientation source target)
    (ht : OpenDiagramIso target target') :
    Step orientation source' target'
```

This theorem depends on per-family isomorphism transport and is completed after Tasks 4 and 5; its declaration may not contain `sorry` until those definitions and transport theorems are complete.

- [ ] **Step 4: Compile structural setup and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Relation.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Step.lean
git diff --check
git add VisualProof/Rule/Relation.lean VisualProof/Rule/Step.lean VisualProof.lean
git commit -m "Define relational proof steps"
```

### Task 4: State and prove the local rule families

**Files:**
- Create: `VisualProof/Rule/Primitive.lean`
- Replace: `VisualProof/Rule/Structural.lean`
- Create: `VisualProof/Rule/Identity.lean`
- Create: `VisualProof/Rule/Erasure.lean`
- Create: `VisualProof/Rule/Quantifier.lean`
- Modify: `VisualProof/Rule/Structural/Semantics.lean`
- Create: `VisualProof/Rule/Soundness/Primitive.lean`
- Replace: `VisualProof/Rule/Soundness/Structural.lean`
- Create: `VisualProof/Rule/Soundness/Identity.lean`
- Create: `VisualProof/Rule/Soundness/Erasure.lean`
- Create: `VisualProof/Rule/Soundness/Quantifier.lean`

**Interfaces:**
- Consumes: `Rule.Contextual`, recursive syntax, polarity, scope, freshness, and isomorphism.
- Produces: proposition-valued local relations and one soundness theorem per family.

- [ ] **Step 1: Define each local relation from mathematical witnesses only**

Use this shape for every constructor listed below:

```lean
namespace Erasure

inductive Local :
    Orientation → Region wires rels → Region wires rels → Prop
  | erase
      (erasable : Erasable removable)
      (allowed : Allowed orientation polarity) :
      Local orientation (conjoin retained removable) retained

def Rel : Rule := fun orientation source target =>
  Contextual (@Local) orientation source target

end Erasure
```

The family constructors are:

| Family | Constructors | Relation form |
|---|---|---|
| `Primitive` | `spawn` | local relation plus scope and binder legality |
| `Structural` | `doubleCutIntro`, `doubleCutElim` | local relation with polarity legality |
| `Identity` | `join`, `sever` | local relation with ordered endpoint/gluing evidence |
| `Erasure` | `erase` | local relation with an `Erasable` witness |
| `Quantifier` | `intro`, `elim` | binder-local relation with freshness and capture evidence |

Each constructor owns a recursive source, recursive target, and its mathematical legality witnesses. Do not share a universal graph-replacement payload.

- [ ] **Step 2: Prove isomorphism transport for each family**

Each module provides:

```lean
theorem Erasure.iso
    (hs : OpenDiagramIso source source')
    (h : Erasure orientation source target)
    (ht : OpenDiagramIso target target') :
    Erasure orientation source' target'
```

- [ ] **Step 3: RED/GREEN the Region-level semantic owner for each family**

After its relation and dependencies compile without incomplete definitions, state the mathematical theorem over the local `Region` relation and arbitrary environments. Reuse the existing Region theorems in `Rule/Structural/Semantics.lean` rather than cloning their proofs. The owning shape is:

```lean
theorem Erasure.Local.sound
    (h : Erasure.Local orientation before after) :
    ∀ model env relEnv,
    match orientation with
    | .forward =>
        denoteRegion model env relEnv before →
          denoteRegion model env relEnv after
    | .backward =>
        denoteRegion model env relEnv after →
          denoteRegion model env relEnv before
```

Use the same ownership rule for primitive, structural, identity, and quantifier mathematics. Each owning proof has no boundary arguments, `BoundaryAssignment`, open compiler witness, or concrete certificate.

- [ ] **Step 4: Derive contextual and open family soundness**

First derive Region-level contextual soundness with `DiagramContext.denote_fill`. Then derive the boundary-visible family theorem:

```lean
theorem Erasure.sound
    (h : Erasure orientation source target) :
    match orientation with
    | .forward => ∀ model args,
        denoteOpen model source args → denoteOpen model target args
    | .backward => ∀ model args,
        denoteOpen model target args → denoteOpen model source args
```

The open proof performs no rule-specific semantic reasoning: destruct the occurrence; transport through source isomorphism; apply the Region-level contextual theorem; invoke `OpenDiagram.denote_body`; transport through target isomorphism. This open theorem is a family interface consumed by `Step.sound`, not the owner of the mathematical rule proof.

- [ ] **Step 5: Validate and commit each independently reviewable family**

For each `Family` in `Primitive Structural Identity Erasure Quantifier`:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Family.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Family.lean
```

Commit one family at a time with `git commit -m "Prove <family> relation sound"`.

### Task 5: State and prove whole-diagram and simultaneous rule families

**Files:**
- Create: `VisualProof/Rule/Iteration.lean`
- Create: `VisualProof/Rule/Substitution.lean`
- Replace: `VisualProof/Rule/Comprehension.lean`
- Create: `VisualProof/Rule/Soundness/Iteration.lean`
- Create: `VisualProof/Rule/Soundness/Substitution.lean`
- Create: `VisualProof/Rule/Soundness/Comprehension.lean`
- Replace directory: `VisualProof/Rule/Soundness/Comprehension/`
- Extract Region-level iteration laws from: `VisualProof/Rule/Soundness/Iteration/**/*.lean`

**Interfaces:**
- Consumes: recursive diagrams, relational occurrences, renaming, freshness, capture avoidance, and denotation.
- Produces: family-owned whole-diagram relations and soundness proofs independent of concrete compilation.

- [ ] **Step 1: Define iteration as its mathematical whole-diagram relation**

```lean
inductive Iteration :
    Orientation → OpenDiagram arity → OpenDiagram arity → Prop
  | iterate
      (occurrences : IterationOccurrences source)
      (nonoverlap : occurrences.Nonoverlapping)
      (scope : occurrences.WellScoped)
      (result : Iterate source occurrences = target) :
      Iteration .forward source target
  | deiterate
      (occurrences : IterationOccurrences target)
      (nonoverlap : occurrences.Nonoverlapping)
      (scope : occurrences.WellScoped)
      (result : Iterate target occurrences = source) :
      Iteration .backward source target
```

The witness refers to recursive occurrences and the resulting recursive diagram. It does not refer to selection indices, traversal, extraction, splice traces, or executor state.

- [ ] **Step 2: Define simultaneous substitution**

```lean
structure Substitution.Site (source : OpenDiagram arity) where
  wires : Nat
  rels : RelCtx
  before : Region wires rels
  after : Region wires rels
  occurrence : Occurrence before source
  replacement : Substitutes before after

structure Substitution.Witness
    (orientation : Orientation)
    (source target : OpenDiagram arity) : Prop where
  sites : List (Substitution.Site source)
  nonoverlap : Nonoverlapping sites
  ordered : OrderedSites sites
  fresh : FreshReplacements sites
  capture_free : CaptureFree sites
  result : SubstituteAll source sites = target
  allowed : Allowed orientation (SitesPolarity sites)

def Substitution (orientation : Orientation)
    (source target : OpenDiagram arity) : Prop :=
  Nonempty (Substitution.Witness orientation source target)
```

Use indexed or vector-valued `Filling` in the final Lean definition so each hole's wire and relation indices are preserved.

- [ ] **Step 3: Define comprehension independently**

```lean
structure Comprehension.Witness
    (orientation : Orientation)
    (source target : OpenDiagram arity) : Prop where
  occurrences : OccurrenceFamily source
  nonoverlap : occurrences.Nonoverlapping
  interface : OrderedInterface occurrences
  fresh : FreshBinder source
  capture_free : CaptureFree occurrences
  result : Comprehend source occurrences interface fresh = target
  allowed : Allowed orientation occurrences.polarity

def Comprehension (orientation : Orientation)
    (source target : OpenDiagram arity) : Prop :=
  Nonempty (Comprehension.Witness orientation source target)
```

Do not reuse substitution's witness merely because both are simultaneous.

- [ ] **Step 4: Extract one mathematical owner per family, then RED/GREEN family soundness**

For iteration, extract the Region/context proposition currently proved as `bodyEquiv` inside contraction, same-site, route, and anchor compiler theorems. State and prove that proposition from the declarative iteration witness; do not retain compiler certificates, compiled sources, routes, anchors, or splice traces in its premises.

For substitution and comprehension, make recursive renaming, simultaneous filling, freshness, and capture avoidance the theorem premises. Reuse `comprehensionInstantiate_sound` and `comprehensionAbstract_context_sound` as Region/context owners. Split the current diagonalization result into:

1. a Region-level substitution/diagonalization theorem;
2. `OpenDiagram.denote_substituteBoundary` for the positional lift;
3. a later refinement theorem proving that the concrete diagonal witness represents that substitution.

Each family then exposes the open implication required by `Step.sound` by using the generic Region-to-open lift from Task 1. Compiler, occurrence extraction, and splice correctness appear only in refinement. Do not create a Region duplicate for every existing `wholeOpen_equiv` or compiled-source theorem.

- [ ] **Step 5: Validate and commit by family**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Iteration.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Iteration.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Substitution.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Substitution.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Comprehension.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Comprehension.lean
```

Commit each family separately.

### Task 6: Prove the exhaustive abstract step theorem

**Files:**
- Modify: `VisualProof/Rule/Step.lean`
- Replace: `VisualProof/Rule/Soundness.lean`
- Remove: `VisualProof/Rule/Soundness/All.lean`
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`

**Interfaces:**
- Consumes: every family relation and soundness theorem.
- Produces: `Step.iso` and `Step.sound` with no concrete dependency.

- [ ] **Step 1: Complete `Step.iso` by constructor exhaustion**

Each case delegates to the corresponding family `iso` theorem.

- [ ] **Step 2: RED the owning theorem**

```lean
theorem Step.sound
    (h : Step orientation source target) :
    match orientation with
    | .forward => ∀ model args,
        denoteOpen model source args → denoteOpen model target args
    | .backward => ∀ model args,
        denoteOpen model target args → denoteOpen model source args
```

At RED, all definitions and family soundness theorems in the dependency closure are complete; the only new `sorry` is the proof of `Step.sound`.

- [ ] **Step 3: GREEN by cases on `h`**

The proof has one case per family constructor and delegates directly to that family's soundness theorem. It performs no execution, matching, translation, or concrete semantic reasoning.

- [ ] **Step 4: Add kernel and dependency audits**

Update the existing `VisualProof/Audit.lean` to import `VisualProof.Rule.Soundness` and issue:

```lean
#print axioms VisualProof.Rule.Step.sound
```

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake env lean --deps VisualProof/Rule/Soundness.lean
```

The resolved dependency list must not include `VisualProof.Diagram.Concrete`, `VisualProof.Concrete`, or `VisualProof.Refinement`.

- [ ] **Step 5: Commit**

```bash
git add VisualProof/Rule/Step.lean VisualProof/Rule/Soundness.lean VisualProof/Rule/Soundness/All.lean VisualProof.lean VisualProof/Audit.lean
git commit -m "Prove relational step soundness"
```

### Task 7: Move flat data and executable rewriting into the concrete namespace

**Files:**
- Create: `VisualProof/Concrete/Diagram.lean`
- Create: `VisualProof/Concrete/Occurrence.lean`
- Create: `VisualProof/Concrete/Match.lean`
- Create: `VisualProof/Concrete/Step.lean`
- Migrate: `VisualProof/Diagram/Concrete/**/*.lean`
- Migrate operational declarations from: `VisualProof/Rule/Step.lean`
- Migrate executor from: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: core signature/boundary data needed to type flat representations.
- Produces: `Concrete.Diagram`, `Concrete.OpenDiagram`, `Concrete.Checked`, `Concrete.Occurrence`, `Concrete.Match`, `Concrete.Step`, `Concrete.Error`, `Concrete.Receipt`, `Concrete.execute`.

- [ ] **Step 1: Move concrete types without compatibility aliases**

Move the complete structures and predicates from `VisualProof/Diagram/Concrete/Core.lean`, `VisualProof/Diagram/Concrete/Open.lean`, and `VisualProof/Diagram/Concrete/WellFormed.lean` into `VisualProof/Concrete/Diagram.lean`. Preserve every field and invariant while renaming only by namespace:

| Current declaration | Final declaration |
|---|---|
| `Diagram.ConcreteDiagram` | `Concrete.Diagram` |
| `Diagram.OpenConcreteDiagram` | `Concrete.OpenDiagram` |
| `Diagram.CheckedDiagram` | `Concrete.Checked` |
| `Diagram.CheckedOpenDiagram` | `Concrete.CheckedOpen` |
| `Diagram.ConcreteDiagram.WellFormed` | `Concrete.Diagram.WellFormed` |
| `Diagram.OpenConcreteDiagram.WellFormed` | `Concrete.OpenDiagram.WellFormed` |

Rename dependents mechanically; do not leave aliases behind.

- [ ] **Step 2: Move matcher/search declarations**

The concrete matcher returns only concrete candidates:

```lean
def Concrete.match
    (host pattern : Concrete.OpenDiagram) :
    List (Concrete.Match host pattern)
```

No abstract `Occurrence` is defined by this function.

- [ ] **Step 3: Move requests, errors, receipts, and execution**

Move the current request constructors from the former execution-indexed `Rule.Step` into `Concrete.Step`, preserving their checked finite references. Move `StepError` to `Concrete.Error`, `StepReceipt` to `Concrete.Receipt`, and `applyStep` to:

```lean
def Concrete.execute
    (orientation : Rule.Orientation)
    (input : Concrete.Checked)
    (request : Concrete.Step input) :
    Except Concrete.Error (Concrete.Receipt input)
```

These declarations do not export semantic theorems.

- [ ] **Step 4: Compile the concrete layer independently**

```bash
lake env lean -DwarningAsError=true VisualProof/Concrete/Diagram.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Occurrence.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Match.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Step.lean
lake build
```

- [ ] **Step 5: Commit**

Stage every migrated Lean file under `VisualProof/Concrete/` and every removed old path, then commit:

```bash
git commit -m "Separate concrete rewriting implementation"
```

### Task 8: Define representation and prove its laws

**Files:**
- Create: `VisualProof/Refinement/Represents.lean`
- Migrate: `VisualProof/Diagram/Concrete/Elaboration/Compile/Certified.lean`
- Migrate: `VisualProof/Diagram/Concrete/Elaboration/Simulation.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `Concrete.Checked`, `Concrete.OpenDiagram`, recursive `OpenDiagram`, elaboration/translation, and recursive isomorphism.
- Produces: `Represents`, checked representation existence, meaning uniqueness modulo isomorphism, and representation coverage.

- [ ] **Step 1: Define the relation independently of execution**

```lean
def Represents
    (concrete : Concrete.OpenDiagram)
    (diagram : Diagram.OpenDiagram concrete.boundary.length) : Prop :=
  ∃ checked : concrete.diagram.WellFormed,
    Diagram.OpenDiagramIso
      (Concrete.elaborate ⟨concrete, checked⟩)
      diagram
```

The final definition must also expose that the boundary list and its repeated entries correspond positionwise; this may be carried by `OpenDiagramIso` if that theorem already proves it.

- [ ] **Step 2: RED/GREEN checked representation existence**

```lean
theorem checked_represents
    (concrete : Concrete.CheckedOpen) :
    ∃ diagram, Represents concrete.val diagram
```

- [ ] **Step 3: RED/GREEN meaning uniqueness**

```lean
theorem represents_unique
    (first : Represents concrete d₁)
    (second : Represents concrete d₂) :
    Diagram.OpenDiagramIso d₁ d₂
```

The conclusion is isomorphism, never Lean equality.

- [ ] **Step 4: RED/GREEN representation coverage**

Because the flat format is intended to implement the complete calculus, prove:

```lean
theorem representation_complete
    (diagram : Diagram.OpenDiagram arity) :
    ∃ concrete : Concrete.CheckedOpen,
      ∃ h : concrete.val.boundary.length = arity,
        Represents concrete.val (diagram.castArity h.symm)
```

- [ ] **Step 5: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Refinement/Represents.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake build
git diff --check
git add VisualProof/Refinement/Represents.lean VisualProof/Concrete/Elaboration VisualProof.lean VisualProof/Audit.lean
git commit -m "Prove concrete representation laws"
```

### Task 9: Prove matcher correctness against relational occurrence

**Files:**
- Create: `VisualProof/Refinement/Match.lean`
- Migrate proofs from: `VisualProof/Diagram/Concrete/Matcher/**/*.lean`
- Migrate proofs from: `VisualProof/Diagram/Concrete/Occurrence*.lean`
- Modify: `VisualProof/Audit.lean`

**Interfaces:**
- Consumes: `Represents`, recursive `Occurrence`, concrete matcher/candidates, and relevant concrete occurrence equivalence.
- Produces: `match_sound` and `match_complete` modulo declared isomorphisms.

- [ ] **Step 1: Define candidate meaning as a relation**

```lean
structure Concrete.Match.Represents
    (candidate : Concrete.Match host pattern)
    (occurrence : Diagram.Occurrence recursivePattern recursiveHost) : Prop where
  host : Refinement.Represents candidate.host recursiveHost
  pattern : Refinement.Represents candidate.pattern recursivePattern
  interface : candidate.boundary.length = recursivePatternArity
  order : BoundaryTransport candidate occurrence
  scope : ScopeTransport candidate occurrence
  embedding : EmbeddingTransport candidate occurrence
  reconstruction : ReconstructionTransport candidate occurrence
```

`BoundaryTransport`, `ScopeTransport`, `EmbeddingTransport`, and `ReconstructionTransport` are declared in this module as propositions over the existing concrete candidate certificates and the fields of `Diagram.Occurrence`; each definition is completed before `match_sound` enters RED.

Complete this definition before introducing either theorem.

- [ ] **Step 2: RED/GREEN matcher soundness**

```lean
theorem match_sound
    (hostRep : Represents host recursiveHost)
    (patternRep : Represents pattern recursivePattern)
    (found : candidate ∈ Concrete.match host pattern) :
    ∃ occurrence : Diagram.Occurrence recursivePattern recursiveHost,
      candidate.Represents occurrence
```

- [ ] **Step 3: RED/GREEN matcher completeness**

```lean
theorem match_complete
    (hostRep : Represents host recursiveHost)
    (patternRep : Represents pattern recursivePattern)
    (occurrence : Diagram.Occurrence recursivePattern recursiveHost) :
    ∃ candidate,
      candidate ∈ Concrete.match host pattern ∧
      candidate.Represents occurrence
```

Completeness may return an equivalent concrete match; it need not preserve carrier numbering or traversal order.

- [ ] **Step 4: Cover ordered aliases, renaming, and nested scope propositionally**

Prove general transport/reflection lemmas used by the two owning theorems. Do not add source-substring tests or example-only fixtures.

- [ ] **Step 5: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Refinement/Match.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake build
git diff --check
git add VisualProof/Refinement/Match.lean VisualProof/Concrete/Match.lean VisualProof/Concrete/Occurrence.lean VisualProof/Audit.lean
git commit -m "Prove concrete matcher correctness"
```

### Task 10: Prove execution refinement, completeness, and rejection correctness

**Files:**
- Create: `VisualProof/Refinement/Step.lean`
- Create: `VisualProof/Refinement/Step/Primitive.lean`
- Create: `VisualProof/Refinement/Step/Structural.lean`
- Create: `VisualProof/Refinement/Step/Identity.lean`
- Create: `VisualProof/Refinement/Step/Erasure.lean`
- Create: `VisualProof/Refinement/Step/Iteration.lean`
- Create: `VisualProof/Refinement/Step/Substitution.lean`
- Create: `VisualProof/Refinement/Step/Comprehension.lean`
- Create: `VisualProof/Refinement/Step/Quantifier.lean`
- Migrate implementation proofs from: `VisualProof/Rule/Soundness/**/*.lean`
- Modify: `VisualProof/Audit.lean`

**Interfaces:**
- Consumes: `Concrete.execute`, `Concrete.Step`, `Concrete.Receipt`, `Represents`, matcher correctness, family relations, and `Rule.Step`.
- Produces: `execute_sound`, `execute_complete`, and `execute_rejects_only_invalid`.

- [ ] **Step 1: Define request meaning without semantic claims**

```lean
def Requested
    (orientation : Rule.Orientation)
    (source : Diagram.OpenDiagram arity)
    (request : Concrete.Step concrete)
    (target : Diagram.OpenDiagram arity) : Prop :=
  Rule.Step orientation source target ∧ RequestWitness request source target
```

`RequestWitness` relates concrete indices/selections to the mathematical witnesses of the appropriate family. It contains no denotation.

- [ ] **Step 2: RED/GREEN execution soundness**

```lean
theorem execute_sound
    (sourceRep : Represents sourceConcrete.asOpen source)
    (success : Concrete.execute orientation sourceConcrete request = .ok receipt) :
    ∃ target,
      Rule.Step orientation source target ∧
      Represents receipt.result.asOpen target
```

The migrated compiler, traversal, splice, attachment, and carrier-numbering proofs discharge `RequestWitness` and target representation only.

Classify the existing open theorem towers while migrating them:

- `DirectionalBoundaryWitness`, heterogeneous `denoteOpen_lift`, open elaboration simulation, and rule-specific boundary witnesses remain refinement infrastructure because they compare positional interfaces or transport alias partitions.
- iteration `wholeOpen_equiv`, same-site, route, anchor, contraction, compiled-source, splice, and reassembly theorems become representation or `RequestWitness` lemmas. Their Region `bodyEquiv` argument is supplied by the abstract iteration theorem from Task 5.
- concrete comprehension diagonal, attachment, and terminal-environment theorems prove that the generated concrete target represents the abstract substitution or comprehension result.
- receipt and replay theorems consume `execute_sound` and `Step.sound`; they never serve as the owning proof of a rule family.

The generic unchanged-interface lift belongs to `Diagram.Semantics`; the heterogeneous boundary simulations in this task remain concrete/refinement theorems. Do not conflate those two responsibilities merely because both conclude with `denoteOpen`.

- [ ] **Step 3: RED/GREEN execution completeness**

```lean
theorem execute_complete
    (sourceRep : Represents sourceConcrete.asOpen source)
    (step : Rule.Step orientation source target) :
    ∃ request receipt,
      Concrete.execute orientation sourceConcrete request = .ok receipt ∧
      Represents receipt.result.asOpen target
```

The request is existential because the executor is deterministic only after a request supplies the chosen abstract application.

- [ ] **Step 4: Separate domain rejection from operational failure**

Define `Concrete.Error.invalid` for fully specified domain-invalid requests separately from unsupported operations, cancellation, resource limits, and internal failures. Prove only:

```lean
theorem execute_rejects_only_invalid
    (sourceRep : Represents sourceConcrete.asOpen source)
    (rejected : Concrete.execute orientation sourceConcrete request =
      .error .invalid) :
    ¬ ∃ target, Requested orientation source request target
```

- [ ] **Step 5: Derive semantic preservation as a corollary**

```lean
theorem execute_preserves
    (sourceRep : Represents sourceConcrete.asOpen source)
    (success : Concrete.execute orientation sourceConcrete request = .ok receipt) :
    ∃ target,
      Represents receipt.result.asOpen target ∧
      match orientation with
      | .forward => ∀ model args,
          denoteOpen model source args → denoteOpen model target args
      | .backward => ∀ model args,
          denoteOpen model target args → denoteOpen model source args
```

The proof is exactly `execute_sound` followed by `Rule.Step.sound`; it contains no rule-specific semantic argument.

- [ ] **Step 6: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Refinement/Step.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake build
git diff --check
git add VisualProof/Refinement/Step.lean VisualProof/Refinement/Step VisualProof/Concrete/Step.lean VisualProof/Audit.lean
git commit -m "Prove concrete execution refinement"
```

### Task 11: Make replay and theorem checking factor through refinement

**Files:**
- Modify: `VisualProof/Proof/Replay.lean`
- Modify: `VisualProof/Proof/Schema.lean`
- Modify: `VisualProof/Proof/Theorem.lean`
- Modify: `VisualProof/Proof/Theory.lean`

**Interfaces:**
- Consumes: concrete execution, `execute_sound`, `Step.sound`, representation uniqueness, and open-diagram isomorphism.
- Produces: replay and checked-theorem soundness without a concrete semantic authority.

- [ ] **Step 1: Replace replay's semantic record with represented recursive states**

The replay theorem should expose represented recursive endpoints and state the implication explicitly:

```lean
theorem applyOpenStep_sound
    (sourceRep : Represents input.asOpen source)
    (success : applyOpenStep orientation input action = .ok result) :
    ∃ target,
      Represents result.asOpen target ∧
      Rule.Step orientation source target
```

- [ ] **Step 2: Prove multi-step replay by composing `Rule.Step.sound` results**

Keep program execution concrete. The semantic proof inducts over the program, obtains each abstract step through refinement, uses representation uniqueness to align adjacent recursive representatives, and composes the explicit implications.

- [ ] **Step 3: RED/GREEN `checkedTheorem_sound`**

The theorem schema remains genuinely open: its proposition quantifies arguments in ordered boundary positions, including repeated aliases, and transports those arguments positionwise between its sides. Its operands are represented recursive `OpenDiagram`s rather than concrete diagrams. The proof uses replay refinement, `Step.sound`, and open-diagram isomorphism. It does not import concrete denotation or executor-specific family soundness.

- [ ] **Step 4: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Proof/Replay.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake build
git diff --check
git add VisualProof/Proof/Replay.lean VisualProof/Proof/Schema.lean VisualProof/Proof/Theorem.lean VisualProof/Proof/Theory.lean
git commit -m "Factor proof replay through refinement"
```

### Task 12: Remove the old authority and run the final Lean audit

**Files:**
- Remove superseded paths under: `VisualProof/Diagram/Concrete/`
- Remove superseded paths under: `VisualProof/Rule/Soundness/`
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `lakefile.toml`

**Interfaces:**
- Consumes: all completed abstract and refinement layers.
- Produces: one public import graph and final kernel/build evidence.

- [ ] **Step 1: Remove every superseded declaration and import path**

There must be no public or internal declaration of:

- an execution-indexed `VisualProof.Rule.Step`;
- rule tags or a fixed rule inventory as mathematical authority;
- semantic modes or direction-named implication wrappers;
- executor receipts/errors inside `VisualProof.Rule`;
- concrete denotation as a separately proved rule-soundness authority;
- compatibility aliases or re-exports for the former paths.

- [ ] **Step 2: Make the public import graph explicit**

`VisualProof.lean` imports the layers in this order:

```lean
import VisualProof.Diagram.Semantics
import VisualProof.Diagram.Occurrence
import VisualProof.Rule.Soundness
import VisualProof.Concrete.Step
import VisualProof.Refinement.Represents
import VisualProof.Refinement.Match
import VisualProof.Refinement.Step
import VisualProof.Proof.Theory
```

- [ ] **Step 3: Audit theorem axioms and dependency direction**

`VisualProof/Audit.lean` prints axioms for:

```lean
#print axioms VisualProof.Diagram.Isomorphic.denote_iff
#print axioms VisualProof.Rule.Step.sound
#print axioms VisualProof.Refinement.checked_represents
#print axioms VisualProof.Refinement.represents_unique
#print axioms VisualProof.Refinement.representation_complete
#print axioms VisualProof.Refinement.match_sound
#print axioms VisualProof.Refinement.match_complete
#print axioms VisualProof.Refinement.execute_sound
#print axioms VisualProof.Refinement.execute_complete
#print axioms VisualProof.Refinement.execute_rejects_only_invalid
#print axioms VisualProof.Proof.checkedTheorem_sound
```

No output may contain `sorryAx` or an unapproved project axiom.

- [ ] **Step 4: Run the complete Lean validation**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Represents.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Match.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Step.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake env lean --deps VisualProof/Rule/Soundness.lean
lake build
git diff --check
```

The `Rule/Soundness.lean` dependency closure must stop at recursive diagrams, contexts, rule relations, and structural semantics. The refinement closure may additionally include concrete diagrams, matching, execution, compiler traversal, and bookkeeping.

- [ ] **Step 5: Commit the completed migration**

```bash
git add VisualProof VisualProof.lean lakefile.toml
git commit -m "Complete recursive rewrite authority"
```

## Plan Acceptance Checklist

- [ ] Recursive syntax and denotation compile without concrete imports.
- [ ] `Region` is the only recursive diagram syntax; `OpenDiagram` contains only the ordered boundary quotient and one closed-relation-context Region body.
- [ ] Ordered boundary positions and repeated aliases are preserved propositionally.
- [ ] Rule-specific recursive semantics are owned by Region-level theorems and lifted through one generic open-body theorem.
- [ ] Boundary quotient, open substitution, open isomorphism, theorem-interface, and heterogeneous boundary-transport theorems remain genuinely open.
- [ ] Iteration and splice compiler theorem towers are refinement evidence for one declarative Region-level iteration law, not parallel semantic authorities.
- [ ] Isomorphism is structural/alpha equivalence, not semantic equality or concrete canonicalization.
- [ ] Contextual replacement accounts for polarity and capture avoidance.
- [ ] Occurrence is decomposition evidence, not matcher output.
- [ ] Whole-diagram and simultaneous rules own their mathematics.
- [ ] `Step` is a proposition-valued family union with no fixed-count claim.
- [ ] `Step.sound` is proved exhaustively and has no concrete dependencies.
- [ ] Concrete matching and execution prove refinement into `Step`.
- [ ] Representation uniqueness concludes isomorphism, not equality.
- [ ] Completeness and rejection theorems have the precise qualifiers stated above.
- [ ] Replay inherits semantics through refinement plus `Step.sound`.
- [ ] No compatibility authority remains.
- [ ] Every owning theorem passes RED/GREEN and final kernel audit.
