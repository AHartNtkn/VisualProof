# Recursive Rule Execution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace graph-based execution with computable indexed functional relations defined directly on recursive `OpenDiagram` syntax, proving that the union of each rule's forward family equals that rule and the union of its backward family equals the rule's converse.

**Architecture:** An `ExecutableFamily R` owns source-indexed request data, a total computable `apply` function, soundness, and completeness. Requests contain only recursive source decompositions and operation operands: never a target diagram or proof of `R`. Because the existing rules are invariant under `OpenDiagramIso`, family relations are functional on the quotient of recursive diagrams by `OpenDiagram.Isomorphic`; every rule witness factors through one computed canonical representative, making the family union exactly equal to the induced rule relation.

**Tech Stack:** Lean 4.30.0, Lake, the existing intrinsic `Region`/`Item`/`ItemSeq`/`OpenDiagram` syntax, `DiagramContext`, the five existing `Rule` relations, and their existing semantic soundness theorems.

## Global Constraints

- Interpret the requested reverse/“contrapositive” executable as the existing relational `Rule.converse R`; do not introduce a second notion of reverse execution.
- Remove the graph representation and its execution/refinement dependents before adding recursive executables. Do not retain aliases, adapters, re-exports, compatibility modules, or dual authorities.
- An executable request may contain source decomposition evidence, finite maps, and rule operands. It must not contain a target `OpenDiagram`, `Rule`/`Rule.Step` evidence, a `ContextReplacement`, or an `OpenDiagramIso`.
- Each indexed relation is definitionally the graph of one total `apply` function on recursive-diagram isomorphism classes. Applicability belongs in the source-indexed request type, not in an error enum or a success-shaped fallback.
- `apply` definitions must be ordinary computable `def`s. `noncomputable`, `Classical.choice`, target search, target occurrence discovery, and semantic denotation are forbidden in executable modules.
- Soundness may construct proof-only `ContextReplacement`, `NestedContextReplacement`, and isomorphism witnesses after the target has been computed.
- Prove both inclusions for every direction: family-member soundness and rule-witness completeness. The exported theorem must state equality between the family union and the induced rule relation on recursive-diagram isomorphism classes.
- Reject the vacuous empty-family solution structurally: each rule has concrete request constructors, and `complete` must extract one of them from every corresponding rule witness.
- Follow theorem-driven RED/GREEN. Supporting definitions compile before the owning soundness theorem is entered with `sorry`; GREEN removes that sole `sorry` before the task is committed.
- Do not add heartbeat or recursion-depth overrides. If a proof needs duplicated traversal, dependent target reconciliation, or growing cast/HEq infrastructure, stop that task, restore its last GREEN boundary, and redesign the request or theorem boundary.
- Preserve all unrelated TypeScript and test changes in the shared worktree. Stage and commit only the task-owned Lean, audit, and plan files.

## Complexity Ledger

- **Essential behavior:** five recursive rule relations; a computable forward family whose union equals each relation; a computable backward family whose union equals its converse; aggregate one-step execution; proof replay; semantic soundness through the existing `Rule.Step.sound`.
- **Essential state:** the recursive source diagram, execution direction, an exact recursive site/nested-site decomposition, and the operands that select one member of a nondeterministic rule family.
- **Integrity constraints:** one request determines one target class; every indexed graph member lies in the selected directed rule; every directed rule witness yields an index and the same endpoint classes; boundaries remain ordered; wire/relation renamings remain well typed; contextual polarity is derived from the supplied recursive context.
- **Derived data:** target diagrams, filled contexts, local before/after regions, `ContextReplacement` witnesses, aggregate `Rule.Step` evidence, replay endpoints, and theorem validity.
- **Accidental state to remove:** graph identifiers, checked graph wrappers, receipts, survivor domains, allocation layouts, compiler results, encoded/elaborated mirrors, and representation witnesses.
- **Accidental control to remove:** graph selection/removal/splice pipelines, compilation replay, target reconstruction, refinement dispatch, operation error plumbing, and generated step-tag execution.
- **Code volume:** the current graph/execution/proof bridge is 66 Lean files and about 42,000 lines. The replacement is bounded to one generic contract, two exact recursive decomposition types, five rule modules, one aggregate, and the recursive proof layer.
- **Power leaks prohibited:** generic transformation/simulation records, matchers hidden inside soundness, arbitrary relation evidence as an index, caller-supplied targets, and a second syntax or navigation authority.

## Target File Structure

### Retained authorities

- `VisualProof/Diagram/**`: intrinsic recursive syntax, contexts, paths, isomorphisms, replacements, and semantics.
- `VisualProof/Rule/{Relation,Erasure,WireSever,Iteration,DoubleCut,Vacuity,Step}.lean`: mathematical rule relations.
- `VisualProof/Rule/Soundness.lean` and `VisualProof/Rule/Soundness/**`: semantic soundness.

### New executable authority

- `VisualProof/Diagram/Rewrite.lean`: exact source-side contextual and nested contextual decompositions plus deterministic fill operations.
- `VisualProof/Rule/Executable/Core.lean`: recursive-diagram isomorphism quotient, invariant-rule lifting, direction, indexed-family contract, functionality, completeness, and exact union theorem.
- `VisualProof/Rule/Executable/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`: rule-specific request types, `apply`, and soundness.
- `VisualProof/Rule/Executable/Step.lean`: exhaustive five-family request sum and aggregate executor.
- `VisualProof/Rule/Executable.lean`: import-only public executable umbrella.

### Rebuilt proof authority

- `VisualProof/Proof/{Schema,Replay,Theorem,Theory}.lean`: recursive schemas, programs, replay, checked theorems, and semantic validity.
- `VisualProof/ComputabilityAudit.lean`: compiler checks for all recursive executable functions.
- `VisualProof/Audit.lean`: axiom audit for rule soundness and checked-theorem validity.

### Removed authority

- `VisualProof/Concrete.lean` and `VisualProof/Concrete/**`.
- `VisualProof/Refinement/**`.
- The graph-dependent contents of `VisualProof/Proof/**`.
- The `visualproof_step_tags` executable target in `lakefile.toml`.

---

### Task 1: Delete the graph execution authority and restore a recursive-only build

**Files:**
- Delete: `VisualProof/Concrete.lean`
- Delete: `VisualProof/Concrete/**`
- Delete: `VisualProof/Refinement/**`
- Delete: `VisualProof/Proof/Schema.lean`
- Delete: `VisualProof/Proof/Replay.lean`
- Delete: `VisualProof/Proof/Theorem.lean`
- Delete: `VisualProof/Proof/Theory.lean`
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`
- Delete: `VisualProof/ComputabilityAudit.lean`
- Modify: `lakefile.toml`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `docs/goals/recursive-rewrite-authority/goal.md`

**Interfaces:**
- Consumes: the independent recursive `Diagram`, `Rule`, and `Rule.Soundness` modules.
- Produces: a project whose only rewriting authority is `Rule.Step`; a rules audit that rejects imports from future executable/proof modules back into mathematical rules.

- [ ] **Step 1: Record the deletion baseline without touching unrelated work**

Run:

```bash
git status --short
find VisualProof/Concrete VisualProof/Refinement VisualProof/Proof -type f -name '*.lean' -print | sort
rg -n '^import VisualProof\.(Concrete|Refinement|Proof)' VisualProof VisualProof.lean
```

Expected: only the known unrelated TypeScript/test files are dirty; recursive rule imports do not depend on `Concrete`, `Refinement`, or `Proof`.

- [ ] **Step 2: Remove the graph execution closure**

Run `git rm` on `VisualProof/Concrete.lean`, the complete `VisualProof/Concrete/` and `VisualProof/Refinement/` trees, and the four graph-dependent `VisualProof/Proof/*.lean` files. Delete `VisualProof/ComputabilityAudit.lean`; it will be recreated only after executable functions exist.

- [ ] **Step 3: Narrow the public and build roots**

Make `VisualProof.lean` import the recursive `Theory`, `Data`, `Diagram`, `Rule`, and `Rule.Soundness` modules only. Remove the `[[lean_exe]] visualproof_step_tags` stanza from `lakefile.toml`. Change `VisualProof/Audit.lean` to import `VisualProof` and print axioms for the existing semantic and `Rule.Step.sound` theorems only.

- [ ] **Step 4: Replace the audit boundary**

In `scripts/audit-lean-authority.sh`, retain the exact five-constructor `Rule.Step` roster and recursive rule dependency checks. Remove graph-operation, receipt, step-tag, representation, and refinement rosters. Add a check that files in `VisualProof/Rule/` other than `VisualProof/Rule/Executable/**` do not import `VisualProof.Rule.Executable` or `VisualProof.Proof`.

- [ ] **Step 5: Update the active architecture objective**

Rewrite `docs/goals/recursive-rewrite-authority/goal.md` so its oracle is: recursive syntax and rules are the sole authority; for every one of the five rules, the forward executable-family union equals the rule and the backward union equals its converse; aggregate replay is sound by `Rule.Step.sound`; no graph representation/refinement layer exists.

- [ ] **Step 6: Validate the deletion boundary**

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Step.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
lake build VisualProof.Rule.Soundness
lake build
scripts/audit-lean-authority.sh rules
rg -n 'VisualProof\.(Concrete|Refinement)|namespace VisualProof\.(Concrete|Refinement)' VisualProof VisualProof.lean lakefile.toml
git diff --check
```

Expected: every build/audit passes; the final search returns no matches.

- [ ] **Step 7: Commit the deletion boundary**

```bash
git add -u -- VisualProof/Concrete.lean VisualProof/Concrete VisualProof/Refinement VisualProof/Proof VisualProof/ComputabilityAudit.lean
git add -- VisualProof.lean VisualProof/Audit.lean lakefile.toml scripts/audit-lean-authority.sh docs/goals/recursive-rewrite-authority/goal.md
git commit -m "remove graph execution authority"
```

**Architecture check:** The retained build must contain recursive syntax, rules, and semantics only. If any retained module still needs a graph type, move that consumer out of the retained build rather than restoring an adapter.

---

### Task 2: Define exact recursive rewrite inputs and the indexed-family contract

**Files:**
- Create: `VisualProof/Diagram/Rewrite.lean`
- Create: `VisualProof/Rule/Executable/Core.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `OpenDiagram`, `DiagramContext`, `ContextReplacement`, `NestedContextReplacement`, `Rule`, and `Rule.converse`.
- Produces: `ExactSite`, `ExactNestedSite`, `OpenDiagramClass`, `Rule.IsoInvariant`, `ExecutableDirection`, `ExecutableFamily`, `ExecutableFamily.At`, `ExecutableFamily.Member`, `At.functional`, and `member_eq_relation`.

- [ ] **Step 1: Add the exact source-side contextual input**

Implement this data owner in `VisualProof/Diagram/Rewrite.lean`:

```lean
structure ExactSite
    (source : OpenDiagram arity)
    (before : Region holeWires holeRels) where
  interface : OpenDiagram arity
  context : DiagramContext interface.externalClasses holeWires [] holeRels
  source_eq : source = interface.withBody (context.fill before)

def ExactSite.replace
    (site : ExactSite source before)
    (after : Region holeWires holeRels) : OpenDiagram arity :=
  site.interface.withBody (site.context.fill after)
```

Add proof-only `ExactSite.replacement`, constructing `ContextReplacement source (site.replace after)` from `source_eq` and reflexive endpoint isomorphisms. The `replace` definition must remain computable and must not mention isomorphisms.

- [ ] **Step 2: Add the exact source-side nested input**

Define `ExactNestedSite source selected before` with exactly the source half of `NestedContextReplacement`: `interface`, `outer`, `descendant`, `selected`, `before`, and one `source_eq`. Define `replace after` by filling the same `outer`/`descendant` decomposition with `after`, and a proof-only `replacement` theorem returning `NestedContextReplacement source (replace after)`.

- [ ] **Step 3: Add the recursive-diagram quotient and rule invariance contract**

Implement in `VisualProof/Rule/Executable/Core.lean`:

```lean
def OpenDiagram.isomorphicSetoid (arity : Nat) :
    Setoid (OpenDiagram arity) where
  r := OpenDiagram.Isomorphic
  iseqv := ⟨OpenDiagram.Isomorphic.refl,
    OpenDiagram.Isomorphic.symm,
    OpenDiagram.Isomorphic.trans⟩

abbrev OpenDiagramClass (arity : Nat) :=
  Quotient (OpenDiagram.isomorphicSetoid arity)

structure Rule.IsoInvariant (R : Rule) where
  transport : ∀ {arity}
    {source source' target target' : OpenDiagram arity},
    OpenDiagramIso source source' → R source target →
    OpenDiagramIso target target' → R source' target'

inductive ExecutableDirection
  | forward
  | backward

def ExecutableDirection.relation
    (direction : ExecutableDirection) (R : Rule) : Rule :=
  match direction with
  | .forward => R
  | .backward => converse R

structure ExecutableFamily (R : Rule) where
  invariant : Rule.IsoInvariant R
  Request : (direction : ExecutableDirection) →
    {arity : Nat} → OpenDiagram arity → Type
  apply : ∀ {direction arity source},
    Request direction source → OpenDiagram arity
  sound : ∀ {direction arity source}
    (request : Request direction source),
    direction.relation R source (apply request)
  complete : ∀ {direction arity source target},
    direction.relation R source target →
    ∃ (canonicalSource : OpenDiagram arity)
      (request : Request direction canonicalSource),
      OpenDiagram.Isomorphic source canonicalSource ∧
      OpenDiagram.Isomorphic target (apply request)
```

Derive `ExecutableDirection.invariant` for the selected relation and define `Rule.ClassRelation` by quotient lifting `direction.relation R` through that invariance proof.

Define `ExecutableFamily.Index direction arity` as a dependent pair of `canonicalSource` and `Request direction canonicalSource`. Define:

```lean
def ExecutableFamily.At
    (family : ExecutableFamily R)
    (index : family.Index direction arity)
    (source target : OpenDiagramClass arity) : Prop :=
  source = Quotient.mk _ index.canonicalSource ∧
  target = Quotient.mk _ (family.apply index.request)

def ExecutableFamily.Member
    (family : ExecutableFamily R)
    (direction : ExecutableDirection)
    (source target : OpenDiagramClass arity) : Prop :=
  ∃ index, family.At index source target
```

- [ ] **Step 4: Enter and prove exactness of the union RED/GREEN**

First enter and close `ExecutableFamily.At.functional`, proving literal target-class equality for one fixed index. Then enter the owning theorem:

```lean
theorem ExecutableFamily.member_eq_relation
    (family : ExecutableFamily R)
    (direction : ExecutableDirection) :
    family.Member direction =
      Rule.ClassRelation (direction.invariant family.invariant) := by
  sorry
```

Prove the forward inclusion from `family.sound` and quotient invariance. Prove the reverse inclusion by quotient induction on the source/target representatives, `family.complete`, and the two returned endpoint isomorphisms. Remove the sole owner `sorry` before continuing.

- [ ] **Step 5: Validate computability and dependency direction**

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Rewrite.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Core.lean
rg -n '\b(noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/Core.lean
rg -n '^import VisualProof.Rule.Executable' VisualProof/Rule --glob '!Executable/**'
git diff --check
```

Expected: strict checks pass; both searches return no matches.

- [ ] **Step 6: Commit the contract**

```bash
git add VisualProof/Diagram/Rewrite.lean VisualProof/Rule/Executable/Core.lean VisualProof.lean
git commit -m "define recursive executable families"
```

**Architecture check:** `ExecutableFamily` and the recursive isomorphism quotient are the only generic abstractions. The quotient exists because the mathematical rules already identify isomorphic presentations; it must not become a second recursive syntax or runtime normalization pass. If a rule needs another simulation, route, receipt, or transformation record, redesign its request around `ExactSite`/`ExactNestedSite` instead.

---

### Task 3: Implement the Erasure executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Erasure.lean`

**Interfaces:**
- Consumes: `ExecutableFamily`, `ExactSite`, `Rule.Erasure.Local.erase`, `ContextReplacement.lift`, and `DiagramContext.polarity`.
- Produces: `Erasure.Request`, `Erasure.apply`, `Erasure.apply_sound`, `Erasure.apply_complete`, and `Erasure.executable : ExecutableFamily Rule.Erasure` with exact forward/backward union theorems.

- [ ] **Step 1: Define direction-selected contextual polarities**

Define total functions:

```lean
def Erasure.erasePolarity : ExecutableDirection → Polarity
  | .forward => .positive
  | .backward => .negative

def Erasure.insertPolarity : ExecutableDirection → Polarity
  | .forward => .negative
  | .backward => .positive
```

- [ ] **Step 2: Define the two source-indexed request constructors**

Define `Erasure.Request direction source` with:

- `erase`: the local `hostLocal`, `hostItems`, `material`, `wireMap`, and `relationMap`; an `ExactSite source (Region.spliceAt hostLocal hostItems material wireMap relationMap)`; and proof that the site polarity is `erasePolarity direction`.
- `insert`: the same operands; an `ExactSite source (.mk hostLocal hostItems)`; and proof that the site polarity is `insertPolarity direction`.

Neither constructor may contain `Rule.Erasure` evidence or a target diagram.

- [ ] **Step 3: Implement the target function**

`Erasure.apply` replaces the erase site with `.mk hostLocal hostItems`, and replaces the insert site with `Region.spliceAt hostLocal hostItems material wireMap relationMap`.

- [ ] **Step 4: Enter the owning soundness theorem RED**

Declare:

```lean
theorem Erasure.apply_sound
    (request : Erasure.Request direction source) :
    direction.relation Rule.Erasure source (Erasure.apply request) := by
  sorry
```

This must be the only `sorry` in the task closure. Close it before entering completeness.

- [ ] **Step 5: Prove GREEN by local construction and contextual lift**

Case on `direction` and the request constructor. Construct `Rule.Erasure.Local.erase` from the stored operands, use the polarity equation to select the direct or converse local evidence, and apply `request.site.replacement` followed by `ContextReplacement.lift` and `Rule.Erasure.iso` only as proof steps.

- [ ] **Step 6: Prove every Erasure witness is executable RED/GREEN**

Enter `Erasure.apply_complete` with the exact `ExecutableFamily.complete` signature and one `sorry`. Case on `direction`; unfold `Rule.converse` in the backward case. Invert the `Rule.Erasure` contextual witness, its polarity, and `Rule.Erasure.Local.erase` evidence. Choose the canonical source `occurrence.interface.withBody (occurrence.context.fill before)`, construct the corresponding `erase` or `insert` request with `ExactSite.source_eq := rfl`, and return `occurrence.host_iso` plus the existing target isomorphism. This proof must not search either endpoint.

- [ ] **Step 7: Package and validate the exact family**

Define `Erasure.executable` using the existing `Rule.Erasure.iso` theorem as `invariant`, plus `Request`, `apply`, `apply_sound`, and `apply_complete`. Instantiate `ExecutableFamily.member_eq_relation` for both directions. Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Erasure.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/Erasure.lean
git diff --check
```

- [ ] **Step 8: Commit**

```bash
git add VisualProof/Rule/Executable/Erasure.lean
git commit -m "execute erasure on recursive diagrams"
```

**Architecture check:** The proof must case only on direction and the two request constructors. Any recursive traversal or target comparison indicates the request boundary is wrong.

---

### Task 4: Implement DoubleCut and Vacuity executable families

**Files:**
- Create: `VisualProof/Rule/Executable/DoubleCut.lean`
- Create: `VisualProof/Rule/Executable/Vacuity.lean`

**Interfaces:**
- Consumes: `ExactSite`, `Rule.DoubleCut.wrap`, `Rule.Vacuity.wrap`, their local `introduce` constructors, `atPolarity_symmetric_of`, and their existing `.symm` theorems.
- Produces: two request types with `introduce`/`eliminate`, two computable `apply` functions, soundness/completeness pairs, and exact `DoubleCut.executable`/`Vacuity.executable` families.

- [ ] **Step 1: Define DoubleCut requests and application**

`DoubleCut.Request direction source` has:

- `introduce`: operands `hostLocal`, `hostItems`, `body`, `wireMap`, `relationMap`, and an exact site at the unwrapped `Region.spliceAt` body.
- `eliminate`: the same operands and an exact site at `Region.spliceAt hostLocal hostItems (DoubleCut.wrap body) wireMap relationMap`.

`apply` replaces one form with the other. The request shape is independent of `direction` because `Rule.DoubleCut` is symmetric.

- [ ] **Step 2: Prove DoubleCut soundness and completeness RED/GREEN**

Enter and close `DoubleCut.apply_sound`. Then enter `DoubleCut.apply_complete` with one `sorry`. Invert the contextual witness and symmetric local evidence to select `introduce` or `eliminate`, choose the occurrence's canonical filled source, and return the source/target isomorphisms already present in the rule witness. Define `DoubleCut.executable` with both proofs and instantiate `member_eq_relation` in both directions.

- [ ] **Step 3: Define Vacuity requests and application**

Mirror the exact interface with the additional `arity` operand and `Vacuity.wrap arity body`. Do not factor the two rule request types through a configurable wrapper function; their rule constructors remain explicit.

- [ ] **Step 4: Prove Vacuity soundness and completeness RED/GREEN**

Enter and close `Vacuity.apply_sound`, then invert each `Rule.Vacuity` witness in `Vacuity.apply_complete` exactly as for DoubleCut, preserving the explicit binder arity. Define `Vacuity.executable` and instantiate exact union equality in both directions.

- [ ] **Step 5: Validate and commit each family**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/{DoubleCut,Vacuity}.lean
git diff --check
git add VisualProof/Rule/Executable/DoubleCut.lean VisualProof/Rule/Executable/Vacuity.lean
git commit -m "execute modal rules on recursive diagrams"
```

**Architecture check:** Each module has one nonrecursive `apply` and one short soundness case split. Shared higher-order wrapper machinery is a power leak and must not be introduced.

---

### Task 5: Implement the Iteration executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Iteration.lean`

**Interfaces:**
- Consumes: `ExactNestedSite`, `Iteration.WireFreshening`, `Iteration.Local.copy`, `NestedContextReplacement.lift`, and `Iteration.symm`.
- Produces: `Iteration.Request`, `Iteration.apply`, `Iteration.apply_sound`, `Iteration.apply_complete`, and exact `Iteration.executable` forward/backward unions.

- [ ] **Step 1: Define the copied descendant body once**

Add a private computable definition with the exact existing local law:

```lean
def Iteration.copied
    (descendant : DiagramContext (ancestorWires + anchorLocal)
      descendantWires ancestorRels descendantRels)
    (selected : Region (ancestorWires + anchorLocal) ancestorRels)
    (remainder : Region descendantWires descendantRels)
    (copyLocal : Nat)
    (copyWires : Iteration.WireFreshening
      (ancestorWires + anchorLocal) descendantWires copyLocal
      descendant.outerWire) : Region descendantWires descendantRels :=
  ((Region.adjoinAt copyLocal .nil
    ((selected.renameWires copyWires.wire).renameRelations
      descendant.outerRelation)).conjoin remainder)
```

- [ ] **Step 2: Define copy and uncopy requests**

`Iteration.Request direction source` has:

- `copy`: an `ExactNestedSite source selected remainder`, `copyLocal`, and `copyWires`.
- `uncopy`: the same selected/remainder/copy data and an `ExactNestedSite source selected (Iteration.copied ...)`.

The direction index is phantom because `Rule.Iteration` is symmetric; both constructors must be available in both directions.

- [ ] **Step 3: Implement `Iteration.apply`**

Copy replaces `remainder` by `copied`; uncopy replaces `copied` by `remainder`. Both use `ExactNestedSite.replace` and perform no search.

- [ ] **Step 4: Prove soundness RED/GREEN**

Enter `Iteration.apply_sound` with one `sorry`. For copy, construct `Iteration.Local.copy` with `after_eq := rfl`, then use `ExactNestedSite.replacement` and `NestedContextReplacement.lift`. For uncopy, reverse the same symmetric `Rule.Iteration` evidence. Case on direction only at the final rule/converse boundary.

- [ ] **Step 5: Prove completeness RED/GREEN**

Enter `Iteration.apply_complete` with one `sorry`. Invert `Rule.Iteration` into its direct or symmetric branch, then invert `NestedContextual` and `Iteration.Local`. Normalize `after_eq`, choose the nested replacement's exact canonical source, construct `copy` or `uncopy`, and return its source/target isomorphisms. Package `Iteration.executable` and prove both `member_eq_relation` instantiations.

- [ ] **Step 6: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Iteration.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/Iteration.lean
git diff --check
git add VisualProof/Rule/Executable/Iteration.lean
git commit -m "execute iteration on recursive diagrams"
```

**Architecture check:** The operation is one nested fill. Any selection partition, path alignment, compiler, or reconstruction theorem belongs to a displaced representation and must not reappear.

---

### Task 6: Implement the WireSever executable family

**Files:**
- Create: `VisualProof/Rule/Executable/WireSever.lean`

**Interfaces:**
- Consumes: `ExactSite`, `WireSever.collapseLocal`, `WireSever.Local.sever`, `WireSever.Open`, and `ContextReplacement.lift`.
- Produces: local sever/join requests, open sever/join requests, `WireSever.apply`, its soundness/completeness pair, and exact `WireSever.executable` forward/backward unions.

- [ ] **Step 1: Define local direction polarities**

Use the same two functions as the Erasure shape: local sever is positive in `.forward` and negative in `.backward`; local join is negative in `.forward` and positive in `.backward`.

- [ ] **Step 2: Define local sever and join request constructors**

For `joined : Fin (wires + localWires)` and `separate : ItemSeq (wires + (localWires + 1)) rels`:

- `localSever` stores an exact site at `.mk localWires (separate.renameWires (WireSever.collapseLocal wires localWires joined))` and the selected sever polarity.
- `localJoin` stores an exact site at `.mk (localWires + 1) separate` and the selected join polarity.

Their targets are the other body, computed directly.

- [ ] **Step 3: Define open sever input data**

Define `WireSever.OpenSeverRequest source` with:

```lean
separateBoundary : Fin arity → Fin (source.externalClasses + 1)
separateBoundary_surjective : Function.Surjective separateBoundary
collapse : Fin (source.externalClasses + 1) → Fin source.externalClasses
collapse_surjective : Function.Surjective collapse
boundary : ∀ position,
  collapse (separateBoundary position) = source.boundary position
separateBody : Region (source.externalClasses + 1) []
body_eq : separateBody.renameWires collapse = source.body
```

The target is the `OpenDiagram` with `separateBoundary` and `separateBody`. This constructor exists only for `.forward`.

- [ ] **Step 4: Define open join input data**

Define `WireSever.OpenJoinRequest source` with `targetClasses`, an equality `source.externalClasses = targetClasses + 1`, and a surjective `collapse : Fin source.externalClasses → Fin targetClasses`. Define the target boundary as `collapse ∘ source.boundary`, prove its surjectivity from the two supplied surjections, and define the target body as `source.body.renameWires collapse`. This constructor exists only for `.backward`.

- [ ] **Step 5: Implement all four `apply` branches**

The local branches call `ExactSite.replace`; the open branches construct the stated `OpenDiagram`. No branch returns `Option` or accepts a target.

- [ ] **Step 6: Prove `WireSever.apply_sound` RED/GREEN**

Enter one owner `sorry`. Local branches construct `WireSever.Local.sever`, select direct/converse contextual evidence from polarity, and lift. The open-sever branch constructs `Nonempty (WireSever.Open source target)` using `body_eq`; the open-join branch constructs `WireSever.Open target source` definitionally. Close soundness before entering completeness.

- [ ] **Step 7: Prove `WireSever.apply_complete` RED/GREEN**

Case on direction and invert the directed `Rule.WireSever` witness. For a contextual local witness, invert polarity and `WireSever.Local.sever` to construct `localSever` or `localJoin` at the occurrence's canonical source. For `WireSever.Open`, use its explicit `one_more`, `collapse`, boundary, and body isomorphism to construct the corresponding open request; when the rule witness supplies only an isomorphic body rather than equality, choose the witness's canonical renamed body as the computed representative and return the body isomorphism in the endpoint-class proof. Package `WireSever.executable` and prove forward/backward `member_eq_relation`.

- [ ] **Step 8: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/WireSever.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/WireSever.lean
git diff --check
git add VisualProof/Rule/Executable/WireSever.lean
git commit -m "execute wire severance on recursive diagrams"
```

**Architecture check:** Open boundary changes are the only special case. If local and open execution start sharing a general renaming/simulation framework, split them back into direct constructors.

---

### Task 7: Build the exhaustive rule-step executor

**Files:**
- Create: `VisualProof/Rule/Executable/Step.lean`
- Create: `VisualProof/Rule/Executable.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: the five `*.executable` families.
- Produces: `ExecutableStep`, `ExecutableStep.apply`, `ExecutableStep.sound`, `ExecutableStep.complete`, `ExecutableStep.member_eq_relation`, and the public executable umbrella.

- [ ] **Step 1: Define the five-family request sum**

```lean
inductive ExecutableStep
    (direction : ExecutableDirection)
    {arity : Nat} (source : OpenDiagram arity) : Type
  | erasure (request : Erasure.Request direction source)
  | wireSever (request : WireSever.Request direction source)
  | iteration (request : Iteration.Request direction source)
  | doubleCut (request : DoubleCut.Request direction source)
  | vacuity (request : Vacuity.Request direction source)
```

Do not add wildcard/default constructors or a registry.

- [ ] **Step 2: Define exhaustive application**

`ExecutableStep.apply` case-splits on all five constructors and invokes exactly the corresponding family `apply`.

- [ ] **Step 3: Prove aggregate soundness RED/GREEN**

Enter `ExecutableStep.sound` with one `sorry` and conclusion `direction.relation Rule.Step source (ExecutableStep.apply request)`. Close it by five cases, applying the corresponding family soundness and the matching `Rule.Step` constructor; for `.backward`, unfold `Rule.converse` before applying the constructor.

- [ ] **Step 4: Prove aggregate completeness RED/GREEN**

Enter `ExecutableStep.complete` with one `sorry`. Case on direction, unfold `Rule.converse` for backward execution, invert the five constructors of `Rule.Step`, invoke the corresponding family's `complete`, and wrap the returned request with the matching `ExecutableStep` constructor. No aggregate branch may inspect rule-specific evidence beyond selecting its family.

- [ ] **Step 5: Expose the exact aggregate member relation**

Define the request-indexed graph and union exactly as in `ExecutableFamily`, prove per-request functionality, and prove the union equals the quotient-lifted `direction.relation Rule.Step` by the aggregate soundness/completeness pair.

- [ ] **Step 6: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Step.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable.lean
rg -n '\| _ =>' VisualProof/Rule/Executable/Step.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable
git diff --check
git add VisualProof/Rule/Executable VisualProof/Rule/Executable.lean VisualProof.lean
git commit -m "aggregate recursive rule executables"
```

**Architecture check:** The aggregate owns dispatch only. Any rule-specific condition or target construction in `Step.lean` must move back to its family module.

---

### Task 8: Rebuild replay and checked theorems on recursive execution

**Files:**
- Create: `VisualProof/Proof/Schema.lean`
- Create: `VisualProof/Proof/Replay.lean`
- Create: `VisualProof/Proof/Theorem.lean`
- Create: `VisualProof/Proof/Theory.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: recursive `OpenDiagram`, `ExecutableStep`, `ExecutableStep.sound`, `Rule.Step.sound`, and `OpenDiagramIso`.
- Produces: recursive `TheoremSchema`, `Program`, `replay`, `Program.sound`, `CheckedTheorem`, `CheckedTheorem.valid`, and `VerifiedTheory`.

- [ ] **Step 1: Define recursive theorem schemas**

Replace boundary-equality transport with the intrinsic arity index:

```lean
structure TheoremSchema (arity : Nat) where
  left : OpenDiagram arity
  right : OpenDiagram arity

def TheoremSchema.Valid (schema : TheoremSchema arity)
    (model : Model) : Prop :=
  ∀ args, denoteOpen model schema.left args →
    denoteOpen model schema.right args
```

- [ ] **Step 2: Define total typed programs and replay**

```lean
inductive Program (direction : ExecutableDirection) :
    OpenDiagram arity → Type
  | done (source) : Program direction source
  | step {source}
      (request : ExecutableStep direction source)
      (next : Program direction (ExecutableStep.apply request)) :
      Program direction source

def replay : Program direction source → OpenDiagram arity
  | .done source => source
  | .step _ next => replay next
```

There is no receipt, error channel, or success equality because applicability is already indexed by `request`.

- [ ] **Step 3: Prove replay rule closure RED/GREEN**

Define a small inductive `DirectedDerivation direction source target` with `.refl` and `.step` constructors over `direction.relation Rule.Step`. Enter `Program.sound : DirectedDerivation direction source (replay program)` with one `sorry`; prove by structural induction using `ExecutableStep.sound`.

- [ ] **Step 4: Prove semantic replay soundness**

Prove forward derivations preserve `denoteOpen` using `Rule.Step.sound`; prove backward derivations reflect it by applying `Rule.Step.sound` to the reversed endpoint order. Package this as `Program.denote`.

- [ ] **Step 5: Define checked theorems directly**

`CheckedTheorem` contains one `schema`, a forward program from `schema.left`, a backward program from `schema.right`, and an `OpenDiagramIso` between their replay results. It stores no separate finish values or replay equations.

- [ ] **Step 6: Prove theorem validity RED/GREEN**

Enter `CheckedTheorem.valid` with conclusion `schema.Valid model`. Compose forward replay soundness, the endpoint isomorphism’s denotation equivalence, and backward replay soundness in reverse. Remove the sole `sorry`.

- [ ] **Step 7: Restore verified-theory aggregation**

Define `VerifiedTheorems` and `VerifiedTheory` over the new arity-indexed schemas; each appended theorem packages its own arity existentially:

```lean
structure SomeCheckedTheorem where
  arity : Nat
  checked : CheckedTheorem arity
```

Use `List SomeCheckedTheorem` as the collection; do not erase arities with casts.

- [ ] **Step 8: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Proof/Schema.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Replay.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theory.lean
rg -n '\b(sorry|admit|Concrete|Refinement|Receipt|Except|Error)\b' VisualProof/Proof
git diff --check
git add VisualProof/Proof VisualProof.lean
git commit -m "replay proofs on recursive executables"
```

**Architecture check:** `Program` stores only requests and continuation structure. If it stores targets, equalities, receipts, or rule proofs, remove that duplicated state and derive it from `ExecutableStep.apply`/`sound`.

---

### Task 9: Install computability, authority, and semantic validation

**Files:**
- Create: `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: all five rule `apply` functions, aggregate `ExecutableStep.apply`, `replay`, every family soundness/completeness/equality theorem, `Rule.Step.sound`, and `CheckedTheorem.valid`.
- Produces: compiler-backed computability evidence, dependency/roster audit, axiom audit, and the final public build.

- [ ] **Step 1: Add compiler-backed computability evidence**

Create `VisualProof/ComputabilityAudit.lean`:

```lean
import Lean.Compiler
import VisualProof.Rule.Executable
import VisualProof.Proof.Replay

open Lean

run_meta Lean.compileDecls #[
  ``VisualProof.Rule.Erasure.apply,
  ``VisualProof.Rule.WireSever.apply,
  ``VisualProof.Rule.Iteration.apply,
  ``VisualProof.Rule.DoubleCut.apply,
  ``VisualProof.Rule.Vacuity.apply,
  ``VisualProof.Rule.ExecutableStep.apply,
  ``VisualProof.Proof.replay
]
```

Use the final namespaces exactly as implemented; compilation failure is a task failure, not grounds for `unsafe` or `noncomputable`.

- [ ] **Step 2: Extend the source authority audit**

Require exactly five mathematical `Rule.Step` constructors and exactly five aggregate `ExecutableStep` constructors. Require one exported `executable : ExecutableFamily` for each rule. Reject imports from executable/proof modules into mathematical rule or soundness modules. Reject any remaining `Concrete`, `Refinement`, receipt, representation, compiler, or graph-operation module under `VisualProof`.

- [ ] **Step 3: Extend the axiom audit**

Add `#print axioms` for each `*.apply_sound`, each `*.apply_complete`, each rule's `member_eq_relation`, `ExecutableStep.sound`, `ExecutableStep.complete`, aggregate `ExecutableStep.member_eq_relation`, `Program.sound`, and `CheckedTheorem.valid`. The output may contain Lean’s accepted classical/propext axioms from existing isomorphism semantics, but must not contain project placeholder axioms.

- [ ] **Step 4: Run strict module validation**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Core.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Erasure.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/WireSever.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Iteration.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Step.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
```

- [ ] **Step 5: Run final architecture and family-coverage validation**

```bash
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh proof
rg -n '\b(sorry|admit|decreasing_by sorry|^axiom |set_option (maxHeartbeats|maxRecDepth))\b' VisualProof
rg -n 'VisualProof\.(Concrete|Refinement)|namespace VisualProof\.(Concrete|Refinement)' VisualProof VisualProof.lean lakefile.toml
lake build
git diff --check
git status --short
```

Expected: strict checks and full build pass; both forbidden searches return no matches; status lists only unrelated user changes before staging.

- [ ] **Step 6: Perform the final architecture-compensation review**

Inspect each family and confirm:

- `apply` is a direct constructor/fill function with no recursion other than structural recursive syntax helpers.
- each request contains no target, relation evidence, isomorphism, or semantic proof;
- each family has one soundness owner, one completeness owner, one exact union theorem, and no alternative executor;
- aggregate execution contains dispatch only;
- replay contains no execution state beyond requests;
- no file raises elaboration limits.

If any item fails, return to the owning task and redesign before committing.

- [ ] **Step 7: Commit final audits**

```bash
git add VisualProof/ComputabilityAudit.lean VisualProof/Audit.lean scripts/audit-lean-authority.sh VisualProof.lean
git commit -m "audit recursive rule execution"
```

## Self-Review

- **Spec coverage:** Task 1 removes the representation split. Tasks 2–6 define a computable indexed functional family for every mathematical rule and its relational converse, and prove both inclusions. Task 7 proves exact equality for aggregate directed `Rule.Step`. Task 8 rebuilds the proof consumer directly on recursive execution. Task 9 proves computability, equality, semantic soundness, dependency direction, and absence of the displaced authority.
- **Anti-vacuity:** Requests cannot contain `R` evidence or a target, every rule exports concrete constructors in both directions, completeness extracts those constructors from every rule witness, and the compiler audit checks the actual target functions.
- **Exact adequacy:** Each family proves per-index functionality and equality of its union with the corresponding quotient-lifted rule relation. Neither missing valid rule instances nor extra executable transitions can pass.
- **Type consistency:** Every `apply` returns an `OpenDiagram arity` representative; every soundness theorem concludes `ExecutableDirection.relation R source target`; every completeness theorem returns isomorphic canonical endpoints; every exported equality is between relations on `OpenDiagramClass arity`; aggregate requests preserve source/arity indices; replay endpoints are definitionally produced by aggregate application.
- **Architecture discipline:** Deletion occurs before replacement. There is one generic family contract, one recursive isomorphism quotient matching the rules' existing invariance, one direct exact-site boundary, no representation/refinement bridge, no target search, no second recursive syntax, and explicit stop/rethink gates after every implementation task.
