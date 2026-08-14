# Recursive Rule Execution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace graph-based execution with computable indexed functional relations defined directly on recursive `OpenDiagram` syntax, proving that the union of each rule's forward family equals that rule and the union of its backward family equals the rule's converse.

**Architecture:** An `ExecutableFamily` contains only an index family and an ordinary computable `run` function. Its union relation is defined by existentially quantifying an index whose function result is the target; each rule exports one theorem equating that union with the rule (or its converse). Indices contain only recursive source decompositions and operation operands, while the existing `OpenDiagram.Isomorphic` quotient accounts for the rules' presentation invariance without adding a runtime normalization pass.

**Tech Stack:** Lean 4.30.0, Lake, the existing intrinsic `Region`/`Item`/`ItemSeq`/`OpenDiagram` syntax, `DiagramContext`, the five existing `Rule` relations, and their existing semantic soundness theorems.

## Global Constraints

- Interpret the requested reverse/“contrapositive” executable as the existing relational `Rule.converse R`; do not introduce a second notion of reverse execution.
- Remove the graph representation and its execution/refinement dependents before adding recursive executables. Do not retain aliases, adapters, re-exports, compatibility modules, or dual authorities.
- An executable index may contain source decomposition evidence, finite maps, and rule operands. It must not contain a target `OpenDiagram`, `Rule`/`Rule.Step` evidence, a `ContextReplacement`, or an `OpenDiagramIso`.
- The executable authority is the function itself: `run` is a total function from a source-indexed operation index to a recursive target representative. Do not define or prove a separate `Functional` predicate.
- `run` definitions must be ordinary computable `def`s. `noncomputable`, `Classical.choice`, target search, target occurrence discovery, and semantic denotation are forbidden in executable modules.
- Soundness may construct proof-only `ContextReplacement`, `NestedContextReplacement`, and isomorphism witnesses after the target has been computed.
- Prove one owning equality theorem for every direction. Its forward implication excludes extra function results; its reverse implication proves every rule witness is the result of some indexed function.
- Reject the vacuous empty-family solution structurally: each rule has concrete index constructors, and the reverse direction of the equality theorem must extract one from every corresponding rule witness.
- Follow theorem-driven RED/GREEN. Supporting definitions compile before the owning union-equality theorem is entered with `sorry`; GREEN removes that sole `sorry` before the task is committed.
- Do not add heartbeat or recursion-depth overrides. If a proof needs duplicated traversal, dependent target reconciliation, or growing cast/HEq infrastructure, stop that task, restore its last GREEN boundary, and redesign the index or theorem boundary.
- Preserve all unrelated TypeScript and test changes in the shared worktree. Stage and commit only the task-owned Lean, audit, and plan files.

## Complexity Ledger

- **Essential behavior:** five recursive rule relations; a computable forward family whose union equals each relation; a computable backward family whose union equals its converse; aggregate one-step execution; proof replay; semantic soundness through the existing `Rule.Step.sound`.
- **Essential state:** the recursive source diagram, execution direction, an exact recursive site/nested-site decomposition, and the operands that select one member of a nondeterministic rule family.
- **Integrity constraints:** Lean's function type makes one index determine one target; the union contains exactly the selected directed rule; boundaries remain ordered; wire/relation renamings remain well typed; contextual polarity is derived from the supplied recursive context.
- **Derived data:** target diagrams, filled contexts, local before/after regions, `ContextReplacement` witnesses, aggregate `Rule.Step` evidence, replay endpoints, and theorem validity.
- **Accidental state to remove:** graph identifiers, checked graph wrappers, receipts, survivor domains, allocation layouts, compiler results, encoded/elaborated mirrors, and representation witnesses.
- **Accidental control to remove:** graph selection/removal/splice pipelines, compilation replay, target reconstruction, refinement dispatch, operation error plumbing, and generated step-tag execution.
- **Code volume:** the current graph/execution/proof bridge is 66 Lean files and about 42,000 lines. The replacement is bounded to one generic contract, two exact recursive decomposition types, five rule modules, one aggregate, and the recursive proof layer.
- **Power leaks prohibited:** generic transformation/simulation records, matchers hidden inside adequacy proofs, arbitrary relation evidence as an index, caller-supplied targets, and a second syntax or navigation authority.

## Target File Structure

### Retained authorities

- `VisualProof/Diagram/**`: intrinsic recursive syntax, contexts, paths, isomorphisms, replacements, and semantics.
- `VisualProof/Rule/{Relation,Erasure,WireSever,Iteration,DoubleCut,Vacuity,Step}.lean`: mathematical rule relations.
- `VisualProof/Rule/Soundness.lean` and `VisualProof/Rule/Soundness/**`: semantic soundness.

### New executable authority

- `VisualProof/Diagram/Rewrite.lean`: exact source-side contextual and nested contextual decompositions plus deterministic fill operations.
- `VisualProof/Rule/Executable/Core.lean`: recursive-diagram isomorphism quotient, invariant-rule lifting, direction, the index/`run` family, and its derived union relation.
- `VisualProof/Rule/Executable/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`: rule-specific index types, computable `run` functions, and exact union-equality theorems.
- `VisualProof/Rule/Executable/Step.lean`: exhaustive five-family index sum and aggregate executor.
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
- Produces: `ExactSite`, `ExactNestedSite`, `OpenDiagramClass`, `Rule.IsoInvariant`, `ExecutableDirection`, `ExecutableFamily`, and `ExecutableFamily.Member`.

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

structure ExecutableFamily where
  Index : (direction : ExecutableDirection) →
    {arity : Nat} → OpenDiagram arity → Type
  run : ∀ {direction arity source},
    Index direction source → OpenDiagram arity
```

Derive `ExecutableDirection.invariant` for the selected relation and define `Rule.ClassRelation` by quotient lifting `direction.relation R` through that invariance proof.

Define the union of the actual indexed functions directly:

```lean
def ExecutableFamily.Member
    (family : ExecutableFamily)
    (direction : ExecutableDirection)
    (source target : OpenDiagramClass arity) : Prop :=
  ∃ (canonicalSource : OpenDiagram arity)
    (index : family.Index direction canonicalSource),
    source = Quotient.mk _ canonicalSource ∧
    target = Quotient.mk _ (family.run index)
```

- [ ] **Step 4: Compile the function family and quotient relation**

This task is structural setup and has no owning rule theorem. Kernel-check the quotient lift, `ExecutableFamily`, and `Member` definitions directly. Do not add `At`, `Functional`, `sound`, `complete`, or generic equality fields; each rule module owns its single concrete equality theorem.

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

**Architecture check:** `ExecutableFamily` is only data (`Index` and `run`), and the recursive isomorphism quotient is only the extensional theorem carrier. If the core grows a functionality predicate, proof fields, simulation, route, receipt, or runtime normalization, remove it and redesign the rule-specific index around `ExactSite`/`ExactNestedSite`.

---

### Task 3: Implement the Erasure executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Erasure.lean`

**Interfaces:**
- Consumes: `ExecutableFamily`, `ExactSite`, `Rule.Erasure.Local.erase`, `ContextReplacement.lift`, and `DiagramContext.polarity`.
- Produces: `Erasure.Index`, computable `Erasure.run`, `Erasure.executable : ExecutableFamily`, and `Erasure.executable_eq_rule` for both directions.

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

- [ ] **Step 2: Define the two source-indexed operation constructors**

Define `Erasure.Index direction source` with:

- `erase`: the local `hostLocal`, `hostItems`, `material`, `wireMap`, and `relationMap`; an `ExactSite source (Region.spliceAt hostLocal hostItems material wireMap relationMap)`; and proof that the site polarity is `erasePolarity direction`.
- `insert`: the same operands; an `ExactSite source (.mk hostLocal hostItems)`; and proof that the site polarity is `insertPolarity direction`.

Neither constructor may contain `Rule.Erasure` evidence or a target diagram.

- [ ] **Step 3: Implement the target function**

`Erasure.run` replaces the erase site with `.mk hostLocal hostItems`, and replaces the insert site with `Region.spliceAt hostLocal hostItems material wireMap relationMap`.

- [ ] **Step 4: Package the function family**

Define:

```lean
def Erasure.executable : ExecutableFamily where
  Index := Erasure.Index
  run := Erasure.run
```

- [ ] **Step 5: Enter the one exact adequacy theorem RED**

Declare:

```lean
theorem Erasure.executable_eq_rule
    (direction : ExecutableDirection) :
    Erasure.executable.Member direction =
      Rule.ClassRelation
        (direction.invariant ⟨Rule.Erasure.iso⟩) := by
  sorry
```

- [ ] **Step 6: Prove both directions GREEN inside the equality theorem**

For left-to-right, unpack the function index, construct `Rule.Erasure.Local.erase`, select direct/converse local evidence from polarity, and lift the exact site replacement. For right-to-left, quotient-induct to representatives, invert the contextual rule witness and local evidence, choose `occurrence.interface.withBody (occurrence.context.fill before)`, construct the corresponding `erase` or `insert` index with `ExactSite.source_eq := rfl`, and close the endpoint classes with the witness's source/target isomorphisms. This proof must not search either endpoint.

- [ ] **Step 7: Package and validate the exact family**

Run:

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

**Architecture check:** The proof must case only on direction and the two index constructors. Any recursive traversal or target comparison indicates the index boundary is wrong.

---

### Task 4: Implement DoubleCut and Vacuity executable families

**Files:**
- Create: `VisualProof/Rule/Executable/DoubleCut.lean`
- Create: `VisualProof/Rule/Executable/Vacuity.lean`

**Interfaces:**
- Consumes: `ExactSite`, `Rule.DoubleCut.wrap`, `Rule.Vacuity.wrap`, their local `introduce` constructors, `atPolarity_symmetric_of`, and their existing `.symm` theorems.
- Produces: two index types with `introduce`/`eliminate`, two computable `run` functions, and one exact union theorem for each family and direction.

- [ ] **Step 1: Define DoubleCut indices and execution**

`DoubleCut.Index direction source` has:

- `introduce`: operands `hostLocal`, `hostItems`, `body`, `wireMap`, `relationMap`, and an exact site at the unwrapped `Region.spliceAt` body.
- `eliminate`: the same operands and an exact site at `Region.spliceAt hostLocal hostItems (DoubleCut.wrap body) wireMap relationMap`.

`run` replaces one form with the other. The index shape is independent of `direction` because `Rule.DoubleCut` is symmetric.

- [ ] **Step 2: Prove DoubleCut exactness RED/GREEN**

Define `DoubleCut.executable := ⟨DoubleCut.Index, DoubleCut.run⟩`. Enter one `DoubleCut.executable_eq_rule` theorem with `sorry`; prove its forward implication by constructing `Rule.DoubleCut.Local.introduce` and its reverse implication by inverting the contextual witness and symmetric local evidence to select `introduce` or `eliminate`. Choose the occurrence's canonical filled source and close endpoint classes with the rule witness's isomorphisms.

- [ ] **Step 3: Define Vacuity indices and execution**

Mirror the exact interface with the additional `arity` operand and `Vacuity.wrap arity body`. Do not factor the two rule index types through a configurable wrapper function; their rule constructors remain explicit.

- [ ] **Step 4: Prove Vacuity exactness RED/GREEN**

Define `Vacuity.executable := ⟨Vacuity.Index, Vacuity.run⟩`. Enter one `Vacuity.executable_eq_rule` theorem and prove both implications exactly as for DoubleCut while preserving the explicit binder arity.

- [ ] **Step 5: Validate and commit each family**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
rg -n '\b(sorry|admit|noncomputable|Classical\.choice|HEq)\b' VisualProof/Rule/Executable/{DoubleCut,Vacuity}.lean
git diff --check
git add VisualProof/Rule/Executable/DoubleCut.lean VisualProof/Rule/Executable/Vacuity.lean
git commit -m "execute modal rules on recursive diagrams"
```

**Architecture check:** Each module has one nonrecursive `run` and one exact equality proof. Shared higher-order wrapper machinery is a power leak and must not be introduced.

---

### Task 5: Implement the Iteration executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Iteration.lean`

**Interfaces:**
- Consumes: `ExactNestedSite`, `Iteration.WireFreshening`, `Iteration.Local.copy`, `NestedContextReplacement.lift`, and `Iteration.symm`.
- Produces: `Iteration.Index`, computable `Iteration.run`, `Iteration.executable`, and `Iteration.executable_eq_rule`.

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

- [ ] **Step 2: Define copy and uncopy indices**

`Iteration.Index direction source` has:

- `copy`: an `ExactNestedSite source selected remainder`, `copyLocal`, and `copyWires`.
- `uncopy`: the same selected/remainder/copy data and an `ExactNestedSite source selected (Iteration.copied ...)`.

The direction index is phantom because `Rule.Iteration` is symmetric; both constructors must be available in both directions.

- [ ] **Step 3: Implement `Iteration.run`**

Copy replaces `remainder` by `copied`; uncopy replaces `copied` by `remainder`. Both use `ExactNestedSite.replace` and perform no search.

- [ ] **Step 4: Package the function and prove exact adequacy RED/GREEN**

Define `Iteration.executable := ⟨Iteration.Index, Iteration.run⟩`. Enter one `Iteration.executable_eq_rule` theorem with `sorry`. For the function-to-rule implication, construct `Iteration.Local.copy`, lift through `ExactNestedSite.replacement`, and use symmetry for `uncopy`. For rule-to-function, invert the symmetric `Rule.Iteration`, `NestedContextual`, and `Iteration.Local` witnesses; normalize `after_eq`, choose the exact canonical source, and construct `copy` or `uncopy` with matching endpoint classes.

- [ ] **Step 5: Validate and commit**

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
- Produces: local sever/join indices, open sever/join indices, computable `WireSever.run`, `WireSever.executable`, and `WireSever.executable_eq_rule`.

- [ ] **Step 1: Define local direction polarities**

Use the same two functions as the Erasure shape: local sever is positive in `.forward` and negative in `.backward`; local join is negative in `.forward` and positive in `.backward`.

- [ ] **Step 2: Define local sever and join index constructors**

For `joined : Fin (wires + localWires)` and `separate : ItemSeq (wires + (localWires + 1)) rels`:

- `localSever` stores an exact site at `.mk localWires (separate.renameWires (WireSever.collapseLocal wires localWires joined))` and the selected sever polarity.
- `localJoin` stores an exact site at `.mk (localWires + 1) separate` and the selected join polarity.

Their targets are the other body, computed directly.

- [ ] **Step 3: Define open sever input data**

Define `WireSever.OpenSeverData source` with:

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

Define `WireSever.OpenJoinData source` with `targetClasses`, an equality `source.externalClasses = targetClasses + 1`, and a surjective `collapse : Fin source.externalClasses → Fin targetClasses`. Define the target boundary as `collapse ∘ source.boundary`, prove its surjectivity from the two supplied surjections, and define the target body as `source.body.renameWires collapse`. This constructor exists only for `.backward`.

- [ ] **Step 5: Implement all four `run` branches**

The local branches call `ExactSite.replace`; the open branches construct the stated `OpenDiagram`. No branch returns `Option` or accepts a target.

- [ ] **Step 6: Package the function family**

Define `WireSever.executable := ⟨WireSever.Index, WireSever.run⟩` with no proof fields.

- [ ] **Step 7: Prove `WireSever.executable_eq_rule` RED/GREEN**

Enter one equality theorem with `sorry`. For function-to-rule, local branches construct `WireSever.Local.sever` and lift with polarity; open branches construct `WireSever.Open`. For rule-to-function, case on direction and invert the directed `Rule.WireSever` witness. A contextual witness yields `localSever` or `localJoin` at the canonical source. An open witness yields the corresponding open index; when it supplies only an isomorphic body, choose the canonical renamed body as the function input representative and use the body isomorphism only to close equality of endpoint classes.

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
- Produces: `ExecutableStep.Index`, computable `ExecutableStep.run`, `ExecutableStep.executable`, `ExecutableStep.executable_eq_rule`, and the public executable umbrella.

- [ ] **Step 1: Define the five-family index sum**

```lean
inductive ExecutableStep.Index
    (direction : ExecutableDirection)
    {arity : Nat} (source : OpenDiagram arity) : Type
  | erasure (index : Erasure.Index direction source)
  | wireSever (index : WireSever.Index direction source)
  | iteration (index : Iteration.Index direction source)
  | doubleCut (index : DoubleCut.Index direction source)
  | vacuity (index : Vacuity.Index direction source)
```

Do not add wildcard/default constructors or a registry.

- [ ] **Step 2: Define exhaustive execution**

`ExecutableStep.run` case-splits on all five constructors and invokes exactly the corresponding family `run`. Package `ExecutableStep.executable := ⟨ExecutableStep.Index, ExecutableStep.run⟩`.

- [ ] **Step 3: Prove aggregate exactness RED/GREEN**

Enter `ExecutableStep.executable_eq_rule` with one `sorry`. For function-to-rule, case on the five indices, use the corresponding family's equality theorem in the forward direction, and wrap with the matching `Rule.Step` constructor. For rule-to-function, quotient-induct to representatives, invert the five constructors of `Rule.Step`, use the corresponding equality theorem in reverse, and wrap the resulting family index. No aggregate branch may inspect rule-specific evidence beyond selecting its family.

- [ ] **Step 4: Validate and commit**

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
- Consumes: recursive `OpenDiagram`, `ExecutableStep.executable`, `ExecutableStep.executable_eq_rule`, `Rule.Step.sound`, and `OpenDiagramIso`.
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
      (index : ExecutableStep.Index direction source)
      (next : Program direction (ExecutableStep.run index)) :
      Program direction source

def replay : Program direction source → OpenDiagram arity
  | .done source => source
  | .step _ next => replay next
```

There is no receipt, error channel, or success equality because applicability is already carried by the operation index.

- [ ] **Step 3: Prove replay rule closure RED/GREEN**

Define a small inductive `DirectedDerivation direction source target` with `.refl` and `.step` constructors over `direction.relation Rule.Step`. Enter `Program.sound : DirectedDerivation direction source (replay program)` with one `sorry`; prove by structural induction, obtaining each one-step rule fact from the forward implication of `ExecutableStep.executable_eq_rule` applied to the current index's function equation.

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

**Architecture check:** `Program` stores only operation indices and continuation structure. If it stores targets, equalities, receipts, or rule proofs, remove that duplicated state and derive it from `ExecutableStep.run`/`executable_eq_rule`.

---

### Task 9: Install computability, authority, and semantic validation

**Files:**
- Create: `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: all five rule `run` functions, aggregate `ExecutableStep.run`, `replay`, every family equality theorem, `Rule.Step.sound`, and `CheckedTheorem.valid`.
- Produces: compiler-backed computability evidence, dependency/roster audit, axiom audit, and the final public build.

- [ ] **Step 1: Add compiler-backed computability evidence**

Create `VisualProof/ComputabilityAudit.lean`:

```lean
import Lean.Compiler
import VisualProof.Rule.Executable
import VisualProof.Proof.Replay

open Lean

run_meta Lean.compileDecls #[
  ``VisualProof.Rule.Erasure.run,
  ``VisualProof.Rule.WireSever.run,
  ``VisualProof.Rule.Iteration.run,
  ``VisualProof.Rule.DoubleCut.run,
  ``VisualProof.Rule.Vacuity.run,
  ``VisualProof.Rule.ExecutableStep.run,
  ``VisualProof.Proof.replay
]
```

Use the final namespaces exactly as implemented; compilation failure is a task failure, not grounds for `unsafe` or `noncomputable`.

- [ ] **Step 2: Extend the source authority audit**

Require exactly five mathematical `Rule.Step` constructors and exactly five aggregate `ExecutableStep.Index` constructors. Require one exported `executable : ExecutableFamily` and one exact `executable_eq_rule` theorem for each rule. Reject any `Functional` predicate/theorem in executable modules. Reject imports from executable/proof modules into mathematical rule or soundness modules and reject any remaining `Concrete`, `Refinement`, receipt, representation, compiler, or graph-operation module under `VisualProof`.

- [ ] **Step 3: Extend the axiom audit**

Add `#print axioms` for each rule's `executable_eq_rule`, aggregate `ExecutableStep.executable_eq_rule`, `Program.sound`, and `CheckedTheorem.valid`. The output may contain Lean’s accepted classical/propext axioms from existing isomorphism semantics, but must not contain project placeholder axioms.

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

- `run` is an ordinary computable function and a direct constructor/fill operation with no recursion other than structural recursive syntax helpers;
- each index contains no target, relation evidence, isomorphism, or semantic proof;
- each family has one exact union theorem and no functionality wrapper, soundness/completeness record fields, or alternative executor;
- aggregate execution contains dispatch only;
- replay contains no execution state beyond operation indices;
- no file raises elaboration limits.

If any item fails, return to the owning task and redesign before committing.

- [ ] **Step 7: Commit final audits**

```bash
git add VisualProof/ComputabilityAudit.lean VisualProof/Audit.lean scripts/audit-lean-authority.sh VisualProof.lean
git commit -m "audit recursive rule execution"
```

## Self-Review

- **Spec coverage:** Task 1 removes the representation split. Tasks 2–6 define a computable indexed function family for every mathematical rule and its relational converse, with one exact equality theorem per family. Task 7 proves exact equality for aggregate directed `Rule.Step`. Task 8 rebuilds the proof consumer directly on recursive execution. Task 9 proves computability, equality, semantic soundness, dependency direction, and absence of the displaced authority.
- **Anti-vacuity:** Indices cannot contain `R` evidence or a target, every rule exports concrete indices in both directions, the reverse implication extracts those indices from every rule witness, and the compiler audit checks the actual functions.
- **Exact adequacy:** Each family union is defined directly from successful `run` equations and equals the corresponding quotient-lifted rule relation. Neither missing valid rule instances nor extra executable transitions can pass.
- **Type consistency:** Every `run` returns an `OpenDiagram arity` representative; every exported equality is between the function-family union and the rule relation on `OpenDiagramClass arity`; aggregate indices preserve source/arity indices; replay endpoints are definitionally produced by aggregate `run`.
- **Architecture discipline:** Deletion occurs before replacement. There is one generic family contract, one recursive isomorphism quotient matching the rules' existing invariance, one direct exact-site boundary, no representation/refinement bridge, no target search, no second recursive syntax, and explicit stop/rethink gates after every implementation task.
