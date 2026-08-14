# Recursive Rule Execution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace graph-based execution with computable indexed functional relations defined directly on recursive `OpenDiagram` syntax, proving that the union of each rule's forward family equals that rule and the union of its backward family equals the rule's converse.

**Architecture:** Every rule directly owns a source-dependent `ForwardIndex`/`BackwardIndex` and computable `runForward`/`runBackward`. The forward theorem says the isomorphism-closed outputs of `runForward` are exactly `R source target`; the backward theorem says the outputs of `runBackward` are exactly `R target source`. There is no generic relation wrapper or direction switch.

**Tech Stack:** Lean 4.30.0, Lake, the existing intrinsic `Region`/`Item`/`ItemSeq`/`OpenDiagram` syntax, `DiagramContext`, the five existing `Rule` relations, and their existing semantic soundness theorems.

## Global Constraints

- State reverse execution by swapping endpoints: the backward theorem characterizes `R target source`. No named direction or converse wrapper belongs in the executable interface.
- Remove the graph representation and its execution/refinement dependents before adding recursive executables. Do not retain aliases, adapters, re-exports, compatibility modules, or dual authorities.
- `Index source` is the computable type of valid choices available at that particular source. Applicability belongs in this dependent domain, so `run` does not return `Option`.
- An executable index may contain source decomposition evidence, finite maps, and rule operands. It must not contain a target `OpenDiagram`, `Rule`/`Rule.Step` evidence, a `ContextReplacement`, or an `OpenDiagramIso`.
- The executable authority is the dependent function itself: `run source : Index source → OpenDiagram arity`. Lean's function type supplies functionality; do not define or prove a separate `Functional` predicate.
- Coverage is presentation-invariant: each exact theorem quantifies an index and requires `OpenDiagram.Isomorphic (run source index) target`. Do not require raw syntactic equality between the computed representative and the rule endpoint.
- Every mathematical rule module must export `respectsTargetIso`, proving `R source target → target ≅ target' → R source target'`, and `backward_respectsTargetIso`, proving `R target source → target ≅ target' → R target' source`. These are proof obligations, not inputs to `run`.
- Each rule must expose distinct `runForward` and `runBackward` definitions and distinct `forward_exact` and `backward_exact` theorems. Do not hide the two functions behind a direction argument.
- `runForward`, `runBackward`, and every definition in their computational dependency closures must be ordinary computable `def`s accepted by `Lean.compileDecls`. Correctness theorems and proof-only helpers may use classical reasoning, `Classical.choice`, or `noncomputable` definitions.
- Target search, target occurrence discovery, and semantic denotation are forbidden in the computational dependency closures of the two `run` functions.
- Soundness may construct proof-only `ContextReplacement`, `NestedContextReplacement`, and isomorphism witnesses after the target has been computed.
- Prove two owning iff theorems for every rule. `forward_exact` characterizes `R source target`; `backward_exact` characterizes `R target source`. Each theorem excludes extra results and covers every witness in its direction up to target isomorphism.
- Reject the vacuous empty-family solution structurally: each rule has concrete index constructors, and the reverse direction of the equality theorem must extract one from every corresponding rule witness.
- Follow theorem-driven RED/GREEN one theorem at a time. After supporting definitions compile, enter `forward_exact` with the sole `sorry` and make it GREEN; only then enter and prove `backward_exact`. A task is committed with neither admission remaining.
- Do not add heartbeat or recursion-depth overrides. If a proof needs duplicated traversal, dependent target reconciliation, or growing cast/HEq infrastructure, stop that task, restore its last GREEN boundary, and redesign the index or theorem boundary.
- Preserve all unrelated TypeScript and test changes in the shared worktree. Stage and commit only the task-owned Lean, audit, and plan files.

## Complexity Ledger

- **Essential behavior:** five recursive rule relations; computable forward outputs covering exactly `R source target`; computable backward outputs covering exactly `R target source`; target-isomorphism closure in both orientations.
- **Essential state:** the recursive source diagram, an exact recursive site/nested-site decomposition, and the operands that select one member of a forward or backward nondeterministic rule family.
- **Integrity constraints:** Lean's dependent function type makes one valid source/index pair determine one canonical target representative; the union contains exactly its isomorphism class and equals the selected directed rule; boundaries remain ordered; wire/relation renamings remain well typed; contextual polarity is derived from the supplied recursive context.
- **Derived data:** canonical target diagrams, filled contexts, local before/after regions, and proof-only contextual replacement/isomorphism witnesses.
- **Accidental state to remove:** graph identifiers, checked graph wrappers, receipts, survivor domains, allocation layouts, compiler results, encoded/elaborated mirrors, and representation witnesses.
- **Accidental control to remove:** graph selection/removal/splice pipelines, compilation replay, target reconstruction, refinement dispatch, operation error plumbing, and generated step-tag execution.
- **Code volume:** the replacement is bounded to two exact recursive decomposition types, five rule executor modules, one import-only umbrella, and validation files.
- **Power leaks prohibited:** generic transformation/simulation records, matchers hidden inside adequacy proofs, arbitrary relation evidence as an index, caller-supplied targets, and a second syntax or navigation authority.

## Target File Structure

### Retained authorities

- `VisualProof/Diagram/**`: intrinsic recursive syntax, contexts, paths, isomorphisms, replacements, and semantics.
- `VisualProof/Rule/{Relation,Erasure,WireSever,Iteration,DoubleCut,Vacuity,Step}.lean`: mathematical rule relations.
- `VisualProof/Rule/Soundness.lean` and `VisualProof/Rule/Soundness/**`: semantic soundness.

### New executable authority

- `VisualProof/Diagram/Rewrite.lean`: exact source-side contextual and nested contextual decompositions plus deterministic fill operations.
- `VisualProof/Rule/Executable/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`: rule-specific index types, ten computable `run` functions, and ten exact iff theorems.
- `VisualProof/Rule/Executable.lean`: import-only public executable umbrella.

### Validation authority

- `VisualProof/ComputabilityAudit.lean`: compiler checks for all recursive executable functions.
- `VisualProof/Audit.lean`: axiom audit for exact coverage and isomorphism closure.

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

Rewrite `docs/goals/recursive-rewrite-authority/goal.md` so its oracle is: recursive syntax and rules are the sole authority; for every one of the five rules, forward outputs cover exactly `R source target` up to target isomorphism and backward outputs cover exactly `R target source`; both functions are compiler-accepted; no flat representation/refinement layer exists.

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

### Task 2: Define exact recursive rewrite inputs

**Files:**
- Create: `VisualProof/Diagram/Rewrite.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `OpenDiagram`, `DiagramContext`, `ContextReplacement`, and `NestedContextReplacement`.
- Produces: `ExactSite`, `ExactNestedSite`, and their computable `replace` functions plus proof-only replacement witnesses.

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

- [ ] **Step 3: Validate the rewrite inputs**

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Rewrite.lean
rg -n '\b(Option|HEq)\b' VisualProof/Diagram/Rewrite.lean
git diff --check
```

Expected: strict checking passes and the search returns no matches in the computational rewrite owner.

- [ ] **Step 4: Commit the rewrite boundary**

```bash
git add VisualProof/Diagram/Rewrite.lean VisualProof.lean
git commit -m "define recursive rewrite inputs"
```

**Architecture check:** This file owns source decomposition and deterministic fill only. If it grows rule dispatch, a target field, `Option`, a relation wrapper, or runtime normalization, move that responsibility back to the concrete rule executor.

---

### Task 3: Implement the Erasure executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Erasure.lean`
- Modify: `VisualProof/Rule/Erasure.lean`

**Interfaces:**
- Consumes: `ExactSite`, `Rule.Erasure.Local.erase`, `ContextReplacement.lift`, and `DiagramContext.polarity`.
- Produces: `Erasure.ForwardIndex`, `Erasure.BackwardIndex`, computable `Erasure.runForward`/`runBackward`, two isomorphism-closure proofs, and two exact iff theorems.

- [ ] **Step 1: Define the forward and backward index types**

Define `Erasure.ForwardIndex source` with these constructors:

- `erase`: the local `hostLocal`, `hostItems`, `material`, `wireMap`, and `relationMap`; an `ExactSite source (Region.spliceAt hostLocal hostItems material wireMap relationMap)`; and proof that the site polarity is positive.
- `insert`: the same operands; an `ExactSite source (.mk hostLocal hostItems)`; and proof that the site polarity is negative.

Define `Erasure.BackwardIndex source` with the same two computational shapes but swapped polarity requirements: `erase` is negative and `insert` is positive. Neither type may contain `Rule.Erasure` evidence or a target diagram.

- [ ] **Step 2: Implement the two target functions**

Define both ordinary functions explicitly:

```lean
def Erasure.runForward (source : OpenDiagram arity) :
    Erasure.ForwardIndex source → OpenDiagram arity

def Erasure.runBackward (source : OpenDiagram arity) :
    Erasure.BackwardIndex source → OpenDiagram arity
```

Each function replaces an `erase` site with `.mk hostLocal hostItems` and an `insert` site with `Region.spliceAt ...`. The two definitions are separate compiler targets even where their branch bodies coincide.

- [ ] **Step 3: Prove the two presentation-closure theorems**

In `VisualProof/Rule/Erasure.lean`, prove the two presentation-closure
interfaces from the existing `Rule.Erasure.iso` theorem:

```lean
theorem Erasure.respectsTargetIso
    (step : Rule.Erasure source target)
    (iso : OpenDiagram.Isomorphic target target') :
    Rule.Erasure source target'

theorem Erasure.backward_respectsTargetIso
    (step : Rule.Erasure target source)
    (iso : OpenDiagram.Isomorphic target target') :
    Rule.Erasure target' source
```

- [ ] **Step 4: Prove the two exact adequacy theorems sequentially RED/GREEN**

Enter and prove the forward theorem first:

```lean
theorem Erasure.forward_exact (source target : OpenDiagram arity) :
    (∃ index : Erasure.ForwardIndex source,
      OpenDiagram.Isomorphic (Erasure.runForward source index) target) ↔
    Rule.Erasure source target := by
  sorry
```

After it is GREEN, enter and prove the backward theorem:

```lean
theorem Erasure.backward_exact (source target : OpenDiagram arity) :
    (∃ index : Erasure.BackwardIndex source,
      OpenDiagram.Isomorphic (Erasure.runBackward source index) target) ↔
    Rule.Erasure target source := by
  sorry
```

- [ ] **Step 5: Verify the proof responsibilities**

For each theorem's function-to-relation implication, unpack its own index, construct the canonical contextual rule witness, then apply the corresponding presentation-closure theorem. For each relation-to-function implication, invert the selected rule orientation, construct that direction's index at `source`, and return the rule witness's target isomorphism. Proof-only isomorphism composition may be noncomputable; neither `run` function may call it.

- [ ] **Step 6: Validate both functions and theorems**

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Erasure.lean
rg -n '\b(sorry|admit|HEq)\b' VisualProof/Rule/Executable/Erasure.lean
git diff --check
```

- [ ] **Step 7: Commit**

```bash
git add VisualProof/Rule/Erasure.lean VisualProof/Rule/Executable/Erasure.lean
git commit -m "execute erasure on recursive diagrams"
```

**Architecture check:** The module exposes two index types, two `run` definitions, and two direct iff theorems. Any direction switch inside a shared executor, recursive traversal, or target comparison indicates the boundary is wrong.

---

### Task 4: Implement DoubleCut and Vacuity executable families

**Files:**
- Create: `VisualProof/Rule/Executable/DoubleCut.lean`
- Create: `VisualProof/Rule/Executable/Vacuity.lean`
- Modify: `VisualProof/Rule/DoubleCut.lean`
- Modify: `VisualProof/Rule/Vacuity.lean`

**Interfaces:**
- Consumes: `ExactSite`, `Rule.DoubleCut.wrap`, `Rule.Vacuity.wrap`, their local `introduce` constructors, `atPolarity_symmetric_of`, and their existing `.symm` theorems.
- Produces: forward/backward index types, distinct computable `runForward`/`runBackward` functions, and two exact union theorems in each module.

- [ ] **Step 1: Define DoubleCut's two families**

Define both `DoubleCut.ForwardIndex source` and `DoubleCut.BackwardIndex source` with:

- `introduce`: operands `hostLocal`, `hostItems`, `body`, `wireMap`, `relationMap`, and an exact site at the unwrapped `Region.spliceAt` body.
- `eliminate`: the same operands and an exact site at `Region.spliceAt hostLocal hostItems (DoubleCut.wrap body) wireMap relationMap`.

Define separate `DoubleCut.runForward` and `DoubleCut.runBackward`; each replaces one form with the other. Symmetry makes their branch bodies coincide but does not collapse the two public executors.

- [ ] **Step 2: Prove DoubleCut's two equalities RED/GREEN**

Prove direct `DoubleCut.respectsTargetIso` and `DoubleCut.backward_respectsTargetIso` theorems from `Rule.DoubleCut.iso`. Then prove these sequentially, with only the current owning theorem admitted during its RED state:

```lean
theorem DoubleCut.forward_exact (source target : OpenDiagram arity) :
    (∃ index : DoubleCut.ForwardIndex source,
      OpenDiagram.Isomorphic (DoubleCut.runForward source index) target) ↔
    Rule.DoubleCut source target

theorem DoubleCut.backward_exact (source target : OpenDiagram arity) :
    (∃ index : DoubleCut.BackwardIndex source,
      OpenDiagram.Isomorphic (DoubleCut.runBackward source index) target) ↔
    Rule.DoubleCut target source
```

- [ ] **Step 3: Define Vacuity's two families**

Define `Vacuity.ForwardIndex`, `Vacuity.BackwardIndex`, `runForward`, and `runBackward` with the additional binder `arity` operand and `Vacuity.wrap arity body`. Do not factor the two rule modules through a configurable wrapper function; their constructors remain explicit.

- [ ] **Step 4: Prove Vacuity's two equalities RED/GREEN**

Prove direct `Vacuity.respectsTargetIso` and `Vacuity.backward_respectsTargetIso` theorems from `Rule.Vacuity.iso`. Then prove sequentially:

```lean
theorem Vacuity.forward_exact (source target : OpenDiagram arity) :
    (∃ index : Vacuity.ForwardIndex source,
      OpenDiagram.Isomorphic (Vacuity.runForward source index) target) ↔
    Rule.Vacuity source target

theorem Vacuity.backward_exact (source target : OpenDiagram arity) :
    (∃ index : Vacuity.BackwardIndex source,
      OpenDiagram.Isomorphic (Vacuity.runBackward source index) target) ↔
    Rule.Vacuity target source
```

- [ ] **Step 5: Validate and commit each family**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
rg -n '\b(sorry|admit|HEq)\b' VisualProof/Rule/Executable/{DoubleCut,Vacuity}.lean
git diff --check
git add VisualProof/Rule/DoubleCut.lean VisualProof/Rule/Vacuity.lean VisualProof/Rule/Executable/DoubleCut.lean VisualProof/Rule/Executable/Vacuity.lean
git commit -m "execute modal rules on recursive diagrams"
```

**Architecture check:** Each module has two nonrecursive `run` definitions and two exact iff proofs. Classical proof-only isomorphism work is permitted; shared configurable execution machinery is a power leak and must not be introduced.

---

### Task 5: Implement the Iteration executable family

**Files:**
- Create: `VisualProof/Rule/Executable/Iteration.lean`
- Modify: `VisualProof/Rule/Iteration.lean`

**Interfaces:**
- Consumes: `ExactNestedSite`, `Iteration.WireFreshening`, `Iteration.Local.copy`, `NestedContextReplacement.lift`, and `Iteration.symm`.
- Produces: `Iteration.ForwardIndex`, `Iteration.BackwardIndex`, computable `runForward`/`runBackward`, and two exact iff theorems.

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

- [ ] **Step 2: Define forward and backward copy indices**

Both `Iteration.ForwardIndex source` and `Iteration.BackwardIndex source` have:

- `copy`: an `ExactNestedSite source selected remainder`, `copyLocal`, and `copyWires`.
- `uncopy`: the same selected/remainder/copy data and an `ExactNestedSite source selected (Iteration.copied ...)`.

Both constructors are available in each family because `Rule.Iteration` is symmetric.

- [ ] **Step 3: Implement both functions**

Define separate `Iteration.runForward` and `Iteration.runBackward`. Copy replaces `remainder` by `copied`; uncopy replaces `copied` by `remainder`. Both functions use `ExactNestedSite.replace` and perform no search.

- [ ] **Step 4: Package and prove both exact equalities RED/GREEN**

Prove direct `Iteration.respectsTargetIso` and `Iteration.backward_respectsTargetIso` theorems from `Rule.Iteration.iso`. Then prove sequentially:

```lean
theorem Iteration.forward_exact (source target : OpenDiagram arity) :
    (∃ index : Iteration.ForwardIndex source,
      OpenDiagram.Isomorphic (Iteration.runForward source index) target) ↔
    Rule.Iteration source target

theorem Iteration.backward_exact (source target : OpenDiagram arity) :
    (∃ index : Iteration.BackwardIndex source,
      OpenDiagram.Isomorphic (Iteration.runBackward source index) target) ↔
    Rule.Iteration target source
```

Construct `Iteration.Local.copy` for function-to-rule; for coverage, invert the symmetric nested witness, normalize `after_eq`, construct that direction's index at the exact source, and return the target isomorphism.

- [ ] **Step 5: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Iteration.lean
rg -n '\b(sorry|admit|HEq)\b' VisualProof/Rule/Executable/Iteration.lean
git diff --check
git add VisualProof/Rule/Iteration.lean VisualProof/Rule/Executable/Iteration.lean
git commit -m "execute iteration on recursive diagrams"
```

**Architecture check:** Each executor is one nested fill. Any direction switch, selection partition, path alignment, compiler, or reconstruction theorem indicates an incorrect boundary.

---

### Task 6: Implement the WireSever executable family

**Files:**
- Create: `VisualProof/Rule/Executable/WireSever.lean`
- Modify: `VisualProof/Rule/WireSever.lean`

**Interfaces:**
- Consumes: `ExactSite`, `WireSever.collapseLocal`, `WireSever.Local.sever`, `WireSever.Open`, and `ContextReplacement.lift`.
- Produces: `WireSever.ForwardIndex`, `WireSever.BackwardIndex`, computable `runForward`/`runBackward`, and two exact iff theorems.

- [ ] **Step 1: Define the two local index surfaces**

For `joined : Fin (wires + localWires)` and `separate : ItemSeq (wires + (localWires + 1)) rels`:

- `WireSever.ForwardIndex.localSever` stores an exact site at `.mk localWires (separate.renameWires (WireSever.collapseLocal wires localWires joined))` with positive polarity; `localJoin` stores an exact site at `.mk (localWires + 1) separate` with negative polarity.
- `WireSever.BackwardIndex` contains the same computational branches with sever negative and join positive.

Their targets are the other body, computed directly.

- [ ] **Step 2: Define forward open-sever data**

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

The target is the `OpenDiagram` with `separateBoundary` and `separateBody`. Include this constructor only in `ForwardIndex`.

- [ ] **Step 3: Define backward open-join data**

Define `WireSever.OpenJoinData source` with `targetClasses`, an equality `source.externalClasses = targetClasses + 1`, and a surjective `collapse : Fin source.externalClasses → Fin targetClasses`. Define the target boundary as `collapse ∘ source.boundary`, prove its surjectivity from the supplied maps, and define the target body as `source.body.renameWires collapse`. Include this constructor only in `BackwardIndex`.

- [ ] **Step 4: Implement the two functions**

Define `WireSever.runForward` over forward local sever/join plus open sever, and `WireSever.runBackward` over backward local sever/join plus open join. Local branches call `ExactSite.replace`; open branches construct the stated `OpenDiagram`. No branch returns `Option` or accepts a target.

- [ ] **Step 5: Prove both exact iff theorems RED/GREEN**

Prove direct `WireSever.respectsTargetIso` and `WireSever.backward_respectsTargetIso` theorems from `Rule.WireSever.iso`. Then prove sequentially:

```lean
theorem WireSever.forward_exact (source target : OpenDiagram arity) :
    (∃ index : WireSever.ForwardIndex source,
      OpenDiagram.Isomorphic (WireSever.runForward source index) target) ↔
    Rule.WireSever source target

theorem WireSever.backward_exact (source target : OpenDiagram arity) :
    (∃ index : WireSever.BackwardIndex source,
      OpenDiagram.Isomorphic (WireSever.runBackward source index) target) ↔
    Rule.WireSever target source
```

Local branches construct `WireSever.Local.sever`; open branches construct `WireSever.Open`; coverage returns the existing target isomorphism.

- [ ] **Step 6: Validate and commit**

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/WireSever.lean
rg -n '\b(sorry|admit|HEq)\b' VisualProof/Rule/Executable/WireSever.lean
git diff --check
git add VisualProof/Rule/WireSever.lean VisualProof/Rule/Executable/WireSever.lean
git commit -m "execute wire severance on recursive diagrams"
```

**Architecture check:** Open boundary changes are the only special case. Each direction has its own direct function. If local and open execution start sharing a general renaming/simulation framework, split them back into direct constructors.

---

### Task 7: Install computability and exact-coverage validation

**Files:**
- Create: `VisualProof/Rule/Executable.lean`
- Create: `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: the ten rule `run` functions and the twenty required rule facts.
- Produces: compiler-backed computability evidence, dependency/roster audit, axiom audit, and the final public build.

- [ ] **Step 1: Add the import-only executable umbrella**

Create `VisualProof/Rule/Executable.lean` importing exactly the five rule executor modules, and import that umbrella from `VisualProof.lean`. It defines no dispatcher, wrapper, index, or function.

- [ ] **Step 2: Add compiler-backed computability evidence**

Create `VisualProof/ComputabilityAudit.lean`:

```lean
import Lean.Compiler
import VisualProof.Rule.Executable

open Lean

run_meta Lean.compileDecls #[
  ``VisualProof.Rule.Erasure.runForward,
  ``VisualProof.Rule.Erasure.runBackward,
  ``VisualProof.Rule.WireSever.runForward,
  ``VisualProof.Rule.WireSever.runBackward,
  ``VisualProof.Rule.Iteration.runForward,
  ``VisualProof.Rule.Iteration.runBackward,
  ``VisualProof.Rule.DoubleCut.runForward,
  ``VisualProof.Rule.DoubleCut.runBackward,
  ``VisualProof.Rule.Vacuity.runForward,
  ``VisualProof.Rule.Vacuity.runBackward
]
```

Use the final namespaces exactly as implemented. Compilation failure is a task failure and must be repaired in the computational dependency closure; it places no restriction on theorem proofs or proof-only helper definitions.

- [ ] **Step 3: Extend the source authority audit**

For each of the five rules require exactly `ForwardIndex`, `BackwardIndex`, `runForward`, `runBackward`, `forward_exact`, `backward_exact`, `respectsTargetIso`, and `backward_respectsTargetIso`. Reject aggregate dispatch, program/replay types, `ExecutableFamily`/`Member` wrappers, `Functional` predicates, named direction switches, and direction-switched executors. Reject imports from executable modules into mathematical rule or soundness modules and reject any remaining flat-representation or refinement authority under `VisualProof`.

- [ ] **Step 4: Extend the axiom audit**

Add `#print axioms` for every rule's `forward_exact`, `backward_exact`, `respectsTargetIso`, and `backward_respectsTargetIso`. The output may contain Lean’s accepted classical/propext axioms from proof-only isomorphism reasoning, but must not contain project placeholder axioms.

- [ ] **Step 5: Run strict module validation**

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Rewrite.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Erasure.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/WireSever.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Iteration.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable.lean
lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
```

- [ ] **Step 6: Run final architecture and family-coverage validation**

```bash
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
rg -n '\b(sorry|admit|decreasing_by sorry|^axiom |set_option (maxHeartbeats|maxRecDepth))\b' VisualProof
rg -n 'VisualProof\.(Concrete|Refinement)|namespace VisualProof\.(Concrete|Refinement)' VisualProof VisualProof.lean lakefile.toml
lake build
git diff --check
git status --short
```

Expected: strict checks and full build pass; both forbidden searches return no matches; status lists only unrelated user changes before staging.

- [ ] **Step 7: Perform the final architecture-compensation review**

Inspect each family and confirm:

- each rule has two ordinary computable functions, each a direct constructor/fill operation with no recursion other than structural recursive syntax helpers;
- each index contains no target, relation evidence, isomorphism, or semantic proof;
- each exact theorem uses `∃ index, Isomorphic (run source index) target`, with no raw-target equality requirement;
- each rule has two exact iff theorems, two target-isomorphism closure proofs, and no generic relation/functionality wrapper or soundness/completeness record fields;
- no file raises elaboration limits.

If any item fails, return to the owning task and redesign before committing.

- [ ] **Step 8: Commit final audits**

```bash
git add VisualProof/Rule/Executable.lean VisualProof/ComputabilityAudit.lean VisualProof/Audit.lean scripts/audit-lean-authority.sh VisualProof.lean
git commit -m "audit recursive rule execution"
```

## Self-Review

- **Spec coverage:** Task 1 removes the representation split. Task 2 provides deterministic recursive fills. Tasks 3–6 define separate computable forward and backward indexed functions for all five rules and establish exactly four required facts per rule. Task 7 validates computability, exact coverage, isomorphism closure, and dependency direction.
- **Anti-vacuity:** Indices cannot contain `R` evidence or a target, every rule exports concrete indices in both directions, the reverse implication extracts those indices from every rule witness, and the compiler audit checks the actual functions.
- **Exact adequacy:** `forward_exact` equates `∃ index, Isomorphic (runForward source index) target` with `R source target`; `backward_exact` equates the analogous backward executor with `R target source`. Neither missing valid rule instances nor extra executable transitions can pass.
- **Type consistency:** Every forward/backward `Index source` is a type of valid choices for that source; every `runForward source` and `runBackward source` is an ordinary computable function to an `OpenDiagram arity`.
- **Architecture discipline:** Deletion occurs before replacement. There is one direct exact-site boundary, two explicit functions and two direct iff theorems per rule, no generic family/relation wrapper, no quotient runtime or theorem carrier, no representation/refinement bridge, no target search, no second recursive syntax, and explicit stop/rethink gates after every implementation task.
