# Recursive Rule Execution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove graph execution and define direct recursive executors for exactly the five constructors of `Rule.Step`, with forward and backward outputs equal to the corresponding rule relation up to target isomorphism.

**Architecture:** Each rule owns source-indexed data describing one already-selected instance and two ordinary functions, `runForward` and `runBackward`. A runner performs no search or discovery: it applies the local operation and rebuilds only the explicitly supplied recursive context. The mathematical rule modules remain the relational authority; exact iff theorems prove that the executors produce every and only rule instances.

**Tech Stack:** Lean 4.30.0, Lake, recursive `OpenDiagram`/`Region`/`ItemSeq` syntax, `Occurrence`, `DiagramContext`, and the five existing `Rule.Step` relations.

## Global Constraints

- Scope is exactly `Erasure`, `WireSever`, `Iteration`, `DoubleCut`, and `Vacuity`, the five constructors of `Rule.Step`. `Comprehension` has no executable obligation.
- For each rule, define separate source-indexed `ForwardIndex source` and `BackwardIndex source` types and separate ordinary `runForward` and `runBackward` functions.
- An index describes the precise already-selected rule instance. It may contain a source occurrence/decomposition, local operands, finite maps, and proofs that those operands are valid at the source.
- An index must not contain the desired target diagram, evidence of the rule relation, a completed replacement from source to target, or a function whose captured result is the desired target.
- A runner returns `OpenDiagram arity`, never `Option`. Applicability is expressed by whether `ForwardIndex source` or `BackwardIndex source` has a value.
- A runner performs no traversal to discover a site, no target search, and no semantic evaluation. It performs one local rewrite and rebuilds the supplied context spine. Consequently, runtime is proportional to the explicitly supplied context depth and local operand construction, independent of the size of unselected source subtrees.
- Coverage is up to target presentation:

  ```lean
  (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    R source target

  (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    R target source
  ```

- Every rule also proves closure under changing the computed endpoint by isomorphism in both orientations:

  ```lean
  R source target → OpenDiagram.Isomorphic target target' → R source target'
  R target source → OpenDiagram.Isomorphic target target' → R target' source
  ```

- Only `runForward`, `runBackward`, and definitions they evaluate must be computable. The correctness theorems and proof-only helpers may use classical reasoning, `Classical.choice`, and `noncomputable` definitions.
- Lean function types already provide functionality. Do not add program, family, member, replay, functionality, direction, or aggregate execution wrappers.
- Remove obsolete dependents rather than preserving aliases, adapters, re-exports, compatibility modules, or a second execution authority.
- Use theorem-driven RED/GREEN. Supporting definitions must compile before an owning exactness theorem is entered with the sole `sorry`; replace that `sorry` with a kernel-checked proof before beginning the other direction.
- Do not raise heartbeat or recursion-depth limits. If a proof starts duplicating navigation, accumulating casts/`HEq`, or reconstructing targets by search, restore the last GREEN boundary and redesign the index or theorem boundary.

## Complexity Ledger

- **Essential behavior:** ten direct executors; ten exact iff theorems; two target-isomorphism closure laws per rule.
- **Essential state:** the recursive source diagram; a source-side occurrence/decomposition identifying the selected instance; the local data needed to compute the other side of that instance.
- **Integrity constraints:** an index is valid only at its source; local wire and relation maps are typed at the selected hole; the runner neither guesses nor validates applicability at runtime.
- **Derived data:** the replacement body, the context-filled output diagram, and all proof-only relational/isomorphism witnesses.
- **Accidental state to remove:** graph states, checked graph mirrors, receipts, allocation/survivor tables, compiler traces, encoded/elaborated mirrors, target reconstruction certificates, and execution lifecycle data.
- **Accidental control to remove:** selection discovery, graph splice/removal pipelines, compilation replay, dispatch programs, error plumbing, and step-tag generation.
- **Code volume to remove:** every module whose only purpose is graph execution, graph refinement, graph replay, or auditing those systems; all imports, build targets, scripts, and documents that keep those modules reachable.
- **Power leaks prohibited:** caller-supplied targets, rule witnesses as indices, generic simulation/transformation frameworks, hidden search inside adequacy proofs, and generic execution containers.

## Target File Structure

### Retained mathematical authority

- `VisualProof/Diagram/**`: recursive syntax, contexts, occurrences, isomorphisms, and semantics.
- `VisualProof/Rule/{Relation,Erasure,WireSever,Iteration,DoubleCut,Vacuity,Step}.lean`: the five mathematical relations and their aggregate.
- `VisualProof/Rule/Soundness.lean` and `VisualProof/Rule/Soundness/**`: semantic soundness, including comprehension soundness where independently required.

### New executable authority

- `VisualProof/Diagram/NestedOccurrence.lean`: the source half of a nested replacement and its direct `replace` function.
- `VisualProof/Rule/Executable/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`: rule-specific index types, runners, and exactness theorems.
- `VisualProof/Rule/Executable.lean`: import-only umbrella.

### Validation authority

- `VisualProof/ComputabilityAudit.lean`: asks Lean's code generator to compile the ten runners. This is a validation file, not an execution abstraction.
- `VisualProof/Audit.lean`: prints axioms for exactness and isomorphism-closure theorems.

---

### Task 1: Remove the graph execution closure and all orphaned dependents

**Files:**
- Remove: `VisualProof/Concrete.lean` and `VisualProof/Concrete/**`
- Remove: `VisualProof/Refinement/**`
- Remove: graph-backed `VisualProof/Proof/**`
- Remove: current `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `lakefile.toml`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: architecture/goal documents that describe graph execution

**Interfaces:**
- Consumes: recursive diagram syntax, the five rule relations, and semantic soundness.
- Produces: a recursive-only build with no reachable graph execution, refinement, replay, or step-tag authority.

- [x] **Step 1: Establish the dependency and deletion boundary**

  Run:

  ```bash
  git status --short
  rg -n '^import VisualProof\.(Concrete|Refinement|Proof)' VisualProof VisualProof.lean
  rg -n 'Concrete|Refinement|StepTags|Proof\.(Replay|Schema|Theorem|Theory)' lakefile.toml VisualProof.lean scripts docs
  ```

  Classify every match as retained mathematical/semantic authority or obsolete execution-dependent material. Add every obsolete importer, build target, audit, and document to this task; do not leave unreachable source behind.

- [x] **Step 2: Remove the complete obsolete closure**

  Use `git rm` for the graph, refinement, graph-backed proof, step-tag, and obsolete audit modules established in Step 1. Remove the `visualproof_step_tags` executable from `lakefile.toml`. Remove their imports from `VisualProof.lean` and all retained aggregators.

- [x] **Step 3: Narrow the retained audits and documentation**

  Make `VisualProof/Audit.lean` cover only retained recursive rules and semantic soundness. Rewrite the authority audit and active goal document around the five recursive executors and the exactness contract in this plan.

- [x] **Step 4: Validate the recursive-only boundary**

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Rule/Step.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
  lake build
  rg -n 'VisualProof\.(Concrete|Refinement)|namespace VisualProof\.(Concrete|Refinement)' VisualProof VisualProof.lean lakefile.toml
  git diff --check
  ```

  Expected: builds pass and the final search is empty.

- [x] **Step 5: Commit the removal boundary**

  Stage only the files classified in this task and commit as `remove graph execution closure`.

**Architecture check:** Nothing retained may require graph states, compilation, receipts, replay programs, or refinement bridges. If an importer has no purpose independent of those systems, remove it rather than adapting it.

---

### Task 2: Define the one missing source-side selection type

**Files:**
- Create: `VisualProof/Diagram/NestedOccurrence.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: existing `Occurrence` for ordinary contextual rules and existing recursive contexts.
- Produces: `NestedOccurrence selected before source` and its direct `replace` operation for iteration.

- [x] **Step 1: Reuse `Occurrence` for ordinary contextual rules**

  Do not introduce an ordinary-site wrapper. A contextual index stores:

  ```lean
  occurrence : Occurrence before source
  ```

  Its output representative is computed directly as:

  ```lean
  occurrence.interface.withBody (occurrence.context.fill after)
  ```

  `Occurrence.host_iso` is source-location evidence, not rule evidence or a supplied target.

- [x] **Step 2: Define only the source half needed by nested iteration**

  Define:

  ```lean
  structure NestedOccurrence
      (selected : Region (ancestorWires + anchorLocal) ancestorRels)
      (before : Region descendantWires descendantRels)
      (source : OpenDiagram arity) where
    interface : OpenDiagram arity
    outer : DiagramContext interface.externalClasses ancestorWires [] ancestorRels
    descendant : DiagramContext (ancestorWires + anchorLocal)
      descendantWires ancestorRels descendantRels
    source_iso : OpenDiagramIso source
      (interface.withBody
        (outer.fill
          (Region.adjoinAt anchorLocal .nil
            (selected.conjoin (descendant.fill before)))))
  ```

  Define `NestedOccurrence.replace occurrence after` by changing only `before` to `after` in that displayed recursive expression. It must be an ordinary computable definition and must not store or inspect a target.

- [x] **Step 3: Validate and commit**

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Diagram/NestedOccurrence.lean
  rg -n '\b(Option|HEq)\b|target\s*:' VisualProof/Diagram/NestedOccurrence.lean
  git diff --check
  ```

  Commit as `define nested recursive occurrence`.

**Architecture check:** Ordinary contextual rules use existing `Occurrence`; iteration gets exactly one analogous nested source occurrence. Neither type performs discovery or contains the computed endpoint.

---

### Task 3: Implement Erasure in both directions

**Files:**
- Create: `VisualProof/Rule/Executable/Erasure.lean`
- Modify: `VisualProof/Rule/Erasure.lean`

**Interfaces:**
- Produces: `Erasure.ForwardIndex`, `Erasure.BackwardIndex`, `runForward`, `runBackward`, `forward_exact`, `backward_exact`, and the two target-isomorphism closure theorems.

- [ ] **Step 1: Define the asymmetric indices**

  `ForwardIndex source` has an `erase` constructor containing the operands of `Erasure.Local.erase`, an `Occurrence` of the spliced body in `source`, and positive polarity; it also has an `insert` constructor containing the same operands, an occurrence of the smaller body, and negative polarity.

  `BackwardIndex source` reverses those source shapes and polarity obligations: it needs the full insertion description when the backward executor adds material. Neither index contains a target or `Rule.Erasure` evidence.

- [ ] **Step 2: Define both runners**

  Each branch computes the opposite local body and fills its supplied occurrence. The definitions contain no recursion except `DiagramContext.fill`, no source inspection, and no branch that can fail.

- [ ] **Step 3: Prove target-isomorphism closure**

  Derive `Erasure.respectsTargetIso` and `Erasure.backward_respectsTargetIso` directly from `Erasure.iso` with a reflexive source isomorphism.

- [ ] **Step 4: Prove exactness sequentially RED/GREEN**

  Prove the two global iff statements from the constraints section. In the executable-to-rule direction, build the contextual witness from the index. In the rule-to-executable direction, invert the contextual witness and its polarity, construct the corresponding index, and return its existing target isomorphism.

- [ ] **Step 5: Validate and commit**

  Strict-check the rule and executable modules, scan them for admissions and raised limits, run `git diff --check`, and commit as `execute erasure recursively`.

**Architecture check:** The backward insertion index must carry the material description; the forward erasure index need only identify it in the source. No common “program” abstraction is permitted.

---

### Task 4: Implement DoubleCut and Vacuity in both directions

**Files:**
- Create: `VisualProof/Rule/Executable/DoubleCut.lean`
- Create: `VisualProof/Rule/Executable/Vacuity.lean`
- Modify: `VisualProof/Rule/DoubleCut.lean`
- Modify: `VisualProof/Rule/Vacuity.lean`

- [ ] **Step 1: Define direct introduction and elimination data**

  For each rule and direction, define constructors that either identify an unwrapped occurrence and carry the data needed to construct the wrapper, or identify the wrapped occurrence and carry the data needed to remove it. Vacuity introduction additionally carries the binder arity. Keep distinct public forward and backward index types even when their constructors are structurally similar.

- [ ] **Step 2: Define the four runners**

  Each runner performs one `wrap`/unwrap local computation and fills the supplied `Occurrence`. It performs no traversal or recognition of wrapper syntax outside data already present in the index.

- [ ] **Step 3: Prove closure and exactness**

  For each rule, derive the two target-isomorphism closure laws from its existing `.iso` theorem. Prove forward exactness GREEN before entering backward exactness. Use the existing symmetric local relation only in proofs, not as a runtime direction abstraction.

- [ ] **Step 4: Validate and commit separately**

  Strict-check both executable modules, scan for admissions/raised limits, run their focused builds, and commit each independently.

**Architecture check:** Similar rule shapes do not justify a configurable wrapper executor. Four direct functions are smaller and expose exactly the required behavior.

---

### Task 5: Implement Iteration in both directions

**Files:**
- Create: `VisualProof/Rule/Executable/Iteration.lean`
- Modify: `VisualProof/Rule/Iteration.lean`

- [ ] **Step 1: Define the local copied body**

  Add one computable helper equal to the right-hand side of `Iteration.Local.after_eq`, using the supplied `selected`, `descendant`, `copyLocal`, and `WireFreshening`.

- [ ] **Step 2: Define asymmetric source-indexed data**

  A copy constructor stores `NestedOccurrence selected remainder source`, `copyLocal`, and `copyWires`. An uncopy constructor stores `NestedOccurrence selected copied source` plus the same data needed to identify the exact copied instance. Define both forward and backward index types explicitly.

- [ ] **Step 3: Define both runners**

  Copy calls `NestedOccurrence.replace` with the computed copied body. Uncopy calls it with the remainder. There is no nested-site discovery or comparison against a proposed target.

- [ ] **Step 4: Prove closure and exactness**

  Derive both target-isomorphism closure laws from `Iteration.iso`; prove the two exact iff theorems sequentially using `NestedContextReplacement.lift` only in proof code.

- [ ] **Step 5: Validate and commit**

  Strict-check, scan for admissions and raised limits, run the focused build, and commit as `execute iteration recursively`.

**Architecture check:** The index supplies the selected ancestor and descendant occurrence directly. Any path search, selection partition, or replay traversal is a design failure.

---

### Task 6: Implement WireSever in both directions

**Files:**
- Create: `VisualProof/Rule/Executable/WireSever.lean`
- Modify: `VisualProof/Rule/WireSever.lean`

- [ ] **Step 1: Define local sever/join data**

  Local sever stores `joined`, `separate`, an occurrence of the collapsed local body, and the required polarity. Local join stores the corresponding occurrence of the separated body and inverse polarity. Define the forward and backward variants explicitly.

- [ ] **Step 2: Define open-boundary data without a target**

  Forward open sever data stores the new external-class count, separated boundary, collapse map and its laws, and separated body whose collapse recovers the source body. Backward open join data stores the collapse from the source boundary classes to the smaller target class count; the runner derives the joined boundary and renamed body. These are operands describing the rule instance, not a stored `OpenDiagram` target.

- [ ] **Step 3: Define both runners**

  Local branches fill their supplied occurrence. Open branches construct the output `OpenDiagram` directly from the supplied boundary/body operands. No branch searches for a wire or returns `Option`.

- [ ] **Step 4: Prove closure and exactness**

  Derive both target-isomorphism closure laws from `WireSever.iso`. Prove forward exactness, then backward exactness, by matching the contextual/open disjunction and returning the rule witness's target isomorphism.

- [ ] **Step 5: Validate and commit**

  Strict-check, scan for admissions and raised limits, run the focused build, and commit as `execute wire severance recursively`.

**Architecture check:** Open sever and open join are legitimately asymmetric. Do not force them through a general renaming or simulation framework.

---

### Task 7: Install public imports and direct validation

**Files:**
- Create: `VisualProof/Rule/Executable.lean`
- Create: `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `scripts/audit-lean-authority.sh`
- Modify: `VisualProof.lean`

- [ ] **Step 1: Add an import-only umbrella**

  `VisualProof/Rule/Executable.lean` imports the five executable modules and declares nothing.

- [ ] **Step 2: Validate code generation for the ten runners**

  In `VisualProof/ComputabilityAudit.lean`, use Lean's test-only `Lean.compileDecls` command on the ten runner names. This asks Lean's code generator to compile those definitions and fails if their computational dependency closure contains a noncomputable definition. It creates no runtime API and imposes no restriction on theorem proofs.

- [ ] **Step 3: Validate the public theorem roster**

  Require exactly these declarations for each rule: `ForwardIndex`, `BackwardIndex`, `runForward`, `runBackward`, `forward_exact`, `backward_exact`, `respectsTargetIso`, and `backward_respectsTargetIso`. Reject aggregate executors, direction switches, replay/program types, target fields, rule-evidence fields, and imports from executable modules into mathematical rule or soundness modules.

- [ ] **Step 4: Run final validation**

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Diagram/NestedOccurrence.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Erasure.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable/WireSever.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Iteration.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable/DoubleCut.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean
  lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
  lake env lean -DwarningAsError=true VisualProof/Audit.lean
  scripts/audit-lean-authority.sh rules
  scripts/audit-lean-authority.sh implementation
  rg -n '\b(sorry|admit|decreasing_by sorry|^axiom |set_option (maxHeartbeats|maxRecDepth))\b' VisualProof
  lake build
  git diff --check
  ```

- [ ] **Step 5: Perform the architecture-compensation review**

  Confirm that every runner merely pattern-matches its index, constructs one local counterpart, and fills the supplied occurrence; no runner traverses the source to discover anything. Confirm that proof code has not introduced a second navigation authority, target reconstruction layer, or raised elaboration limits. Backtrack the owning task if either check fails.

- [ ] **Step 6: Commit validation authority**

  Commit the umbrella and audits as `audit recursive rule execution`.

## Self-Review

- **Spec coverage:** exactly five `Rule.Step` rules; two direct functions, two exact iff theorems, and two target-isomorphism closure laws per rule.
- **Anti-vacuity:** indices may describe the source occurrence and operands but cannot contain the desired target or evidence that the rule holds.
- **Execution cost:** no discovery or source traversal; cost is rebuilding the explicitly supplied context spine plus local construction.
- **Proof freedom:** classical/noncomputable proof machinery is allowed outside the runners' evaluated dependency closures.
- **Removal discipline:** the graph execution closure and every orphaned dependent/build/audit/documentation surface are removed before replacement.
- **Architecture discipline:** existing `Occurrence` is reused, only one nested source occurrence is added, and no generic program/family/relation/functionality wrapper exists.
