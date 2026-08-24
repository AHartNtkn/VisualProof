# Recursive Rule Execution Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Use recursive `OpenDiagram` syntax as the sole execution
representation and give every executable relation family a direct forward and
backward runner whose successful outputs are exactly that relation up to target
isomorphism.

**Architecture:** Each relation family owns source-indexed data describing one
already-selected instance and two ordinary functions, `runForward` and
`runBackward`. A runner may reject an invalid index with `none`; on success it
performs the selected local operation and rebuilds only the explicitly supplied
recursive context. Mathematical rule modules remain the relational authority,
and exact iff theorems prove that successful executions produce every and only
instances of the relation.

**Tech Stack:** Lean 4.30.0, Lake, recursive
`OpenDiagram`/`Region`/`ItemSeq` syntax, source-indexed occurrences and
contexts, and the public Lean compiler with build-plus-source validation.

## Authority Roster

`Rule.Step.Evidence` is the sole proof-relevant one-step authority. It contains
exactly these fifteen executable relation families:

- `WireSever`, `Iteration`, `DoubleCut`, `Vacuity`, `Presentation`, and
  `Identification`;
- `WirePrimitive.CutShape`, `WirePrimitive.ParallelShape`,
  `WirePrimitive.Ends`, `WirePrimitive.Arity`,
  `WirePrimitive.ArgumentPermutation`, `WirePrimitive.ArgumentDuplicate`,
  `WirePrimitive.ArgumentProjection`, `WirePrimitive.FormalApplication`, and
  `WirePrimitive.IdentityLeaf`.

`Rule.Step source target` is exactly
`Nonempty (Rule.Step.Evidence source target)`. `Erasure` is an independently
executable relation with the same runner contract but is not a `Step`
constructor. `Comprehension` is a standalone recursively defined mathematical
relation with semantic soundness; it has no executable module, runner, or
`Step` constructor.

## Rule-Level Execution Contract

For every executable relation family `R`, the public runners have
source-indexed input and partial output:

```lean
runForward : (source : OpenDiagram boundary) →
  ForwardIndex source → Option (OpenDiagram boundary)

runBackward : (source : OpenDiagram boundary) →
  BackwardIndex source → Option (OpenDiagram boundary)
```

Their exactness theorem types, including the backward orientation, are:

```lean
(∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
    runForward source index = some output ∧
      OpenDiagram.Isomorphic output target) ↔
  R source target

(∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
    runBackward source index = some output ∧
      OpenDiagram.Isomorphic output target) ↔
  R target source
```

Every executable family also proves target-isomorphism closure in both exact
orientations:

```lean
R source target →
  OpenDiagram.Isomorphic target target' →
  R source target'

R target source →
  OpenDiagram.Isomorphic target target' →
  R target' source
```

## Step-Level Proof Contract

`Step.iso` is the two-sided isomorphism closure theorem, with this exact public
type:

```lean
OpenDiagramIso source source' →
  Step source target →
  OpenDiagramIso target target' →
  Step source' target'
```

`Step.sound` carries a `Step source target` denotation forward in every model
at the same boundary arguments. Both declarations elaborate in their owning
modules. No admission or project axiom is permitted in these or the other
public Step contract theorems.

`Step.forward_execution_complete` and
`Step.backward_execution_complete` have the exact public result shapes:

```lean
Step source target →
  ∃ evidence : Step.Evidence source target, evidence.ForwardExecutable

Step source target →
  ∃ evidence : Step.Evidence source target, evidence.BackwardExecutable
```

For each evidence constructor, `ForwardExecutable` and `BackwardExecutable`
reduce to the corresponding family-owned Option-success proposition above;
backward execution runs from `target` and returns a result isomorphic to
`source`. These two theorems are proof-only exhaustive coverage. They do not
define a Step-level `runForward`, `runBackward`, dispatcher, search procedure,
or independent inductive roster.

## Global Constraints

- Each `ForwardIndex source` and `BackwardIndex source` identifies one precise,
  already-selected rule instance. It may contain a source occurrence or
  decomposition, local operands, finite maps, and proofs that those operands
  are valid at the source.
- An index must not contain the desired target diagram, evidence of the rule
  relation, a completed source-to-target replacement, or a function whose
  captured result is the desired target.
- A runner performs no site discovery, source traversal to find an occurrence,
  target search, proposed-target inspection, or semantic evaluation. It
  validates only the supplied index data, performs one local rewrite, and
  rebuilds the supplied recursive context spine.
- Runtime is proportional to the explicitly supplied context depth and local
  operand construction. It is independent of the size of unselected source
  subtrees and performs no hidden global search.
- Only the runners and definitions in their evaluated dependency closures must
  be computable. Correctness theorems and proof-only helpers may use classical
  reasoning, `Classical.choice`, and noncomputable proof definitions.
- Lean function types already provide functionality. Do not add program,
  family, member, replay, functionality, direction, generic execution,
  compatibility, or aggregate dispatcher wrappers.
- The executable umbrella remains import-only. `Executable/Step.lean` owns only
  dependent proof coverage definitions and the two completeness theorems; it
  contains no independent `inductive` roster or aggregate executor.
- No executable owner or umbrella may refer to or declare Comprehension
  execution.
- Remove displaced dependents rather than preserving aliases, adapters,
  re-exports, compatibility modules, fallback behavior, or a second execution
  authority.
- Do not raise heartbeat or recursion-depth limits. If a proof duplicates
  navigation, accumulates casts/`HEq`, or reconstructs targets by search,
  restore the last GREEN boundary and redesign the index or theorem boundary.

## Complexity Ledger

- **Essential behavior:** one forward runner, one backward runner, one exact iff
  theorem per direction, and two target-isomorphism closure laws for each of the
  fifteen Step families and standalone Erasure; two additional proof-only Step
  coverage theorems.
- **Public computability boundary:** thirty Step runners plus two standalone
  Erasure runners. One locally bound `Array Name` must contain exactly all
  thirty-two declarations, and that same array is passed to
  `Lean.compileDecls`.
- **Essential state:** the recursive source diagram, a source-side
  occurrence/decomposition selecting the instance, and local data needed to
  compute its counterpart.
- **Integrity constraints:** an index is valid only at its source; local wire
  and relation maps are typed at the selected hole; a runner may validate that
  supplied data but neither guesses nor discovers applicability.
- **Derived data:** the replacement body, context-filled output, and proof-only
  relational and isomorphism witnesses.
- **Accidental state prohibited:** graph mirrors, receipts, survivor or
  allocation tables, compiler traces, encoded execution mirrors, target
  reconstruction certificates, and lifecycle state.
- **Accidental control prohibited:** discovery traversal, graph splice/replay
  pipelines, dispatch programs, target search, generic execution direction
  switches, and error-plumbing abstractions beyond the runner's `Option` result.
- **Power leaks prohibited:** caller-supplied targets, relation witnesses as
  indices, generic simulation/transformation frameworks, hidden search in
  adequacy proofs, and aggregate runtime execution containers.

## Authority Layout

### Mathematical and semantic authority

- `VisualProof/Diagram/**`: recursive syntax, contexts, occurrences,
  isomorphisms, and semantics.
- `VisualProof/Rule/Step.lean`: the exact fifteen-family evidence roster,
  relational view, and two-sided isomorphism closure.
- `VisualProof/Rule/{Erasure,WireSever,Iteration,DoubleCut,Vacuity,Presentation,Identification}.lean`
  and `VisualProof/Rule/WirePrimitive/**`: mathematical relations and closure
  laws.
- `VisualProof/Rule/Comprehension.lean`: standalone recursive mathematics.
- `VisualProof/Rule/Soundness.lean` and `VisualProof/Rule/Soundness/**`:
  semantic soundness, including standalone Comprehension soundness.

### Executable authority

- `VisualProof/Diagram/NestedOccurrence.lean`: source-side nested selection and
  direct replacement support.
- `VisualProof/Rule/Executable/{Erasure,WireSever,Iteration,DoubleCut,Vacuity,Presentation,Identification}.lean`
  and `VisualProof/Rule/Executable/WirePrimitive/**`: family-owned indices,
  runners, and exactness proofs.
- `VisualProof/Rule/Executable/Step.lean`: proof-only exhaustive Step coverage.
- `VisualProof/Rule/Executable.lean`: import-only umbrella.

## Theorem-Driven RED/GREEN Workflow

- Complete every definition in an owning theorem's dependency closure before
  RED. The sole admitted term in RED is the owning production theorem proof.
- Enter and elaborate one exactness or completeness theorem with `sorry`; scan
  the relevant closure to prove no definition or helper is admitted.
- Replace that proof with a kernel-checked term and confirm its axiom output
  before beginning the next direction or theorem.
- Do not create redundant aliases, fixture theorems, `example`s, or `#check`
  declarations in production to manufacture RED/GREEN.

## Completion Oracle

Run and require all of the following:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Step.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Step.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
rg -n '\b(sorry|admit|decreasing_by sorry|^axiom |set_option (maxHeartbeats|maxRecDepth))\b' VisualProof
lake build
git diff --check
```

The no-admission search must return no matches. The focused owner builds and
full build must elaborate the exact Step contract and every family-owned
runner used by its exhaustive coverage proofs.

## Self-Review

- **Spec coverage:** the Step roster and proof coverage range over the same
  fifteen relations; Erasure and Comprehension retain their standalone roles.
- **Anti-vacuity:** indices select source data and local operands without a
  target or relation evidence.
- **Execution cost:** no discovery or source traversal; only supplied-context
  rebuilding and local validation/construction are permitted.
- **Proof freedom:** classical proof machinery remains outside the public
  runners' evaluated dependency closures.
- **Architecture discipline:** there is one evidence roster, family-owned
  executors, an import-only umbrella, and no aggregate runtime dispatcher.
