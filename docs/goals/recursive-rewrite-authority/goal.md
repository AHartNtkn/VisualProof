# Recursive Rule Execution

## Objective

Keep recursive `OpenDiagram` syntax as the only execution representation and
make `Rule.Step.Evidence` the single proof-relevant inventory of executable
one-step relations. `Rule.Step source target` is the relational view of that
inventory: `Nonempty (Step.Evidence source target)`.

## Step Authority

`Step.Evidence` has exactly fifteen families:

- `WireSever`, `Iteration`, `DoubleCut`, `Vacuity`, `Presentation`, and
  `Identification`;
- `WirePrimitive.CutShape`, `ParallelShape`, `Ends`, `Arity`,
  `ArgumentPermutation`, `ArgumentDuplicate`, `ArgumentProjection`,
  `FormalApplication`, and `IdentityLeaf`.

Each family owns a source-indexed forward runner and backward runner whose
`Option OpenDiagram` result is exact up to `OpenDiagram.Isomorphic`. For every
executable family `R`, exactness
has these precise orientations:

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

Each family proves target-isomorphism closure in both orientations.
`Step.iso` is the public two-sided closure theorem:

```lean
OpenDiagramIso source source' →
  Step source target →
  OpenDiagramIso target target' →
  Step source' target'
```

`Step.sound` is the public semantic theorem for the same evidence roster.

`Step.forward_execution_complete` and `Step.backward_execution_complete` are
proof-only exhaustive coverage theorems. They eliminate `Step.Evidence` and
select an existing family runner; they do not define an aggregate runtime
dispatcher. No aggregate runtime dispatcher is permitted.

## Standalone Boundaries

`Erasure` remains a standalone relation with its own two runners and is
excluded from `Step.Evidence`.
`Comprehension` remains standalone recursive mathematics with semantic
soundness and no executor. Neither relation is a `Step` constructor.

## Execution Boundary

- Indices select a source occurrence and the operands used to compute the
  counterpart; they contain neither a desired target nor evidence that the
  relation already holds.
- Runners do not search for occurrences, inspect proposed targets, or act as
  generic programs. They perform no discovery traversal and rebuild only the
  supplied recursive context. Runtime is proportional to that context depth
  and local construction, not to unselected source subtrees.
- Proofs may use classical reasoning. Each runner's evaluated dependency
  closure must remain computable.
- The executable umbrella is import-only; `Executable/Step.lean` has no
  independent inductive roster and no aggregate `runForward`, `runBackward`,
  or dispatcher definition.
- No executable owner or umbrella refers to Comprehension execution.

## Governing Plans

- `docs/superpowers/plans/2026-08-13-recursive-rule-execution.md`
- `docs/superpowers/plans/2026-08-20-restore-step-execution-boundary.md`

## Validation

`lake build` must elaborate the authoritative relations, runners, exactness
theorems, soundness theorems, and exhaustive Step coverage. The production
Lean source must contain no admissions or project axioms.
