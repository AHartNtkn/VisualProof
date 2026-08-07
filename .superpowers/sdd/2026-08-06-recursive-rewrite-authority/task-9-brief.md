# Task 9 brief: successful execution refinement

Base commit: `26b57d84`

## Outcome

Prove that each successful concrete execution realizes exactly one of the six
recursive rule relations.  Concrete execution evidence may be used only below
`VisualProof.Refinement`; it must not become part of the recursive rule or
semantic authority.

## Required family mapping

The mapping is exhaustive and fixed:

| Recursive relation | Concrete constructors |
| --- | --- |
| `Erasure` | `erasure`, `boundRelationSpawn` |
| `WireSever` | `wireSever`, `wireJoin` |
| `Iteration` | `iteration`, `deiteration` |
| `DoubleCut` | `doubleCutIntro`, `doubleCutElim` |
| `Comprehension` | `comprehensionAbstract`, `comprehensionInstantiate` |
| `Vacuity` | `vacuousIntro`, `vacuousElim` |

Create one owner for each family at
`VisualProof/Refinement/Step/{Erasure,WireSever,Iteration,DoubleCut,Comprehension,Vacuity}.lean`
and an aggregate at `VisualProof/Refinement/Step.lean`.

For each concrete constructor, prove from its actual successful
`Concrete.execute` equation that the translated source and target satisfy the
assigned recursive relation.  Existing operational proof towers that establish
the necessary compiler, splice, attachment, carrier, or receipt facts must be
moved under the matching refinement owner or under
`Refinement/Implementation`; migrate their consumers rather than retaining a
parallel owner under `Rule.Soundness`.

`Concrete.Insertion` must carry
`input.AttachmentsRespectBoundary`.  This existing predicate is the exact
legality condition under which the splice attachment quotient is discrete on
retained host wires, so `boundRelationSpawn` realizes only the converse of
`Erasure`.  Add the field in `VisualProof/Concrete/Step.lean`, migrate request
constructors, and use the existing discrete-quotient/open-isomorphism bridge.
Do not weaken `Erasure` or combine insertion with `WireSever`/wire joining.

## Public theorems

The aggregate theorem is:

```lean
theorem execute_sound
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source request = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.Step sourceDiagram targetDiagram
       | .backward => Rule.Step targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram
```

Also prove the canonical translation square:

```lean
theorem execute_translates
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source request = .ok receipt) :
    ∃ sourceDiagram targetDiagram,
      source.translate = .ok sourceDiagram ∧
      receipt.target.translate = .ok targetDiagram ∧
      match orientation with
      | .forward => Rule.Step sourceDiagram targetDiagram
      | .backward => Rule.Step targetDiagram sourceDiagram
```

Family theorems may expose the existential target diagram needed by the
aggregate, but must state recursive relation conclusions rather than semantic
implication.  Use `represents_unique` and `Step.iso` to align alternate
representatives; do not re-prove rule semantics in refinement.

## Authority and naming constraints

- Orientation chooses the rule relation or its converse.  Do not add
  direction-named recursive rules or direction-named copies of relations.
- The recursive `Rule.Step` and `Rule.Soundness` dependency closures remain free
  of `Concrete`, `Refinement`, execution, receipt, trace, or compiler imports.
- Do not define or call a matcher, candidate enumerator, occurrence search, or
  executable inverse to diagram isomorphism.
- Do not retain operational proof ownership below `Rule.Soundness` once its
  consumer has moved to refinement.
- Do not add a direct concrete-to-semantics theorem.  Concrete correctness is
  refinement to the recursive relation.
- Use the current twelve constructor names and six relation names exactly.  Do
  not invent prefixes or replacement terminology.
- Lean only.  TypeScript is outside scope.

## Theorem-driven development

For each family:

1. Complete the family module's definitions and moved helper dependencies.
2. State the family successful-execution theorem with its proof as the only
   `sorry` in that dependency closure and compile RED.
3. Replace the owning `sorry` with a kernel-checked proof and compile GREEN.
4. Run a focused dependency and authority scan before committing that family.

After all six families are GREEN, run a separate RED/GREEN cycle for
`execute_sound`, then for `execute_translates`.

## Validation and delivery

- Strict compilation of all six family modules and `Refinement/Step.lean`.
- Direct signature checks for `execute_sound` and `execute_translates`.
- Exact audit that all twelve `Concrete.Step` constructors are covered once by
  the required six-family mapping.
- `lean --deps` and recursive source scans proving `Rule.Step` and
  `Rule.Soundness` remain independent of concrete/refinement modules.
- Repository scans for matchers, search, alternate execution authorities,
  proof holes, and project axioms.
- Full `lake build` and `git diff --check`.
- Write
  `.superpowers/sdd/2026-08-06-recursive-rewrite-authority/task-9-report.md`.
- Commit each completed family separately when practical, then the aggregate;
  return all commit hashes and exact validation evidence.
