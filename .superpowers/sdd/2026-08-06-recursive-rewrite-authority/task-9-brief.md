# Task 9 brief: structural execution refinement

Base commit: `26b57d84`

## Outcome

Prove that each successful concrete execution realizes exactly one of the six
recursive rule relations. Task 9 is entirely syntactic: it may establish
compiler equations, carrier and boundary correspondences, recursive
isomorphisms, rule witnesses, representation transport, and execution
refinement, but it may not state or prove any result about models, denotation,
semantic implication, or rule soundness.

Before resuming family proofs, repair the dependency boundary introduced or
retained by earlier work. Preserve compliant structural proofs. Extract only
the structural declarations actually consumed by refinement, and eliminate
concrete-dependent semantic machinery instead of moving, renaming, wrapping,
re-exporting, or retaining it as a parallel authority.

## Required remediation

The following conditions must hold before the Task 9 aggregate is GREEN:

- `Concrete/**` contains no denotation API, model theorem, semantic simulation,
  operation-soundness theorem, or aggregate importing such material.
- `Refinement/**` contains no model, denotation, semantic implication,
  `Rule.Step.sound`, family soundness proof, or operational semantic tower.
- Mixed diagram modules are split as needed so the import closures used by
  Concrete and Refinement reach only structural syntax, renaming, contexts,
  reachability, algebra, and isomorphism declarations—not semantic modules.
- Structural facts currently owned by operational `Rule.Soundness` modules are
  moved into focused syntactic owners only when an active refinement proof uses
  them. Their semantic portions and operational soundness aggregates are not
  retained elsewhere.
- The pure six-family rule soundness owners and `Rule.Step.sound` remain in the
  Rule layer and remain independent of Concrete and Refinement.
- `Concrete.Error.DomainInvalid` is not an authority for later rejection
  correctness. Task 11 covers every executor error from exact-request
  completeness.

The active WireSever and WireJoin work may keep its checked execution inversions,
raw transformations, compiler naturality equations, finite equivalences,
boundary maps, recursive isomorphisms, and `Rule.WireSever` witnesses. Replace
imports from mixed operational soundness modules with focused structural owners.
Do not commit a wholesale relocation of an operational semantic module or a
reverse import from `Rule.Soundness` into Refinement.

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

Each family owns its structural successful-execution theorems at
`VisualProof/Refinement/Step/{Erasure,WireSever,Iteration,DoubleCut,Comprehension,Vacuity}.lean`.
The aggregate owner is `VisualProof/Refinement/Step.lean`.

For every constructor, start from its actual successful `Concrete.execute`
equation. Construct the assigned recursive relation or its converse at the
controlling context polarity, and construct the represented target. No family
proof may conclude a semantic implication or invoke a rule soundness theorem.

`Concrete.Insertion` carries `input.AttachmentsRespectBoundary`, ensuring
`boundRelationSpawn` is only the converse of `Erasure`. The authorized relation
shapes already use splice framing for Erasure, DoubleCut, Comprehension, and
Vacuity, and bind the Iteration anchor-local carrier once. Task 9 consumes those
relations structurally; it does not prove their semantic laws.

## Public theorems

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

`execute_translates` is derived only from `execute_sound`, checked-state
translation, representation uniqueness, and `Step.iso`. It does not invoke
`Step.sound`.

## Authority and naming constraints

- Concrete and Refinement are semantic-free in both direct source and recursive
  dependency closure.
- Rule relations and Rule soundness are independent of Concrete, Refinement,
  execution, receipts, compiler traces, and carrier numbering.
- Orientation chooses a relation or its converse. Do not add direction-named
  rule variants.
- Do not define or call a matcher, candidate enumerator, occurrence search, or
  executable inverse to diagram isomorphism.
- Do not add compatibility paths, transitional wrappers, alternate authorities,
  or names prefixed with `Direct`, `Directed`, `Abstract`, or `Recursive`.
- Lean only. TypeScript is outside scope.

## Theorem-driven development

1. First make the semantic-boundary remediation compile with no proof holes.
2. For each family, complete every structural definition in the theorem's
   dependency closure.
3. State the successful-execution theorem with its proof as the only `sorry` in
   that closure and compile RED.
4. Replace the owning `sorry` with a kernel-checked proof and compile GREEN.
5. Run the bidirectional dependency and authority scans before committing the
   family.
6. After all families are GREEN, run separate RED/GREEN cycles for
   `execute_sound` and `execute_translates`.

## Validation and delivery

- Strict compilation of every structural owner, all six family modules, and
  `Refinement/Step.lean`.
- Direct signature checks for `execute_sound` and `execute_translates`.
- Exact audit that the twelve `Concrete.Step` constructors are covered once by
  the fixed six-family mapping.
- Recursive dependency scans proving all Rule relations and soundness owners are
  independent of Concrete and Refinement.
- Direct source and recursive dependency scans proving Concrete and Refinement
  contain no model, denotation, semantic implication, semantic simulation,
  `Rule.Soundness`, `Rule.Step.sound`, or `Proof` declaration/import.
- Source checks proving no concrete semantic module, refinement semantic tower,
  operational soundness aggregate, matcher/search subsystem, compatibility
  authority, proof hole, or project axiom remains.
- Full `lake build` and `git diff --check`.
- Write
  `.superpowers/sdd/2026-08-06-recursive-rewrite-authority/task-9-report.md`.
- Commit the remediation before resuming family commits; then commit each
  completed family separately when practical and return exact validation
  evidence.
