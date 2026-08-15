# Task 4A report — primitive vacuity

## Status

Implementation is GREEN and awaiting independent review before commit.

## Implemented boundary

- `point` adds or removes one arity-zero identity at the suffix of the selected
  region's item sequence.
- `pin` adds or removes one unary identity at the suffix of the selected region's
  item sequence. Removal carries only `Pin.DeletionGuard`, which states the
  selected surviving wire's exact local/ancestor DCA and external two-end
  obligations.
- `stub` adds one fresh typed host-local wire as a suffix, inserts one fresh port
  at an exact source-indexed position of the selected identity while retaining
  all other ports in order, and adds one unary far point at the suffix of an
  exactly selected region at or below the base.
- `Vacuity.Local` contains exactly these three constructors. The global rule is
  `Contextual (symmetric Vacuity.Local)` and retains both endpoint-isomorphism
  closure directions and symmetry.

## Endpoint validity

- Point validity follows from unchanged incidence paths and unchanged child
  canonicality.
- Pin insertion is monotone. Pin removal derives the complete target validity
  from the selected-wire deletion guard while proving every other wire's
  incidence paths unchanged.
- Stub validity uses one ambient-extension proof kernel in
  `VisualProof/Diagram/Scope/Rename.lean`. Its public surface is exactly:
  - old-wire incidence paths under `Region.adjoinHostWire`;
  - `ItemSeq.ChildrenCanonical` iff under `Region.adjoinHostWire`;
  - `Region.Canonical` iff under `Region.adjoinHostWire`.
- The fresh Stub wire receives one root incidence at the selected identity and
  exactly one far incidence, establishing `RootedTwo`. Old host wires preserve
  their incidence paths, DCA, child canonicality, and external two-end floor.

## Surviving-wire scope

- `DiagramContext.mapInternalWire` maps every internal wire of a filled source
  context through a total hole-wire map; `ownerPath_mapInternalWire` proves that
  its owner path is preserved.
- `Vacuity.Local.existsInternalWire_ownerPath` proves that every internal wire in
  the retained endpoint has a counterpart in the endpoint containing the new
  identity syntax with the same owner path.
- `Vacuity.Local.existsPresentedWire_scopePath` lifts that result through the
  exact Contextual presentation and covers every source `OpenDiagram.Wire`.
  External wires map identically; internal wires retain their exact numeric scope
  path. The theorem deliberately does not claim literal path equality across
  arbitrary endpoint isomorphisms.

## Executable and coverage

- `ForwardIndex` has exactly six source-indexed constructors: introduce/eliminate
  for point, stub, and pin.
- `BackwardIndex` is a `def` with the same direct index authority.
- No index stores a target diagram or rule witness.
- Point, Stub, and Pin insertion and Point/Stub removal store no generic target
  validity evidence.
- Pin removal stores only `Pin.DeletionGuard`.
- `Pin.DeletionGuard.ofValidity` extracts that guard from the exact Contextual
  target endpoint witness during relation-to-runner coverage.
- `forward_exact` and `backward_exact` are kernel checked.

## Soundness

- Point is conjunction with a true nullary identity.
- Pin is conjunction with a reflexive unary identity.
- Stub eliminates one fresh existential value. For positive arity the value is
  selected from an existing identity port; for zero arity it uses the model's
  inhabited carrier (or the canonical false relation at higher-order signature).
  The far unary identity is reflexive, and the proof follows the exact recursive
  `Stub.Far` evidence.
- `Vacuity.Local.sound_iff` and `Vacuity.sound` are kernel checked.

## Ownership and size

| File | Total LOC | Net change |
|---|---:|---:|
| `VisualProof/Diagram/Scope/Context.lean` | 214 | +103 |
| `VisualProof/Diagram/Scope/Rename.lean` | 285 | +285 |
| `VisualProof/Rule/Vacuity.lean` | 1462 | +1380 |
| `VisualProof/Rule/Executable/Vacuity.lean` | 216 | +57 |
| `VisualProof/Rule/Soundness/Vacuity.lean` | 411 | +356 |
| **Total** | **2588** | **+2181** |

All structural proof helpers are private. Public declarations are limited to the
ambient-extension projections, primitive endpoint data, deletion guard and
validity boundary, the two generic context declarations, the two
surviving-scope existence theorems, relation laws, direct runner API, exactness,
and soundness.

## Validation

Passed:

- `lake env lean -DwarningAsError=true VisualProof/Diagram/Scope/Rename.lean`
- `lake env lean -DwarningAsError=true VisualProof/Diagram/Scope/Context.lean`
- `lake env lean -DwarningAsError=true VisualProof/Rule/Vacuity.lean`
- `lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Vacuity.lean`
- `lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Vacuity.lean`
- `lake build VisualProof.Rule.Executable.Vacuity VisualProof.Rule.Soundness.Vacuity`
- `scripts/audit-lean-authority.sh implementation`
- `scripts/audit-lean-authority.sh rules`
- `scripts/audit-lean-authority.sh roster`
- `scripts/audit-lean-authority.sh documentation`
- admission, `HEq`/cast API, raised-limit, component/assembly/search/normalization,
  and displaced-model scans over all five owned Lean files
- `git diff --check`

The repository-wide build reaches the current integration frontier: the Task 4A
modules build, while `VisualProof/Rule/Step.lean` still expects its planned typed
Vacuity integration and `VisualProof/Rule/Comprehension/Relation.lean` remains the
planned Task 5 owner.

## Architecture assessment

The implementation has one recursive syntax authority, one existing
`DiagramContext` navigation authority, one direct `Stub.Far` descendant witness,
one ambient-extension proof kernel, and one private operation-specific internal
wire embedding proof. It contains no assembly/component model, target search or
data, generic endpoint-validity fields, normalization/rehoming, parallel
relation, `HEq`, cast API, or raised elaboration limits.
