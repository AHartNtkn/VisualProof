# Task 9 structural witness foundation validation

## Status

PASS for the committed foundation range `432d5708^..5a16b1d0`.

The canonical recursive isomorphism hierarchy is proof-relevant data:

- `RegionIso`, `ItemIso`, and `ItemSeqIso` are mutually inductive in `Type`;
- `DiagramContextIso` is inductive in `Type`;
- `Region.ContextPath.Alignment` contains the relation-context equality, exact
  hole-wire equivalence, and direct `DiagramContextIso`;
- `RegionIso.ContextPathAlignment` contains that neutral alignment and its
  direct body `RegionIso`;
- `RegionIso.alignContextPath` constructs the indexed target path, context
  alignment, and body witness directly from the source path and recursive
  isomorphism; and
- `OpenDiagramIso.body` is a direct `RegionIso`, while theorem-facing
  `Core.Isomorphic` and `OpenDiagram.Isomorphic` are `Nonempty` wrappers.

The four canonical Diagram owners contain no `Classical.choice`,
`Classical.choose`, `Exists.choose`, or `Nonempty.some` recovery. The
foundation diff adds none of those operations.

The removed `RegionIsoPresentation`, `SourceFactorPresentation`, and
`PairedCompilerContextAlignment` names are absent. The generic and
family-specific compiler-alignment structures redeclare none of
`holeRelsEq`, `holeWire`, `contexts`, or a parallel `context` field.

## Validation

- A serial warnings-as-errors sweep compiled all 63 production owners changed
  by the foundation range:

  ```text
  LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true <owner>
  STRICT GREEN OWNERS: 63/63
  ```

- The four authority audits passed:

  ```text
  scripts/audit-lean-authority.sh rules
  rules: clean recursive source-import closure across 14 root(s)

  scripts/audit-lean-authority.sh implementation
  implementation: clean recursive source-import closure across 5 root(s)

  scripts/audit-lean-authority.sh proof
  proof: clean recursive source-import closure across 3 root(s)

  scripts/audit-lean-authority.sh roster
  roster: exact five-family Rule.Step and ten-constructor Concrete.Step roster;
  standalone Comprehension only
  ```

- The tracked-production scan found no `sorry`, `admit`, or project `axiom`
  declaration. `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true
  VisualProof/Audit.lean` reported only the accepted kernel foundations
  `propext`, `Quot.sound`, and `Classical.choice`.
- Concrete and Refinement contain no imports of semantic, soundness, or Proof
  owners. The foundation range adds no compatibility/alias marker and its
  changed production owners contain no `example`, `#check`, or `#eval`.
- The final serial full build passed:

  ```text
  LEAN_NUM_THREADS=1 lake build
  Build completed successfully (142 jobs).
  ```

## Validation repair

The first full build exposed one missed theorem-facing boundary in
`VisualProof/Rule/Soundness/WireSever.lean:96`: `iso_denotation` expects
`Core.Isomorphic`, while the revised rule stores the direct `RegionIso` in
`step.body`. The call now supplies `⟨step.body⟩`. The owner then passed a
serial warnings-as-errors compile, and the full repository build passed on
the next run.

No Task 9 theorem was resumed. The untracked `Deiteration.lean` and
`IterationRootSourceFactor.lean` files were neither edited nor staged.

## Root source certificate local-map repair

The tracked root source-factor owner now retains the canonical local carrier
map that its direct `OpenDiagramIso` construction already uses. The public
endpoint lemmas identify the arity-cast source body with the checked hidden
wires and the arity-cast target body with the retained-hidden plus selected-
explicit block. `Certificate.source_local` states that
`source_iso.body.localEquivCast` at those endpoints is exactly
`(rootLocalEquiv source.checked selection anchorRoot boundaryDisjoint).symm`.

`complete` constructs the equality alongside its existing proof-relevant body
isomorphism, starting from the explicit `regionIso_of_cast` local equivalence,
then transporting it once across the body endpoints and once across the final
open-diagram arity/`withBody` endpoint. No downstream unfolding, presentation,
choice recovery, compatibility layer, or second certificate was added.

Validation passed:

```text
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true -DmaxHeartbeats=4000000 \
  VisualProof/Refinement/Implementation/IterationRootSourceFactor.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true \
  VisualProof/Refinement/Implementation/IterationSourceFactor.lean
LEAN_NUM_THREADS=1 lake build \
  VisualProof.Refinement.Implementation.IterationRootSourceFactor \
  VisualProof.Refinement.Implementation.IterationSourceFactor

scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh proof
scripts/audit-lean-authority.sh roster
```

Both strict owners and the focused 67-job serial build passed. All four
authority audits passed. The tracked-production hole/axiom scan was empty;
`VisualProof/Audit.lean` reported only the accepted kernel foundations
`propext`, `Quot.sound`, and `Classical.choice`. The repair diff adds no
`Classical.choice`/`choose`, semantic import, compatibility or alias marker,
`example`, `#check`, or `#eval`. The dependent SourceFactor owner retains two
pre-existing `indexOf?_complete` choice calls; neither is changed or consumed
by this certificate repair.

The untracked `IterationBase.lean` and `Deiteration.lean` owners remained
unstaged throughout this repair.
