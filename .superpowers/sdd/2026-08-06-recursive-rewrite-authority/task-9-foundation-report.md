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
