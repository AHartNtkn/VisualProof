# Task 7 diagram-algebra extraction report

## Outcome

The live generic region-algebra operations and isomorphisms used by the
comprehension compiler now have one owner in the Diagram layer. Every live
Compiler and WireSever caller was migrated directly; no alias, re-export, or
completeness-owned wrapper remains.

The extraction preserves the existing `Region`, `ItemSeq`, and `RegionIso`
representation. It introduces no alternate syntax, validity authority,
occurrence authority, rule evidence, executor, or decidability layer.

## Ownership

`VisualProof/Diagram/Isomorphism.lean` now owns the constructors and
eliminators that depend only on `RegionIso` and `WireEquiv`:

- `RegionIso.ofEq`
- `RegionIso.localEquiv`
- `RegionIso.itemSeqIso`
- `WireEquiv.refl_append_left_index_val`

`VisualProof/Diagram/Algebra.lean` now owns the shared operation
`Region.extendHostItems`.

`VisualProof/Diagram/Isomorphism/Algebra.lean` imports exactly
`VisualProof.Diagram.Algebra` and owns the operation-dependent laws:

- `Region.renameWires_conjoin`
- `RegionIso.renameWiresConjoin`
- `RegionIso.renameWiresComp`
- `WireEquiv.adjoinMaterialAssoc`
- `RegionIso.adjoinAt`
- `RegionIso.adjoinAtAssoc`
- `RegionIso.adjoinAtConjoinLeft`
- `RegionIso.conjoinComm`
- `Region.appendAdjoinedHostSuffix`
- `RegionIso.adjoinAtMoveHostSuffix`
- `Region.renameWires_adjoinAt_nil`
- `RegionIso.renameWiresAdjoinAtNil`
- `Region.singleton_renameWires`
- `RegionIso.adjoinAtSingleton`

The unused nil-adjoin presentation and its support equality have no successor.
Comprehension-specific endpoint, occurrence, validity, and generated-pin laws
remain local to the compiler.

## Commits

- `12988a4d` — hoist rename and conjoin diagram isomorphisms
- `e6f7a471` — centralize core region-isomorphism eliminators and migrate
  WireSever
- `16033910` — hoist the generic adjoin operation, lift, and reassociation laws
- `025c98b2` — hoist conjunction commutativity, host-suffix movement,
  nil-renaming, and singleton laws

Each dependency slice elaborated the owning module and focused Compiler client
before commit. The WireSever slice also elaborated its focused client.

## Directed-rule tripwire

The extraction changes only pure region operations, presentation witnesses,
and caller names. The production diff from `53542a49` adds no `Step.*`
application.

`atomSiteExposurePinnedWithHost` still reaches steps only through
`EqualityNormalization.pinAllTwiceRegionOfNonempty` and
`Erasure.Exposure.equates`. The former uses symmetric Vacuity steps; the latter
uses symmetric Vacuity and the symmetric local Identification branch. No
directed wire primitive is applied beneath the retained host.

## Validation

The following checks pass at `025c98b2`:

- `lake build VisualProof.Diagram.Isomorphism`
- `lake build VisualProof.Diagram.Algebra`
- `lake build VisualProof.Diagram.Isomorphism.Algebra`
- `lake env lean VisualProof/Rule/Executable/WireSever.lean`
- `lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean`
- full `lake build`: 77 jobs successful
- `git diff 53542a49..HEAD --check`
- repository-wide `sorry` / `admit` / axiom scan: no matches
- new-module import-boundary scan for Rule, Completeness, Canonical,
  Occurrence, Step, Instantiation, and StrictEquates: no matches
- changed-line scan for `Eq.rec`, unsafe casts, executors, runners,
  validators, `Decidable`, and `Step.*`: no matches
- displaced local-name scan: no old generic helper authority remains

The current repository has no authority-audit script entry, so the import,
hole, prohibited-construction, and displaced-authority checks above were run
directly against the authoritative production sources.
