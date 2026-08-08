# Task 9 Iteration base report

## Status

BLOCKED before the owning `baseOfSplice` RED declaration pending an
architecture decision about root-scoped selected boundary wires. The current
concrete operation admits a case that the current `Rule.Iteration.Base`
relation cannot represent.

The structural dependency requested by the previous report is complete and
kernel checked in `IterationSourceFactor.lean` at `804769a2`.
`SourceFactorResult` now supplies the route-indexed descendant and remainder,
the ordinary source factor isomorphism, and the extracted-material
isomorphism with selected explicit wires represented as locals.

## Exact root counterexample shape

Consider a checked ordered-open source with:

- a wire `w` scoped at the concrete root and occurring in the ordered
  boundary;
- one or more root-owned nodes incident to `w`;
- a selection anchored at the root, containing those nodes directly and
  listing `w` in `explicitWires`;
- no selected child region containing the root; and
- iteration targeted at the root.

This is permitted by the current predicates:

- `SelectionRequest.Valid.explicitWires_at_anchor` requires only that `w` is
  scoped at the selection anchor;
- `explicitWireEndpoints_selected` requires its endpoints to be selected;
- `SelectsRegion root` is false when the selected child roots are proper
  children, so the executor's target-nonselection check accepts the root;
- `CheckedSelection.touchingWires` excludes `w` because `SelectsWire w` holds
  through explicit selection;
- `iterationInput` attaches only `touchingWires`, so `w` is internal to the
  extracted pattern rather than an attachment; and
- `Splice.Input.Admissible` imposes attachment visibility and binder-target
  conditions but no disjointness between `explicitWires` and the ordered
  boundary. With no touching wires or binder proxies, those obligations are
  vacuous, and `spliceChecked_complete` supplies a successful splice.

The successful root splice retains the frame wire `w` as the source boundary
wire and creates a fresh hidden copy for the pattern-internal `w`.

`Rule.Iteration.Base` cannot express that transition. Its one `selected`
region is used at both endpoints. A selected local wire is rebound by the
copied region and therefore becomes fresh, while a selected outer wire is
transported through `descendant.outerWire` and therefore remains attached.
For `w`:

- classifying it as local gives the required fresh target copy, but makes the
  source presentation non-isomorphic to the ordered-open source, where `w` is
  an external boundary class; and
- classifying it as outer makes the source presentation possible, but the
  abstract target shares `w` instead of creating the executable splice's
  fresh hidden wire.

This is not a missing compiler transport lemma. The two endpoints have
different binder/interface structure, so the required `OpenDiagramIso` does
not exist.

## Candidate repairs

### 1. Reject the unsupported concrete request

Add an iteration legality condition for a root anchor requiring

```lean
Disjoint selection.val.explicitWires source.val.exposedWires
```

equivalently disjointness from `source.val.boundary`. Enforce it in concrete
execution before splice and expose it in successful-operation inversion.
Then every selected explicit root wire can soundly be represented as a local
of `Rule.Iteration.Base`, and the existing `SourceFactorResult` is the correct
factorization authority.

This is the smaller repair, but it narrows the set of accepted concrete
iteration requests.

### 2. Attach selected root boundary wires instead of freshening them

Retain the request but change root iteration extraction/splice so a selected
explicit wire that is also an ordered boundary class is part of the pattern
interface and is attached back to the frame wire. The root source factor must
then split selected explicit wires into:

- exposed selected wires, represented as outer wires of `selected`; and
- nonexposed selected wires, represented as locals of `selected`.

The existing `Rule.Iteration.Base` copy then shares the exposed wires through
`descendant.outerWire` and freshens only the nonexposed locals. This preserves
the ordered interface and accepts the current request shape, but it changes
the concrete root splice result and requires a root-specific source-factor
certificate.

## Safe boundary

No `baseOfSplice` theorem or helper was stated with `sorry`. No rule,
concrete-legality, execution, or compiler definition was changed. The only
task-owned change for this checkpoint is this report.

## Material-local witness repair

While assembling the operation-independent root splice bridge, the direct
`SourceFactorResult.material_iso` witness was found to erase the exact local
equivalence used by its constructor.  The endpoint isomorphism alone does not
determine that map, so recovering it by unfolding `sourceFactor_complete`
would have made the base proof depend on an opaque implementation term.

`SourceFactorResult` now retains the canonical equality
`material_local`: after transport across the named extracted-material and
adjoined-material local-count equalities, `material_iso.localEquivCast` is
exactly `(anchorLocalEquiv input.val selection).symm`.  The result uses the
existing `route_alignment.retainedLength` as the sole authority for
`anchorLocal = retainedAnchorWires.length`.  `sourceFactor_complete` constructs
a direct `rawMaterialIso`, transports it to the public `Region.adjoinAt`
endpoint, and proves `material_local` with
`RegionIso.localEquivCast_castEndpoints`; no presentation, wrapper, choice, or
second carrier map was introduced.

Validation for this focused repair:

- strict warning-as-error compilation of `IterationSourceFactor.lean` and
  `IterationRootSourceFactor.lean` passed;
- `lake build VisualProof.Refinement.Implementation.IterationSourceFactor`
  passed;
- authority audits `rules`, `implementation`, `proof`, and `roster` passed;
- changed-line scans found no hole, axiom, structural choice recovery,
  semantic import, compatibility alias, or example directive; and
- `git diff --check` passed.
