# Task 4D report — accepted assembly decomposition and typed `Step`

Status: DONE

Baseline: `9dd04e07d214da6368122fd201e83e862d12e4e6`

Typed `Step` commit: `8aa5fbb087d4ce5d547866e0a55b1d691bc9c212`

## Final theorem boundary

`VisualProof/Rule/VacuousAssembly.lean` owns a proof-only generic assembly
relation.  Its external context and ordered boundary are fixed: insertion adds
no boundary entry.  Acceptance is proof-irrelevant while retaining the
dependent trace witness as erased data:

```lean
def AcceptedVacuousAssembly
    (source insertion : OpenDiagram boundary) : Prop :=
  Nonempty (Σ growth : OpenAddition source insertion,
    AbsorptionTrace source growth)
```

The derived primitive language is exactly vacuity, presentation, and
identification.  Lean 4.30 core provides `Relation.TransGen`, so the
reflexive-transitive conclusion uses equality for the empty case and
`TransGen` for the nonempty case without defining another closure authority:

```lean
theorem AcceptedVacuousAssembly.decompose
    {boundary : List Sig}
    {source insertion : OpenDiagram boundary}
    (accepted : AcceptedVacuousAssembly source insertion) :
    ∃ endpoint : OpenDiagram boundary,
      (source = endpoint ∨
        Relation.TransGen Primitive source endpoint) ∧
      OpenDiagram.Isomorphic endpoint insertion
```

The proof is induction over the accepting fixpoint trace read backwards.
`empty` is equality; `bare` expands one coarse component into point, stub, and
its finite extra-pin chain; `equated` constructs one identification exposure;
and `present` constructs one presentation replacement.  Namespace-local
lemmas prepend and concatenate the standard `TransGen` evidence.

## Proof-only assembly model

- `WireEmbedding` and `WireExtension` relate existing typed wire contexts.
  The retained map is injective and every target wire has a partial source
  origin; bare complement wires have no origin and equated complement wires
  name their retained origin.
- `RegionAddition` / `ItemSeqAddition` relate the existing recursive
  `Region` / `Item` / `ItemSeq` syntax.  Retained atoms reuse
  `Item.PortPartition`; retained identities reuse
  `Identification.PortExpansion` through `IdentityExpansion`.
- `IdentityExpansion` counts actual target positions.  Its complement evidence
  covers every added port position, so auxiliary data cannot create phantom
  complement size.
- `OpenAddition` relates source and current endpoints over one shared external
  context.  It owns the structural complement measure used by the trace.
- `RawContext` stores exact syntax occurrence and target validity but no rule
  relation witness.  Conversion functions construct the primitive contextual
  relations.

## Acceptance transitions

`RawBare` has four coarse component cases:

- `isolated`: one nullary point;
- `freshStub`: one base point, one zero-arity stub, and finite extra unary ends;
- `attachedStub`: one selected existing identity attachment and finite extra
  unary ends;
- `pinBatch`: a nonempty finite unary-end batch on an existing visible wire.

`ExtraPins` stores only `Vacuity.Stub.Far` home/visibility topology and the
successive erased target-validity facts.  Descendant pin occurrences are
derived by composing the actual `DiagramContext` paths.  The coarser bare
constructors therefore do not carry a list or closure of primitive rule
witnesses.

`RawEquated` stores the active identification syntax, typed port partition,
nonempty non-identity transfer, and applicability data.  Its conversion builds
the `Identification` evidence.

Residual physical identity-node and port arrangement is represented by an
explicit `RawPresentation` transition.  It stores exact source/target
configurations and `Presentation.Applicability`, not a `Presentation` relation
witness.  This permits multiple region-local bookkeeping transitions for a
cross-region component.

`AbsorptionTrace` has exactly `empty`, `bare`, `equated`, and `present`.
Bare/equated reconstruction strictly increases `OpenAddition.complementSize`;
presentation preserves it.

## Typed `Step`

`VisualProof/Rule/Step.lean`:

- indexes `Step` by `{boundary : List Sig}` and `OpenDiagram boundary`;
- imports `Presentation` and `Identification`;
- exposes exactly seven distinct constructors: `erasure`, `wireSever`,
  `iteration`, `doubleCut`, `vacuity`, `presentation`, and `identification`;
- dispatches `Step.iso` directly to all seven family isomorphism closures.

Aggregate soundness, executable, computability, and audit owners remain outside
this checkpoint.

## Theorem-driven evidence

The structural addition layer, raw endpoint layer, coarse bare topology, and
trace conversions were strict-green before the owning theorem was stated.

RED: `AcceptedVacuousAssembly.decompose` elaborated with `sorry` as the only
admission in its dependency closure.

GREEN: the admission was replaced by the kernel-checked trace conversion and
the existing reflexive open-diagram isomorphism.

## Validation

- `lake env lean -DwarningAsError=true VisualProof/Rule/VacuousAssembly.lean`
  — passed.
- `lake build VisualProof.Rule.VacuousAssembly` — passed, 20 jobs.
- `lake build VisualProof.Rule.Step` — passed, 26 jobs.
- `scripts/audit-lean-authority.sh rules` — clean recursive authority closure.
- Changed-owner scan for admissions, custom axioms, `HEq`, casts,
  `Classical.choose`, and raised limits — no matches.
- `git diff --check` — passed.

## Self-review

The assembly layer is proof-only and does not enter `Rule`, `Step`, runners,
executable indices, or recursive diagram syntax.  Primitive conversions are
derived from raw syntax/navigation and erased validity rather than stored
primitive relation evidence.  Presentation bookkeeping is explicit and
measure-preserving, while every complement-producing trace transition is
strictly measured.  No admission remains.

## Concerns

None.
