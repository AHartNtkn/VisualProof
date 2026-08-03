# Task 11 Audit Report — Complete definitions, citation, and the exact 34-step checker

**Status:** BLOCKED

## Completed requirement evidence

| Requirement | Evidence |
| --- | --- |
| RED fixture for every tag, including exact tag and exhaustiveness coverage | `VisualProof/Rule/StepFixtures.lean` supplies fixtures; `StepTag` and `ProofStep.tag` enumerate the exact 34 tags. |
| Checked definition unfold/fold and soundness | `VisualProof/Rule/Definition.lean` provides `applyUnfold`, `applyFold`, `unfold_sound`, and `fold_sound`; completed in `0516d42`, with boundary-target retention in `e9727dd`. |
| Pinned prior-theorem application and soundness | `VisualProof/Rule/Theorem.lean` provides `applyTheorem` and `theorem_application_sound`; completed in `e078661`. |
| Exact checked 34-constructor sum | `VisualProof/Rule/Step.lean` defines `ProofStep` with 34 explicit constructors, `rawTarget`, `tag`, and `receipt`; the original exact-step work is `462faff` and final soundness integration is `71e4053`. |
| Step receipt and transport surfaces | `StepReceipt` exposes normalized result, allocation, transport, root interface, ordered boundary transport, and root-boundary transport in `VisualProof/Rule/Step.lean`; transport work begins at `471fc72`. |
| Exhaustive checker soundness | `VisualProof/Rule/Soundness.lean` defines `applyStep_sound` with explicit case analysis over `ProofStep`; final 34-step proof is `71e4053`. |
| Import integration and GREEN completion | `VisualProof.lean` imports the Task 11 modules; parent-session validation completed with full `lake build` and `npm run formal:size`. |

## Concern: public receipt fields are caller-controlled

`VisualProof/Rule/Step.lean` publicly defines `StepReceipt` with caller-supplied `provenance` and `rawTransport` fields (lines 311–315). Every one of the 34 public `ProofStep` constructors accepts such a receipt, `ProofStep.receipt` selects it, and `applyStep` returns it unchanged (lines 620–624). No equality or construction relation ties either field to the transport/provenance receipt owned by the corresponding primitive, structural, definition, or theorem application.

The fixtures explicitly demonstrate the unconstrained shape: `fixtureReceipt` supplies `WireProvenance.none` and `WireTransport.none` in `VisualProof/Rule/StepFixtures.lean` (lines 44–49). Thus a checker-accepted step can expose arbitrary transport/provenance rather than checker-owned transport. This violates Task 11's checker-owned receipt model and makes Task 12 boundary replay untrustworthy.

## Required repair scope before trusting replay

Replace caller-supplied `StepReceipt` transport/provenance with receipts constructed by, or definitionally/equality-linked to, each owning checked transition. Migrate all 34 `ProofStep` constructors and `ProofStep.receipt`/`applyStep` to that authority. Update fixture construction to assert real owner-derived transport and provenance; strengthen soundness and replay validation to verify ordered boundary and root-interface transport against those owner receipts. Remove the unconstrained construction path completely—no adapter, optional override, or fallback receipt may remain.

## Commits and validation

Relevant completed work: `471fc72` through `71e4053`; dependent replay work is `acbb107`.

Validation reported by the parent session: full `lake build` and `npm run formal:size` passed. No tests were run for this report-only task.

## Change scope

This audit created only this report. No repository source files were changed.

## Ownership repair attempt — BLOCKED

The requested owner-derived receipt repair stopped before any repository source
edit because one of the exact 34 owners does not retain the concrete carrier
needed to construct its receipt.

`StructuralCore.CheckedDoubleCut` in
`VisualProof/Rule/Structural.lean:676-686` stores only:

- `siteCompiled : SiteCompilation plain input.site`; and
- the intrinsic equality
  `elaborate doubled = siteCompiled.frame.context.fill (doubleCut
  siteCompiled.frame.siteBody)`.

Its public namespace exposes `plain`, `doubled`, the two tags, and closed
denotational equivalence. It exposes no construction-derived correspondence
between `plain.val.WireId` and `doubled.val.WireId`. Consequently neither
`doubleCutIntro` nor `doubleCutElim` can derive the required logical
`WireTransport` or injective, signature-preserving `WireProvenance` after the
unrestricted `StepReceipt` input is removed.

The precise missing owner interface is either:

```lean
CheckedDoubleCut.wireEquiv :
  Data.Finite.FiniteEquiv
    checked.plain.val.WireId checked.doubled.val.WireId

CheckedDoubleCut.wireEquiv_signature :
  ∀ wire,
    (checked.doubled.val.wires (checked.wireEquiv wire)).sig =
      (checked.plain.val.wires wire).sig
```

or equivalent forward/inverse directional images with mutual-inverse,
injectivity, and signature theorems. `checkDoubleCut` must derive and retain
this carrier from its concrete construction. It cannot be supplied by proof
input, recovered by isomorphism search, assumed to preserve dense indices, or
replaced by an all-`none` transport.

Per the repair contract, implementation stopped at this exact missing theorem
rather than leaving a partial 32/34 authority migration or manufacturing a
fallback. No Task 11 source was edited, no validation was rerun because no
behavior changed, and no commit was created. The two protected dirty files and
the untracked `VisualProof/Diagram/Concrete/OpenIsomorphism.lean` draft remain
untouched.

## Double-cut owner slice

**Status:** COMPLETE — the `CheckedDoubleCut` prerequisite is unblocked; the
broader 34-case checker-owned receipt migration remains outside this slice.

**Foundation record:**
`/tmp/vpa-task11-doublecut-owner-20260803-foundation.md`

**Changed files:**

- `VisualProof/Rule/Structural.lean`
- `VisualProof/Rule/StructuralFixtures.lean`

**Checker and API evidence:** `checkDoubleCut` now validates the intrinsic
double-cut target, equality of the plain/doubled dense wire counts, and exact
pointwise signature preservation under the stable positional `Fin` cast.
`CheckedDoubleCut` privately retains those checker-derived facts and exposes
only `wireEquiv`, `wireEquiv_injective`, `wireEquiv_signature`, and
`wireEquiv_symm_signature` for downstream receipt construction. The existing
semantic `equivalence`, `intro_sound`, and `elim_sound` proofs are unchanged.

**Fixture evidence:** the canonical double-cut endpoint remains accepted and
its owned equivalence is proved injective and signature-preserving. A second
well-formed target has the same intrinsic elaboration as the canonical doubled
diagram but swaps two concrete wire IDs carrying distinct signatures;
`checkDoubleCut` rejects it with `targetMismatch`, proving intrinsic equality
alone no longer admits a non-stable carrier.

**Validation:** `lake build VisualProof.Rule.Structural
VisualProof.Rule.StructuralFixtures`, `lake build
VisualProof.Rule.StepFixtures`, full `lake build` (193 jobs), `npm run
formal:size`, and `git diff --check` all passed. Existing lint warnings only.

**Commit:** `e2b2eae` (`fix: derive double-cut wire transport in checker`)

**Self-review:** the carrier is construction-stable (`finCast`), total,
bidirectional, injective, and signature-preserving; no caller evidence,
isomorphism search, compatibility wrapper, fallback, compiler-adequacy edit,
or change to the other 32 cases was introduced. The protected dirty files and
the preserved `OpenIsomorphism.lean` draft were not touched.
