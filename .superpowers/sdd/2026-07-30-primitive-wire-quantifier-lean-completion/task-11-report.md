# Task 11 Audit Report — Complete definitions, citation, and the exact 34-step checker

**Status:** DONE_WITH_CONCERNS

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
