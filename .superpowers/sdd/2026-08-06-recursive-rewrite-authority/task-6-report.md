# Task 6 report: concrete rewrite execution

## Outcome

The flat checked representation and operational execution surface now live
under `VisualProof.Concrete`. All Lean importers and the step-tag executable
target use the Concrete module paths in one atomic buildable migration.

The public executor is indexed by ordered boundary arity:

- `Concrete.State arity` owns a checked open diagram and its boundary-length
  equality.
- supplied deiteration and comprehension evidence is directly indexed by the
  source `State`, including abstraction occurrences and witnesses;
- `Concrete.Step source` has exactly the twelve required constructors;
- `Concrete.Insertion` accepts a complete admissible splice input;
- `Concrete.BoundaryTransport` records an image for each boundary position;
- `Concrete.Receipt source` returns the target state, wire provenance, and
  position-aware boundary transport;
- `Concrete.execute` consumes the supplied certificates and does not perform
  occurrence discovery;
- generalized insertion checks `spawnPolarity` from the requested orientation
  and concrete insertion-site cut depth, returning `wrongPolarity` on failure.

Wire severing has an operation-specific completion path. For each source
boundary position denoting the severed wire, `WireSeverBoundary.side` selects
the retained or fresh target wire. Other positions are preserved, with
`WireSeverBoundary.other` supplying the canonical irrelevant branch. The
resulting checked-open target and receipt use that positional image.

Concrete execution has no operation-tag semantic classification. Existing
per-operation proof towers compile against Concrete operation modules and
state direct orientation-specific implications or operation-specific
equivalences over their raw evidence; their later refinement-layer relocation
remains outside this task.

Proof replay is indexed directly by `Concrete.State` and `Concrete.Step`, and
every transition calls `Concrete.execute`. The replay, theorem, and theory
certificate layers contain no parallel dispatcher and make no independent
semantic claims; semantic rule interpretation belongs to refinement.

## Module migration

- Core/open/well-formed diagrams: `VisualProof/Concrete/{Diagram,Open,WellFormed}.lean`
- Elaboration/compiler/simulation: `VisualProof/Concrete/Elaboration/**`
- Selection/extraction/splice/reassembly: `VisualProof/Concrete/Subgraph/**`
- Isomorphism and occurrence evidence: `VisualProof/Concrete/{Isomorphism,Occurrence}.lean`
- Operational rules: `VisualProof/Concrete/Operation/**`
- State, transport, requests, receipts, and execution:
  `VisualProof/Concrete/{State,Transport,Step}.lean`
- Step-tag executable: `VisualProof.Concrete.StepTagsMain`

## Proof development

Definition dependencies for the indexed executor and positional wire-sever
result were completed first. The wire-sever boundary root-scope obligation was
then checked at its owning theorem declaration and completed with a
kernel-checked proof. No proof holes or project axioms remain.

## Validation

- `lake build VisualProof.Concrete VisualProof.Concrete.State VisualProof.Concrete.Transport VisualProof.Concrete.Step VisualProof.Concrete.Operation.Structural VisualProof.Concrete.Operation.Comprehension VisualProof.Concrete.StepTags VisualProof.Concrete.StepTagsMain VisualProof.Audit` — passed (290 jobs).
- Focused builds for `VisualProof.Concrete.Step`, every retained
  operation-soundness aggregate, `VisualProof.Proof.{Replay,Theorem,Theory}`,
  and `VisualProof.Audit` — passed.
- `lake build` — passed (289 jobs).
- `lake exe visualproof_step_tags` — passed and emitted the twelve expected
  tags in constructor order.
- Source scans found no old concrete/rule/step-tag import paths, occurrence
  discovery declarations or language, obsolete declaration aliases, concrete
  operation semantic classifiers, parallel raw operation step/dispatch/replay
  declarations, `sorry`, `admit`, or project/local axioms.
- The `Concrete.Step` constructor scan counted exactly twelve constructors.
- `git diff --check` — passed.

## Scope

Changes are limited to Lean sources, `lakefile.toml`, and this task report.
TypeScript is unchanged.

## Concerns

None.
