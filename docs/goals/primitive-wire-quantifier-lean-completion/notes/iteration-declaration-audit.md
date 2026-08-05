# Iteration declaration audit: HO-selected architecture

## Decision

The single iteration predecessor is the completed abandoned signature-indexed
higher-order implementation in
`/tmp/vpa-current-lean-code-20260804-XO7NPu`. The exact terminal kernel is
`CheckedOrdinaryIteration.equivalence` and `.sound` in
`VisualProof/Rule/Structural.lean`. The operation and proof dependency chain it
consumes must be ported as one unit.

The second-order tree at `2bddfe4` is comparison evidence only for localized
current representation changes. Its selection/copy/compiler-route proof
architecture is not an iteration owner and must not be combined with the
selected HO chain.

## Selected terminal dependency chain

The completed HO theorem consumes these exact owners directly:

| HO owner | Terminal role | Current status |
|---|---|---|
| `CheckedExtraction` and its `compilation` | supplies the exact selected open occurrence | pending coherent port |
| `SiteCompilation` and `compileRelativeFrame?` / `RegionFrame` | factors the source at the selection site and the destination below it | pending coherent port |
| `ConcreteSpliceAttachment` | fixes ordered attachment of the extracted occurrence at anchor and destination | pending coherent port |
| `InsertionCompilation` and `compileInsertion?` | identifies the intrinsic insertion produced by the raw concrete splice | pending coherent port |
| `RawConcreteSpliceResult` and `spliceRaw` | owns the concrete iteration target | pending coherent port |
| `copyTruth`, `iterateInto`, `regionContained`, and their denotation theorems | proves local duplication equivalence | pending coherent port |
| `CheckedOrdinaryIteration.equivalence` / `.sound` | terminal all-model semantic result | RED at current production endpoint |

Definition/reference, macro, normalization, provenance, transport, and opaque
checker packaging that are not mathematical dependencies of this chain are
removed during the port. A required mathematical owner is not replaced merely
because its predecessor packaging is obsolete.

## Current mismatch

| Current declaration family | Evidence | Classification |
|---|---|---|
| `Subgraph/IterationSplice.lean`: `IterationSpliceDomains`, `iterationSpliceRaw`, and raw host/fragment tables | Direct specialization of HO `ConcreteSpliceAttachment.fragmentRegions`, `fragmentInternalWires`, host/fresh carrier maps, `diagram`, and `RawConcreteSpliceResult`: canonical extraction removes the fragment root, retains exactly selected regions/nodes/internal wires, and maps each extracted boundary class to its touching host wire | **L: renamed selected raw-splice owner; GREEN** |
| `Subgraph/IterationSplice.lean`: raw well-formedness and host-carrier equations | Same downstream responsibility as HO `spliceRaw_success_wellFormed`, `spliceRaw_success_checked`, and `ConcreteSpliceAttachment` host/fragment table equations | **L: retained proofs of the specialized HO raw result; GREEN** |
| `Rule/Structural/Iteration.applyIteration` through `iterationSplice` | Current public selection/destination specialization of the HO checked raw result; obsolete checker/receipt packaging is absent | **L: public wrapper over the selected raw-splice owner; GREEN** |
| `Subgraph/Extraction.lean`: canonical `extract`, its checked fragment, attachments, origin maps, and exactness laws | HO `CheckedExtraction`, `CheckedExtraction.openDiagram`, and the exact selection/boundary seam fields; current selection determines the occurrence pattern canonically and `CheckedOpenDiagram.elaborate` replaces the obsolete `OpenCompilation` receipt | **L: canonical specialization of selected extraction owner; GREEN** |
| `Elaboration/Context.lean`: `SiteFrame`, `compileRegionFrame?`, `compileRootFrame?`, and their generated/completeness laws | HO `RegionFrame`, `SiteCompilation`, `compileSite?`, and frame-fill equations; SO supplies the localized treatment of existential `Region.locals` | **L: selected site/relative-frame responsibility in current representation; GREEN** |
| former `Rule/Soundness/Iteration.lean` canonical-extraction and copied-fragment compiler-simulation hierarchy | independently proved the bespoke operation rather than porting the HO terminal dependency chain | **X: removed** |
| former `SelectionPartition.lean` and `ExtractionSelected.lean` | disconnected files intended to connect the current atlas to terminal semantics | **X: removed** |
| `Rule/Structural/Semantics.lean`: `conjoin`, `adjoinAt`, their denotation laws, `adjoinAt_contraction_sound`, and `Context.denote_adjoinAt_iff` | HO `Region.conjoin`, `iterateInto`, `denote_iterateInto`, and the contextual equivalence step used inline by `CheckedOrdinaryIteration.equivalence`; SO supplies only the region-local witness adaptation | **L: exact local semantic kernel; GREEN** |
| former `ancestorCopy_sound` and `ancestorAdjoin_sound` | no exact selected-HO declaration; generalized wrappers created for the displaced route proof | **X: removed** |

Canonical extraction makes the generic HO attachment boundary-coherent: equal
fragment boundary wires have the same host origin, so the predecessor's grouped
identity-request list is empty. This removes identity-request table cases from
the specialized raw construction; it does not introduce identity normalization.

No other current iteration declaration is reusable until a row records its
exact HO predecessor declaration, the localized representation edit, and the
precise downstream use in `CheckedOrdinaryIteration.equivalence` or `.sound`.

## Next exact owner

The next missing selected declaration is HO
`InsertionCompilation.generated_checked_denotes_inserted`. Its current form
must relate `iterationSplice` directly to the intrinsic insertion compiled from
the canonical extraction and current `SiteFrame`. Its proof must be the
localized port of the completed HO factorization/naturality closure; it must not
reference or recreate the deleted copied-fragment simulation atlas.

## Stop condition

If an exact selected HO declaration cannot be adapted through removal of
obsolete content and localized current-representation edits, stop before
constructing an alternative and record its old statement, required current
statement, and precise incompatible hypothesis or conclusion.
