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

## Receipt migration resume — BLOCKED on normalization provenance

The double-cut prerequisite from `e2b2eae` was verified at current HEAD, but
the resumed all-34 receipt migration reached the next owner prerequisite before
any repository source edit.

`ConcreteDiagram.IdentityRewrite` in
`VisualProof/Diagram/Concrete/IdentityNormalization.lean:43-59` stores the
exact rewrite kind and target plus only one wire action:

- total `wireImage : source.val.WireId → target.val.WireId`; and
- its signature-preservation theorem.

`IdentityNormalizationTrace.wireImage` and
`IdentityNormalization.wireImage` (`IdentityNormalization.lean:247-303`)
compose and expose only that logical action. No partial external-identity image
or injectivity theorem exists.

This is materially insufficient in the collapse branch.
`collapseWireTransport` in
`VisualProof/Diagram/Concrete/IdentityNormalizationTransport.lean:162-181`
maps every absorbed incident wire to `eligible.survivor`. The logical action is
therefore intentionally coalescing and cannot be used as the injective external
provenance composed after a raw proof step.

The precise missing normalization-owner interface is:

```lean
IdentityRewrite.externalImage? :
  source.val.WireId → Option rewrite.target.val.WireId

IdentityRewrite.externalImage_injective :
  ∀ {left right mapped},
    rewrite.externalImage? left = some mapped →
    rewrite.externalImage? right = some mapped →
    left = right

IdentityRewrite.externalImage_signature :
  ∀ {wire mapped},
    rewrite.externalImage? wire = some mapped →
    (rewrite.target.val.wires mapped).sig = (source.val.wires wire).sig
```

with corresponding composition and laws on `IdentityNormalizationTrace` and
`IdentityNormalization`. The owner semantics must be construction-derived:

- drop and fusion retain every source wire through their exact positional
  carrier;
- collapse retains the designated `eligible.survivor` and every wire outside
  `eligible.second :: eligible.rest`; and
- each absorbed collapse wire maps to `none` in external provenance even
  though logical `wireImage` maps it to the survivor.

Until this distinction exists, sealing `StepReceipt` would require either
using a coalescing logical map as provenance or inventing an all-`none`, search,
or caller-supplied fallback. All are prohibited by the controlling contract.
The migration therefore stopped without partial constructor changes.

No repository source was edited, no validation was rerun because behavior did
not change, and no commit was created. The two protected dirty files and the
untracked `VisualProof/Diagram/Concrete/OpenIsomorphism.lean` draft remain
untouched. Foundation evidence:
`/tmp/task-11-receipt-migration-foundation-20260803.md`.

## Normalization external provenance slice

**Status:** COMPLETE — eager identity normalization now owns an injective,
signature-preserving partial external identity map independently of its total
logical wire image.

**Foundation record:**
`/tmp/vpa-task11-normalization-provenance-foundation-20260803.md`

**API and ownership:** `IdentityRewrite` construction is sealed and exposes
`externalImage?`, `externalImage_injective`, and
`externalImage_signature`. Drop and fusion derive total external images from
their stable dense positions. Collapse derives its partial image from the
canonical `retainedWires` index: the survivor and all nonabsorbed source wires
remain, while every member of `eligible.second :: eligible.rest` maps to
`none`; the unchanged logical `wireImage` still coalesces absorbed wires at the
survivor. `IdentityNormalizationTrace` composes the partial maps with
`Option.bind` and proves injectivity and signature preservation; the final
`IdentityNormalization` exposes the same map and laws without importing the
higher-level Step module.

**Fixture evidence:**
`VisualProof/Diagram/Concrete/IdentityNormalizationFixtures.lean` proves drop
and fusion totality, exact positional images, collapse survivor/nonabsorbed
retention, absorbed rejection alongside the distinct logical coalescing image,
per-rewrite injectivity/signature preservation, and a two-step eager
drop-then-collapse composition with final injectivity and signatures.

**Validation:** `lake build
VisualProof.Diagram.Concrete.IdentityNormalizationSemantics
VisualProof.Diagram.Concrete.IdentityNormalizationFixtures
VisualProof.Rule.StepFixtures`, full `lake build` (194 jobs), `npm run
formal:size`, the focused `tests/architecture/lean-semantics.test.ts` closure
gate (3 tests), and `git diff --check` all passed. The compiler adequacy import
closure remains normalization-free.

**Commit:** `fac8e7d` (`feat: track normalization external provenance`)

**Self-review:** logical normalization semantics and their total `wireImage`
were not changed. External provenance is construction-derived rather than
caller-supplied; collapse never maps an absorbed distinct identity to its
survivor, while repeated uses of one surviving source identity remain
representable by consumers. No Step dependency, graph search, parallel graph
model, fallback, compiler-adequacy edit, protected-file edit, or modification
of the preserved `OpenIsomorphism.lean` draft was introduced.

## Receipt migration resume — BLOCKED on structural insertion carrier laws

The normalization prerequisite from `fac8e7d` was verified at current HEAD.
The restarted constructor-order audit then stopped at the first exact
`ProofStep` constructor, `refSpawn`, before any Lean source edit.

`WirePrimitive.CompiledPrimitiveStep.refSpawn` retains a checked
`StructuralInsertionReceipt`. That receipt correctly owns the concrete splice
and exposes the exact source-to-raw-target carrier:

```lean
StructuralInsertionReceipt.rawHostWire :
  base.val.WireId -> checked.target.val.WireId
```

However, its public API exposes no injectivity or signature-preservation law
for that carrier. `Structural.lean:268-281` exposes only the corresponding node
injectivity theorem. The necessary evidence exists below the private receipt
boundary as:

```lean
ConcreteSpliceAttachment.hostWire_injective
ConcreteSpliceAttachment.diagram_wire_hostWire
```

in `VisualProof/Diagram/Concrete/Subgraph/SpliceRaw.lean:822-827` and
`:1091-1097`, but `Step.lean` cannot access the receipt's private attachment.

The precise missing owner interface is:

```lean
StructuralInsertionReceipt.rawHostWire_injective
    (checked : StructuralInsertionReceipt input) :
    Function.Injective checked.rawHostWire

StructuralInsertionReceipt.rawHostWire_signature
    (checked : StructuralInsertionReceipt input)
    (wire : base.val.WireId) :
    (checked.target.val.wires (checked.rawHostWire wire)).sig =
      (base.val.wires wire).sig
```

These theorems must be proved inside the structural owner from the retained
attachment. Re-proving them from representation details in `Step.lean`,
accepting them as caller premises, or replacing the carrier with all-`none`
provenance would violate receipt ownership. The same completed owner interface
will serve `atomSpawn` and `identityInsert`, but the audit intentionally did not
skip ahead past the first missing theorem.

Per the repair contract, no partial receipt migration was made. No behavior
changed, so validation was not rerun and no Lean source commit was created.
The protected dirty files and the preserved untracked
`VisualProof/Diagram/Concrete/OpenIsomorphism.lean` draft remain untouched.
Foundation evidence:
`/tmp/task-11-receipt-migration-foundation-20260803-r2.md`.

## Insertion carrier slice

**Status:** COMPLETE — `StructuralInsertionReceipt` now publicly owns the
minimal checker-derived raw host-wire carrier laws needed by the `refSpawn`
receipt route.

**Foundation record:**
`/tmp/vpa-task11-insertion-carrier-20260803-foundation.md`

**API and ownership:** `StructuralInsertionReceipt.rawHostWire_injective`
projects the private accepted `ConcreteSpliceAttachment.hostWire_injective`.
`StructuralInsertionReceipt.rawHostWire_signature` projects the attachment's
generated target wire-table law, `diagram_wire_hostWire`. The concrete
attachment remains private; no search, alternative carrier, fallback, or
insertion redesign was introduced.

**Fixture evidence:** `StructuralFixtures` proves, for the existing accepted
insertion, both injectivity of `rawHostWire` and pointwise signature
preservation from base wire to raw target wire.

**Validation:** `lake build VisualProof.Rule.StructuralFixtures
VisualProof.Rule.StepFixtures`, full `lake build` (194 jobs), `npm run
formal:size`, and `git diff --check` passed. Existing lint warnings only.

**Source commit:** `784bb84` (`feat: expose structural insertion wire carrier
laws`)

**Concerns:** None for this slice. The broader `StepReceipt` authority
migration remains deliberately unimplemented.

## Complete 34-constructor owner-carrier audit

**Status:** DONE_WITH_CONCERNS — 20 constructors have complete current owner
routes; 14 require a coherent five-group prerequisite batch before
`StepReceipt` can be sealed.

**Foundation record:**
`/tmp/task-11-complete-owner-audit-foundation-20260803.md`

This audit is against HEAD `8f4101f`, which includes the green insertion
carrier source commit `784bb84`. In the matrix, “logical” means the raw rule
action before normalization, while “provenance” means the partial injective
image of stable surviving source identities. Identity normalization is not
part of any row: afterward, logical transport composes with `wireImage` and
provenance composes with `externalImage?`.

| # | Constructor | Canonical raw logical map | Canonical external provenance | Existing exact owner API | Missing owner API |
|---:|---|---|---|---|---|
| 1 | `refSpawn` | Total `checked.rawHostWire` | Same total injection | `StructuralInsertionReceipt.rawHostWire`, `_injective`, `_signature` | None |
| 2 | `atomSpawn` | Total `checked.rawHostWire` | Same total injection | Same structural-insertion API | None |
| 3 | `identityInsert` | Total `checked.rawHostWire` | Same total injection | Same structural-insertion API | None |
| 4 | `wireJoin` | Inner wire coalesces to `outerWire`; every other wire uses `WireJoinResult.wireImage` | `inner -> none`; every `wire != inner` uses `wireImage` (so the stable outer survives) | Lower result owns `outer`, `inner`, `wireImage`, `outerWire`, `sourceWire` inverse laws, equal signatures, and retained signature law; `AppliedWireJoin` hides the result | Public applied-owner raw logical/provenance maps and their laws |
| 5 | `erasure` | Compose `sourceIso.wires` with the partial inverse of the accepted insertion's host-wire carrier; inserted internal wires map to `none` | Same partial injection | `StructuralErasureReceipt` privately retains the exact insertion; `CompiledPrimitiveStep.erasure` owns `sourceIso` | Structural-erasure partial wire image plus injectivity/signature laws |
| 6 | `wireSever` | Total retained branch `WireSeverResult.wireImage`; the newly split branch has no source preimage | Same total source injection | Lower result owns `wireImage`, signature, `sourceWireOfRetained` inverse laws, and `retained_ne_fresh`; `AppliedWireSever` hides the result | Public applied-owner total image plus injectivity/signature laws |
| 7 | `iteration` | Total host image through the accepted `destinationAttachment` | Same total injection | `CheckedOrdinaryIteration` privately retains `destinationAttachment` and raw splice result | `rawHostWire`, injectivity, and signature laws |
| 8 | `deiteration` | `wire -> Removal.wireIndex` exactly when the wire survives removal; removed inner wires map to `none` | Same partial injection | Receipt privately retains `RemovalResult`; lower `Removal.wires`, `wireIndex`, `sourceWire`, inverse laws, and `diagramWire_signature` exist | Public partial raw image plus injectivity/signature laws |
| 9 | `doubleCutIntro` | Total `checked.wireEquiv` | Same total injection | `CheckedDoubleCut.wireEquiv`, `_injective`, `_signature` | None |
| 10 | `doubleCutElim` | Total `checked.wireEquiv.symm` | Same total injection | `wireEquiv`, inverse bijection, `wireEquiv_symm_signature` | None |
| 11 | `theorem` | For each source wire retained by occurrence removal: `Removal.wireIndex` then replacement attachment `hostWire`; removed theorem-side internal wires map to `none` | Same partial injection | `AppliedTheorem` privately retains occurrence, removal, replacement attachment, and raw splice; lower removal/splice carrier laws exist | Public replacement partial image plus injectivity/signature laws |
| 12 | `vacuousIntro` | Total plain-to-bound image `(deletion.wireOriginEquiv wire).1` | Same total injection; the new bound wire has no source preimage | `EliminationReceipt.wireOriginEquiv` and `wire_signature` | None |
| 13 | `vacuousElim` | Eliminated wire maps to `none`; every survivor maps through `targetWireImage ⟨wire, h⟩` | Same partial injection | `eliminatedWire`, `wireOriginEquiv`, `targetWireImage`, inverse laws, and `wire_signature` | None; injectivity/signature derive directly from the public equivalence |
| 14 | `unfold` | Retained source wire: removal index then body-splice host image; removed reference-internal wire maps to `none` | Same partial injection | `AppliedUnfold` privately retains occurrence, removal, attachment, and raw splice; lower exact laws exist | Public replacement partial image plus injectivity/signature laws |
| 15 | `fold` | Retained source wire: removal index then reference-splice host image; removed body-internal wire maps to `none` | Same partial injection | `AppliedFold` privately retains removal, attachment, and raw splice; lower exact laws exist | Public replacement partial image plus injectivity/signature laws |
| 16 | `cutWrap` | Total `constructionResult.targetWireImage`; the acted wire maps to `targetWire` | Only `wire != acted` maps through `retainedWireImage`; the consumed/reallocated acted identity maps to `none` | Applied receipt exposes `constructionResult`; result exposes `wireOriginEquiv`, total/retained images, origin laws, retained signature, and acted target signature | None |
| 17 | `cutAbsorb` | Total `wireOriginEquiv.symm`; the acted source maps to `targetWire` | Restrict the same carrier to `wire != acted`; the consumed/reallocated acted identity maps to `none` | Lower result retains `wireOriginEquiv`, `targetWire`, inverse wrap, and inverse isomorphism; applied receipt hides it; no direct wire signature law | Public construction result, directional target image, and injectivity/signature laws |
| 18 | `parallelSplit` | Acted source maps to canonical `firstWire`; every other source maps through `retainedWireImage` | Only `wire != acted` uses `retainedWireImage`; both generated branches are new identities | Applied receipt exposes result; result exposes retained image, first/second wires, complete wire-origin equivalence, retained and branch signature laws | None |
| 19 | `parallelFuse` | `left` and `right` coalesce to `targetWire`; all other wires use the retained image | Both acted/coalesced identities map to `none`; every wire distinct from both uses the retained injection | Lower result retains target, inverse split, inverse isomorphism, and a target allocation equivalence, but exposes no source-direction retained/logical classifier; applied receipt hides the result | Public construction result, retained source image, coalescing logical map, partial provenance map, and all signature/injectivity laws |
| 20 | `endsDelete` | Total `constructionResult.targetWireImage` | Same total injection: only endpoints/nodes are deleted; no wire identity is removed | Applied receipt exposes result; `wireOriginEquiv`, `targetWireImage`, origin inverse, and signature law exist | None |
| 21 | `endsSpawn` | Total `wireOriginEquiv.symm` | Same total injection: only endpoints/nodes are appended; no wire identity is replaced | Lower result exposes `wireOriginEquiv` but applied receipt hides the result and no directional signature law exists | Public construction result, source-to-target image, and injectivity/signature laws |
| 22 | `arityShift` | Acted signature-changing wire maps to `none`; every other wire uses `transportRetainedWire` | Same partial injection | Public argument result, exact `[acted]` removal set, retained image/signature, target-exclusion and retained inverse machinery | None |
| 23 | `arityUnshift` | Every member of `sourceRemovedWires` (acted head and checked local wires) maps to `none`; other wires use `argumentResult.retainedWireImage` | Same partial injection | Public argument result/removal set; lower retained image, signature, target-exclusion, and inverse laws | None |
| 24 | `argPermute` | Acted signature-changing wire maps to `none`; every other wire uses `applied.wireEquiv` | Same partial injection | `wireEquiv` is an equivalence and `wireEquiv_retained_signature` covers `wire != acted` | None |
| 25 | `argDuplicate` | Acted signature-changing wire maps to `none`; every other wire uses `wireEquiv` | Same partial injection | `wireEquiv`, equivalence injection, retained signature law | None |
| 26 | `argContract` | Acted signature-changing wire maps to `none`; every other wire uses `wireEquiv` | Same partial injection | `wireEquiv`, equivalence injection, retained signature law | None |
| 27 | `argDrop` | Acted signature-changing wire maps to `none`; every other wire uses `wireEquiv` | Same partial injection | `wireEquiv`, equivalence injection, retained signature law | None |
| 28 | `argExtend` | Acted signature-changing wire maps to `none`; every other wire uses `wireEquiv` | Same partial injection | `wireEquiv`, equivalence injection, retained signature law | None |
| 29 | `applyFormal` | Consumed acted relation maps to `none`; every other wire maps through `constructionResult.targetWireImage ⟨wire, h⟩` | Same partial injection | Applied receipt exposes `LeafResult`; result exposes retained `wireOriginEquiv`, target image, inverse law, and signature law | None |
| 30 | `abstractFormal` | Total stable source-prefix image `wireSplitEquiv.symm (Fin.castAdd 1 wire)`; appended relation wire is fresh | Same total injection | `LeafAbstractResult.wireSplitEquiv` exists, but applied receipt hides the result and no source-prefix signature theorem exists | Public construction result and total source-wire image with injectivity/signature laws |
| 31 | `identityLeaf` | Consumed acted relation maps to `none`; every other wire uses leaf `targetWireImage` | Same partial injection | Same complete `LeafResult` route as `applyFormal` | None |
| 32 | `identityAbstract` | Total stable source-prefix image through `wireSplitEquiv.symm` | Same total injection | Same incomplete `LeafAbstractResult` route as `abstractFormal` | Public construction result and source-image laws |
| 33 | `refLeaf` | Consumed acted relation maps to `none`; every other wire uses leaf `targetWireImage` | Same partial injection | Same complete `LeafResult` route as `applyFormal` | None |
| 34 | `refAbstract` | Total stable source-prefix image through `wireSplitEquiv.symm` | Same total injection | Same incomplete `LeafAbstractResult` route as `abstractFormal` | Public construction result and source-image laws |

### Batched missing owner APIs

The following shapes are the complete prerequisite batch. Exact spelling may
vary, but each authority and law must live at the named owner boundary.

1. **Structural owner — `VisualProof/Rule/Structural.lean` (3 rows)**

   - `StructuralErasureReceipt.rawWireImage?` from inserted raw source to base,
     with `rawWireImage_injective` and `rawWireImage_signature`.
   - `CheckedOrdinaryIteration.rawHostWire`,
     `rawHostWire_injective`, and `rawHostWire_signature`, projected from the
     retained destination attachment.
   - `CheckedOrdinaryDeiteration.rawWireImage?`,
     `rawWireImage_injective`, and `rawWireImage_signature`, projected from
     the retained removal result.

2. **Partition owner — `VisualProof/Rule/WirePrimitive/Partition.lean` (2 rows)**

   - `AppliedWireSever.rawWireImage` with injectivity and signature laws,
     projecting the hidden `WireSeverResult` carrier.
   - `AppliedWireJoin.rawLogicalImage?` with signature law and
     `rawExternalImage?` with injectivity/signature laws. The logical map sends
     `inner` to `outerWire`; provenance rejects `inner` and retains `outer`.
     These APIs should encapsulate the private outer/inner choice rather than
     exposing a new caller decision.

3. **Replacement owners — `VisualProof/Rule/Theorem.lean` and
   `VisualProof/Rule/Definition.lean` (3 rows)**

   - `AppliedTheorem.rawWireImage?`, `rawWireImage_injective`, and
     `rawWireImage_signature`.
   - The same three laws for `AppliedUnfold` and `AppliedFold`.
   - Each is the owner-held composition of occurrence removal's retained
     `wireIndex` with the accepted replacement attachment's `hostWire`; no
     occurrence search or Step-level access to private fields is permitted.

4. **Content owner — `VisualProof/Rule/WirePrimitive/Content.lean` plus its
   concrete content carrier module (3 rows)**

   - Expose `AppliedCutAbsorb.constructionResult`; add the source-to-target
     `CutAbsorbResult.targetWireImage` and its injectivity/signature laws.
     Provenance is that image restricted away from the consumed acted wire.
   - Expose `AppliedParallelFuse.constructionResult`; add a construction-owned
     retained source image, its injectivity/signature laws, the logical map
     coalescing both inputs at `targetWire`, and the partial provenance map
     excluding both inputs. `constructionWireEquiv` alone is insufficient
     because it does not classify source identities.
   - Expose `AppliedEndsSpawn.constructionResult`; add total
     `EndsSpawnResult.targetWireImage` with injectivity/signature laws.

5. **Leaf abstraction owner — `VisualProof/Rule/WirePrimitive/Leaves.lean`
   plus `Diagram/Concrete/WirePrimitive/Leaves.lean` (3 rows)**

   - Expose `constructionResult` on `AppliedAbstractFormal`,
     `AppliedIdentityAbstract`, and `AppliedRefAbstract`.
   - Add `LeafAbstractResult.sourceWireImage :=
     wireSplitEquiv.symm (Fin.castAdd 1 wire)`, plus injectivity and signature
     laws. The appended relation wire remains fresh and has no source origin.

No other prerequisite is missing. In particular, structural insertion,
double cut, vacuity, the ready content directions, arguments, forward leaves,
and normalization already expose enough exact carrier evidence. The all-34
migration should remain stopped until these five groups land together or in
validated owner slices; otherwise Step would again need private-field
reconstruction or partial authority.

No Lean source was edited and no broad validation was run. The report diff was
checked for whitespace errors. Protected dirty files and the preserved
`OpenIsomorphism.lean` draft were not touched.
