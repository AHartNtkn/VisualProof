# Task 13 independent review

## Assessment

Rejected pending two Important corrections. The Lean build and admission scan
pass, and the new relations are semantically sound for the witnesses they
accept, but the formal Fusion surface omits a valid TypeScript operation and
the AnchoredWire global-address composition is incorrect for descendant-root
locals.

## Critical findings

None.

## Important findings

### 1. Fusion cannot represent a consumer in a descendant region

`Fusion.Description.source` places the producer and consumer as the first two
items of one `Region`, and `Description.target` places the merged consumer in
that same region (`VisualProof/Rule/Lambda/Fission.lean:231-247`). The only
global wrapper is a single ordinary `Occurrence` of that local source
(`VisualProof/Rule/Lambda/Fission.lean:264-278`), so it cannot put the producer
at an ancestor scope and the consumer inside a descendant cut.

The authoritative TypeScript rule has no same-region requirement. It requires
only that the producer's region equal the bridge's derived scope
(`src/kernel/rules/lambda/fission.ts:156-164`), and it deliberately preserves
the consumer's own region when constructing the merged node
(`src/kernel/rules/lambda/fission.ts:199-208`). A root producer connected by a
private output/free bridge to a consumer in a child cut therefore succeeds; I
executed that case directly and `applyLambdaFusion` returned the merged
consumer in the child region.

Consequently `Lambda.Fusion`, its exact runners, and the aggregate execution
claims do not cover the complete Task 7 operation. Represent Fusion with a
nested producer/consumer occurrence (or an equivalently exact existing
recursive occurrence witness), retain the producer-at-bridge-scope condition,
and prove/run the descendant-consumer case as well as the same-region case.

### 2. Nested AnchoredWire addresses omit the prefix on descendant-root locals

The nested source representation lays the anchor region's local context out as

`anchorLocals ++ selected.locals ++ descendant-root locals`:

- `anchorMaterial` conjoins `selected` before the filled descendant, so their
  local lists append (`VisualProof/Diagram/NestedScopedRewrite.lean:34-37`).
- `anchorRegion` then adjoins that material after `anchorLocals`
  (`VisualProof/Diagram/NestedScopedRewrite.lean:39-43`).

Despite that layout, `descendantWireAddress` preserves an internal wire's
unshifted local index (`VisualProof/Diagram/NestedScopedRewrite.lean:77-83`),
and the local branch of `nestedItemAddress` likewise emits
`localWire.index.val` unchanged (`VisualProof/Diagram/NestedScopedRewrite.lean:87-99`).
When the addressed owner is the descendant root, both need the
`anchorLocals.length + selected.locals.length` prefix. Descendant paths under
an actual cut do not need that local-index shift; the root-owner case does.

This directly corrupts the AnchoredWire contract premises that use those
addresses: output distinctness, the drop scope, and the exact completion set
(`VisualProof/Rule/Lambda/AnchoredWire.lean:247-270`). In an ordinary
same-region contract, the survivor output occupies an `anchorLocals` slot and
`Contract.Primary.drop` is a descendant-root local. With both local indices
equal to zero, the current address functions identify both as the same global
wire, even though TypeScript accepts and performs this contraction. Depending
on the surrounding locals, the relation is therefore either unavailable or
its completion plan can be certified against the wrong carrier.

Correct the root-local address embedding (including both the
`descendantWireAddress` and local `nestedItemAddress` paths), then validate
same-region contraction, descendant contraction, carrier aliases, exact old
scopes, and the final two-ended target against the TypeScript operation.

## Minor findings

None.

## Areas reviewed without findings

- Fission's bound-closed path witness, capture-avoiding residual, reconstruction,
  native-slot aliases, and binary bridge match the TypeScript split.
- Fusion's same-region carrier list, consumer duplicate columns, producer
  same-position preference, first physical occurrence fallback, and old-scope
  completion data match TypeScript once restricted to the represented case.
- Congruence preserves aliased physical carriers, requires covered common
  columns and distinct outputs, checks both output scope depths, and keeps the
  left output, matching the operational guards.
- `Model.rigidHead_args_reflect` is the specific reflection principle needed
  by HeadStrip. Its canonical quotient proof transports evaluation equality to
  beta-eta equivalence and back to each aligned prefix-closed argument without
  an extra semantic assumption.
- HeadStrip preserves aligned bound rigid heads, source argument order,
  syntactic reflexivity filtering, first-occurrence physical compaction, and
  touched-wire completion.
- The AnchoredWire primary split/contract constructions otherwise carry the
  closed witnesses, exact port partition/collapse, availability structure,
  authoritative completion sequence, canonical target, and external
  two-endedness required by the task.
- All five new relations have isomorphism transport, soundness cases, forward
  and backward source-indexed runners, Step evidence constructors, and
  aggregate execution-completeness cases. Existing Spawn, TermLeaf,
  Conversion, and FreeVariableIdentity definitions and registrations were not
  displaced.
- The implementation report records theorem-driven RED/GREEN for each owning
  production theorem, and the final tree contains no Lean admissions.

## Validation

- `lake build` — PASS, 151 jobs.
- `rg -n '\bsorry\b' VisualProof --glob '*.lean'` — no matches.
- `git diff --check f36bce003cd9b44929ab9299b0bfd4b2a769d54f..c533dfe57c0319ded1bb064998863ec0c624d88a` — PASS.
- Direct TypeScript probes confirmed both omitted operational cases:
  descendant-consumer Fusion and same-region AnchoredWire contraction.

## Re-review: fix round 1

### Assessment

Approved. Both prior Important findings are resolved, and I found no regression
in the corrected Fusion or nested AnchoredWire address paths.

### Critical findings

None.

### Important findings

None.

### Minor findings

None.

### Fusion verification

- `Fusion.Description` now separates ancestor-owned producer data from the
  consumer's recursive descendant context. `extension` carries the fresh bridge
  through every cut as an inherited wire; `source` places the producer at the
  ancestor and the consumer in the extended context, while `target` rebuilds the
  original context and merged consumer (`VisualProof/Rule/Lambda/Fission.lean:190-321`).
  The `.hole` case is same-region Fusion, and recursive `.cut` cases preserve an
  arbitrarily deep descendant consumer.
- The producer/consumer carrier list still has the exact TypeScript order and
  alias behavior: non-consumed consumer columns are retained positionally,
  producer slots prefer the same native position and otherwise reuse the first
  physical occurrence, and duplicate physical carriers are completed once
  (`VisualProof/Rule/Lambda/Fission.lean:130-167,201-231,442-449`; compare
  `src/kernel/rules/lambda/fission.ts:166-198,212-217`).
- Source/target address pairs account for deletion of the ancestor bridge and
  producer item. Old scopes are computed from source incidences, rebased only
  across the preserved descendant branch, and applied to the target carrier
  address. Completion depth is the outer occurrence depth plus descendant depth,
  and the public target is still description-owned, canonical, and externally
  two-ended (`VisualProof/Rule/Lambda/Fission.lean:347-544`).
- Recursive denotational transport proves both the `.hole` and `.cut` cases,
  including cut negation and environment reachability. Fusion soundness then
  composes the local equivalence, exact completion plan, and open isomorphisms
  (`VisualProof/Diagram/Semantics/NestedScopedRewrite.lean:27-176`;
  `VisualProof/Rule/Soundness/Lambda/Fission.lean:551-730`). Forward and backward
  exact runners quantify over the updated description, so both same-region and
  descendant witnesses are covered (`VisualProof/Rule/Executable/Lambda/Fission.lean:76-135`).
- Direct TypeScript probes of a root producer with (a) a root consumer and (b) a
  consumer one cut below both removed the producer and bridge, preserved the
  consumer's original region, retained the shared physical carrier once, and
  produced the same one-slot merged application. This matches the formal source,
  target, carrier, and region-preservation construction.

### Nested AnchoredWire address verification

- Combined-root locals are now indexed after
  `anchorLocals.length + selected.locals.length`; actual cut-owned locals keep
  their native index while only their owner path is embedded. Both
  `descendantWireAddress` and `nestedItemAddress` route through this
  owner-sensitive distinction, with explicit reduction theorems for root and
  cut cases (`VisualProof/Diagram/NestedScopedRewrite.lean:144-278`).
- AnchoredWire split uses the corrected anchor address for its exact completion
  request, and contract uses it consistently for survivor/drop distinctness,
  drop-derived scope, touched carriers, and target completion destinations.
  Each rewrite still owns its ordered completion plan and final canonical,
  externally two-ended target (`VisualProof/Rule/Lambda/AnchoredWire.lean:112-162,220-291`).
  Consequently same-region contraction addresses descendant-root locals after
  both prefixes, while descendant contraction leaves true cut-local indices
  unshifted and embeds only their paths.

### Validation

- `lake build` — PASS, 152 jobs.
- `npx vitest run tests/kernel/rules/lambda-fission.test.ts` — PASS, 3 tests.
- Direct same-region and descendant TypeScript Fusion probes — PASS.
- Lean admission scan — no `sorry`, `admit`, or `admitted` proof terms in
  `VisualProof`; the sole textual `admitted` match is prose in an existing
  documentation comment.
- `git diff --check 1fab88a5..c52b7208` — PASS.
