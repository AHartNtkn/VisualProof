# Task 3 signature-indexed compiler production report

Status: COMPLETE

## Outcome

The production source compiler now has one signature-indexed result authority.
Every successful root or nested region result is indexed by the exact call that
produced it. The source focus is one structural zipper over that result, and a
`CompiledSite` stores exactly one such focus.

Endpoint call inputs, endpoint result, intrinsic context, focused body, cut
depth, source occurrence, rebuilding equation, and direct compiled items are
all projections of the same focus. Selection partitioning operates on those
direct items. Encoding consumes the public compiler entry points and public
success-inversion laws directly.

No endpoint reconciliation layer, occurrence-index transport, target compiler
state, stored path, call trace, or consumer-specific compiler state was
required. The architecture verdict is GO.

## Commits

The implementation is split into dependency-ordered strict-green checkpoints:

1. `862d393e` — index compiler results by exact call signatures
2. `f4d82f55` — fix compiler node kernel to exact signatures
3. `ceef7aec` — replace compiler producer with exact signatures
4. `4e9c1177` — migrate elaboration to indexed root results
5. `bd7c647b` — migrate certified compiler equivariance
6. `b28b4ffc` — derive compiled focus from indexed results

## Responsibility model

### Exact compiler calls and results

- `CompilerCall.root` owns the exact ambient and local wire contexts.
- `CompilerCall.nested` owns predecessor fuel, origin, exact wire context,
  relation context, and exact binder context.
- `CompiledRegion` is indexed by one `CompilerCall` and owns the direct compiled
  item sequence at that call's derived child signature.
- `CompiledItem` owns an ordinary occurrence origin. Cut and bubble constructors
  contain child region results at their exact recursive call indices.
- `CompiledItems` is an ordinary ordered sequence with uniform fuel, wire
  context, relations, and binders. Its origins are a derived list.
- `compileRegion?`, `compileOccurrence?`, `compileItems?`, and `compileRoot?`
  are the public producer surface. Fuel recursion and its implementation
  helpers remain private.

### One structural source focus

- `CompiledZipper` selects the current region or descends into one compiled item
  sequence.
- `CompiledItemsZipper` has only cut, bubble, and tail structural cases.
- `CompiledFocus` packages the exact endpoint call/result and that zipper.
- `CompiledSite` has one field: `focus` over
  `source.checked.compilation`.
- `CompiledIntrinsic` is derived in the same recursion as the zipper. Its
  context hole indices are the endpoint call's outer wire length and relations,
  and its body is definitionally `endpoint.erase`.
- The sole parent-frame wire-length transport is confined to one private
  `DiagramContext.castOuterWires_fill` lemma shared by cut and bubble. It does
  not alter endpoint indices or the focused body.
- Total focus construction follows compiler success and diagram enclosure.
  It does not run an executable search or store navigation state.

### Consumers

- Elaboration stores the exact root-indexed result and defines the intrinsic
  body by erasure.
- Certified equivariance is stated over exact compiler calls and results.
- Occurrence results retain their ordinary-origin interface.
- Encoding uses the public origin and success-inversion laws and the canonical
  `CompiledItems.erase_get` theorem.
- `CompiledSelection` stores the anchor `CompiledSite` and derives its stable
  retained/material partition and intrinsic factorization from the endpoint's
  one item sequence.
- Aggregate elaboration, translation, and representation modules accept the
  new boundary directly and required no source changes.

## Complexity ledger self-review

- Essential behavior is unchanged: checked diagrams elaborate through the same
  public root and nested compiler entry points and erase to intrinsic regions.
- Essential state is held once: exact call inputs in `CompilerCall`, occurrence
  origins in compiled items, and recursive child results in the result tree.
- Compiler-success origin order is proved over ordinary lists, so encoding and
  stable selection need no dependent occurrence casts.
- Intrinsic context, body, cut depth, source occurrence, direct items, and
  selection subsequences are projections or theorems, not parallel stored
  state.
- The seven changed production files total 1,950 insertions and 2,839
  reductions relative to `10a431a0`, for a net reduction of 889 lines.
- `Compiled.lean` is 960 lines, 44 lines smaller than its starting version,
  while owning the complete zipper, totality, site, and selection boundary.

## Validation

All changed modules pass direct strict elaboration with warnings as errors:

```text
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Tree.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Kernel.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Region.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Elaborate.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Certified.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Occurrence.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compiled.lean
lake env lean -DwarningAsError=true VisualProof/Concrete/Encode.lean
```

Focused build results:

- compiler focus: 30/30 jobs
- encoding closure: 41/41 jobs
- aggregate elaboration, translation, and representation: strict GREEN

Repository-wide `lake build` succeeds: 96/96 jobs. It reports warnings in
untouched modules; every changed compiler module is warning-free under
`-DwarningAsError=true`.

Authority and forbidden scans confirm one `CompilerCall` family, one mutually
recursive compiled-result family, one public root/nested compiler surface, one
stored `CompiledSite.focus`, and no forbidden bridge in the changed closure.
`git diff --check` passes.

## Final assessment

All acceptance gates are satisfied. No task-owned concern remains. The next
splice theorem can consume the source endpoint call, endpoint result, and
intrinsic context directly from `CompiledSite` without extending the compiler
authority.
