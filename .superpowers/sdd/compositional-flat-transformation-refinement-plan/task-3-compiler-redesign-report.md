# Task 3 compiler redesign report

## Status

Complete. The ordinary compiler now returns one origin-annotated compilation
tree, checked elaboration uses only that tree's intrinsic erasure, and every
checked source region has one canonical `CompiledSite` whose sole stored field
is its source compiler focus.

## Selected responsibility model

- `CompiledItem` owns its concrete node or child-region origin as ordinary
  data. It is not indexed by `LocalOccurrence`.
- `CompiledItems` owns the ordered annotated item sequence. Compiler success
  proves that `CompiledItems.origins` is exactly the ordered occurrence input.
- `CompiledRegion` owns the annotated sequence at the exact total-wire index
  returned by `compileOccurrencesWith?`.
- `RegionWireSplit` contains the local-wire count equation used only when
  erasing a compiled region to an intrinsic `Region`. No annotated item or
  recursively owned child tree is cast for region packaging.
- `compileNode?`, `compileOccurrenceWith?`, `compileOccurrencesWith?`,
  `compileRegion?`, and `compileRoot?` are the single compiler authority.
- `Checked.compilation` and `CheckedOpen.compilation` are the canonical trees;
  their elaborations are the corresponding intrinsic erasures.
- `CompiledSite.focus` is exactly one dependent pair containing a source path
  and its `CompiledPath` witness. The intrinsic `Region.ContextPath`, context,
  local body, intrinsic cut depth, source occurrence, and rebuild theorem are
  derived from that field.
- `CompiledSite.ofSource` privately runs one source-tree search. Checked
  enclosure and the recursive compiler success equations prove that search
  total for every source region.

## Changed boundary

- Added `VisualProof/Concrete/Elaboration/Compile/Tree.lean` for the ordinary
  annotated compiler result and its sole intrinsic erasure.
- Migrated the compiler kernel, region compiler, certified compiler laws,
  occurrence laws, and checked elaboration to that result.
- Migrated encoding and the direct translation/representation closure to use
  erasure only at intrinsic proof boundaries.
- Added `VisualProof/Concrete/Elaboration/Compiled.lean` for the source-only
  compiler focus and imported it from the public elaboration module.

## Architecture audits

- Exactly one `compileRegion?` declaration and one `compileRoot?` declaration
  remain, both in `Compile/Region.lean`.
- `CompiledSite` has exactly one stored field.
- No annotated-tree cast operation exists or is used.
- No compatibility wrapper, mirrored compiler result, alternate stored focus,
  target-derived data, operation-specific logic, or consumer-supplied
  occurrence/index equality was introduced.
- The source search and its totality proofs are private construction details;
  consumers receive the single stored `CompiledPath` focus.
- No concrete execution file or execution import boundary changed.
- No `sorry` occurs in the changed compiler/focus dependency closure.

## Validation

All required checks passed:

- strict warning-as-error compilation of every changed Lean module;
- strict warning-as-error compilation of `Concrete/Elaboration.lean`,
  `Concrete/Translate.lean`, `Concrete/Encode.lean`, and
  `Refinement/Represents.lean`;
- `scripts/audit-lean-authority.sh implementation`;
- `scripts/audit-lean-authority.sh documentation`;
- `lake build` (96 jobs);
- `git diff --check`;
- declaration, single-field, forbidden-cast, target-data, and source-closure
  scans.

The whole build reports warnings in existing modules outside this checkpoint;
the build succeeds, and every changed module is warning-free under
`-DwarningAsError=true`.
