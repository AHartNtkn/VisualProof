# Task 3A selection factorization report

## Status

Complete. A checked source selection now has one source-only
`CompiledSelection` whose only stored field is the existing compiled anchor
site. Stable retained/material partitions, exact source-origin laws, intrinsic
erasures, and the canonical factorization braid are projections of that field
and the checked selection.

## Implemented boundary

### Structural item partition

`VisualProof/Concrete/Elaboration/Compile/Tree.lean` now provides:

- `CompiledItems.Partition`, containing only the derived retained and material
  annotated sequences;
- `CompiledItems.partition`, a pure recursive stable partition by a Boolean
  predicate on `CompiledItem.origin`;
- exact filter equations for both output origin lists;
- `List.Sublist` laws proving both output orders are stable subsequences of
  compiler order;
- a permutation law proving the two outputs are exhaustive;
- `CompiledItems.partitionFactorization`, the canonical neutral `ItemSeqIso`
  from compiler order to retained items followed by material items.

The recursive operation inspects only each direct item's origin. A cut or
bubble and its complete compiled child region move as one item; the partition
does not descend into child bodies.

### Source-only selection authority

`VisualProof/Concrete/Elaboration/Compiled.lean` now provides:

- `CompiledRegionItems`, a derived existential projection of the annotated
  direct item sequence at one compiled region;
- zipper projections that obtain those items from the existing single
  `CompiledRegionFocus`/`CompiledItemsFocus` path;
- a private compiler-origin invariant proving that every derived focused item
  sequence has origins exactly equal to that source region's
  `localOccurrences`;
- `checkedSelectionAnchorClassifier`, fixed by the checked selection's direct
  nodes and direct child roots;
- `CompiledSelection source selection` with exactly the required field:

  ```lean
  anchor : CompiledSite source selection.val.anchor
  ```

- derived anchor items, retained/material annotated sequences, their intrinsic
  erasures, the canonical `ItemSeqIso` factorization, and its derived finite
  position map;
- exact retained/unselected and material/selected origin equations;
- stable-subsequence, exhaustive-permutation, duplicate-free classification,
  and retained/material disjointness laws;
- exact direct-node and direct-child-root material membership laws.

The public `CompiledSelection` API accepts no classifier, order, permutation,
context, route, target, receipt, or compiler callback.

## Mathematical claim established

For any checked source state, checked selection, and compiled anchor site:

1. the anchor annotated origins are exactly the compiler's ordered direct
   source occurrences at the selection anchor;
2. retained origins are exactly that list filtered by classifier false;
3. material origins are exactly that list filtered by classifier true;
4. retained and material origins are stable subsequences of compiler order;
5. their concatenation is a permutation of the complete anchor origin list;
6. because local source occurrences are duplicate-free, the concatenated
   outputs classify every anchor occurrence exactly once and are disjoint;
7. a direct node is material exactly when it belongs to
   `selection.val.directNodes`;
8. a direct child item is material exactly when its root belongs to
   `selection.val.childRoots`;
9. the intrinsic anchor item sequence is related by the derived canonical
   neutral `ItemSeqIso` braid to retained intrinsic items followed by material
   intrinsic items.

This is a source factorization only. It does not claim a complete extracted
pattern compilation or construct a target compilation.

## Complexity-ledger self-review

### Essential behavior and state

- Arbitrary selected direct nodes and arbitrary selected direct child roots
  are classified by concrete annotated origins.
- A selected child subtree remains atomic in its cut or bubble item.
- The stable filters preserve source compiler order in each output.
- `CompiledSelection` stores one `CompiledSite`; that site stores the accepted
  single source zipper.

### Essential invariants and derived data

- Exact compiler-origin agreement is proved from the existing checked root
  compilation and propagated structurally through its existing zipper.
- Disjointness, exhaustiveness, uniqueness, and output stability are theorems,
  not fields.
- Retained/material sequences, origin lists, intrinsic erasures, the position
  equivalence, and the braid are functions of the one anchor field and checked
  selection.

### Forbidden accidental state and control flow

- No partition, context, route, path, position map, braid, or compiler equation
  is stored in `CompiledSelection`.
- No second focus, compiler result, selection view, target data, receipt data,
  or arbitrary presentation/permutation authority exists.
- No target traversal, target search, target compiler invocation, second
  source compiler run, or recursive selection descent into child bodies was
  added.
- The generic structural partition accepts the predicate required by the task;
  the public selection authority fixes its classifier from checked selection
  data and exposes no caller-supplied classifier.
- No compatibility alias, adapter, wrapper authority, or displaced duplicate
  remains.

The focused authority search found exactly one `CompiledSelection`
declaration and exactly one relevant annotated partition operation.

## Validation

All task checks passed:

- `lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compile/Tree.lean`
- `lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration/Compiled.lean`
- `lake env lean -DwarningAsError=true VisualProof/Concrete/Elaboration.lean`
- `lake env lean -DwarningAsError=true VisualProof/Concrete/Encode.lean`
- `lake env lean -DwarningAsError=true VisualProof/Concrete.lean`
- `lake build VisualProof.Concrete.Elaboration.Compile.Tree`
- `lake build VisualProof.Concrete.Elaboration.Compiled`
- `lake build` (96 jobs)
- `scripts/audit-lean-authority.sh implementation`
- `scripts/audit-lean-authority.sh documentation`
- focused scans for `sorry`, `admit`, `#check`, and `example` in both changed
  modules;
- focused searches for duplicate `CompiledSelection` and partition
  authorities;
- `git diff --check`.

Every changed module and direct aggregate is warning-free under
`-DwarningAsError=true`. The full build succeeds. It reports existing warnings
in unchanged semantic/refinement modules outside this task's closure.

## Concerns

None within Task 3A. Later structural grafting must continue to consume this
derived factorization without adding stored target, context, route, or
permutation authority.
