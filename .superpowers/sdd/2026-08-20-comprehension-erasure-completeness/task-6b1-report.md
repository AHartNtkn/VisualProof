# Task 6b1 implementation report

Date: 2026-08-21

## Status

**GREEN.** Exact evidence-indexed identity-boundary normalization now generates
dependent `RegionResult` / `ItemsResult` / `ItemResult` outputs and preserves
canonicality, inherited-wire incidence nonemptiness, and inherited-wire
`RegionPath.RootedTwo`. The owning public theorem returns the generated
`ItemsResult` together with canonical and external-two-ended validity in the
original occurrence context.

Commit subject: `feat(lean): preserve normalized comprehension scope`.

This task contains no reachability fold, Exposure API change, or BoundaryPlan
integration.

## Owning theorem signatures

The narrow Diagram owner exposes the generic cross-source/target conjunction
preservation principle:

```lean
theorem Region.conjoin_preserves_scope
    (sourceFirst sourceSecond targetFirst targetSecond : Region outer)
    (firstCanonical : sourceFirst.Canonical → targetFirst.Canonical)
    (secondCanonical : sourceSecond.Canonical → targetSecond.Canonical)
    (firstNonempty : ∀ {signature} (wire : Var outer signature),
      sourceFirst.incidencePaths wire.index.val ≠ [] ↔
        targetFirst.incidencePaths wire.index.val ≠ [])
    (secondNonempty : ∀ {signature} (wire : Var outer signature),
      sourceSecond.incidencePaths wire.index.val ≠ [] ↔
        targetSecond.incidencePaths wire.index.val ≠ [])
    (firstRooted : ∀ {signature} (wire : Var outer signature),
      RegionPath.RootedTwo
          (sourceFirst.incidencePaths wire.index.val) →
        RegionPath.RootedTwo
          (targetFirst.incidencePaths wire.index.val))
    (secondRooted : ∀ {signature} (wire : Var outer signature),
      RegionPath.RootedTwo
          (sourceSecond.incidencePaths wire.index.val) →
        RegionPath.RootedTwo
          (targetSecond.incidencePaths wire.index.val)) :
    ((sourceFirst.conjoin sourceSecond).Canonical →
        (targetFirst.conjoin targetSecond).Canonical) ∧
      ∀ {signature} (wire : Var outer signature),
        ((sourceFirst.conjoin sourceSecond).incidencePaths
              wire.index.val ≠ [] ↔
            (targetFirst.conjoin targetSecond).incidencePaths
              wire.index.val ≠ []) ∧
          (RegionPath.RootedTwo
              ((sourceFirst.conjoin sourceSecond).incidencePaths
                wire.index.val) →
            RegionPath.RootedTwo
              ((targetFirst.conjoin targetSecond).incidencePaths
                wire.index.val))
```

Its rootedness proof uses the exact component-independent characterization:

```lean
RegionPath.RootedTwo
    ((first.conjoin second).incidencePaths wire.index.val) ↔
  RegionPath.RootedTwo (first.incidencePaths wire.index.val) ∨
  RegionPath.RootedTwo (second.incidencePaths wire.index.val) ∨
    (first.incidencePaths wire.index.val ≠ [] ∧
      second.incidencePaths wire.index.val ≠ [])
```

Thus a cross-component root is reconstructed from one incidence in each
component; source and target `RegionPath.shiftHead` offsets never need to be
equal.

The sole new Compiler handoff is:

```lean
theorem EqualityNormalization.normalizeItemsScope
    {arguments common sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence : Instantiation.ItemsResult
      pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ normalized : Region common,
      Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        (occurrence.context.fill normalized).Canonical ∧
        OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill normalized)
```

## Exact dependent outputs and induction

The three private mutually recursive generators have these result indices:

```lean
normalizedRegion pattern evidence sites :
  { normalized : Region common //
    Instantiation.RegionResult
      (identityBoundary pattern) frame.sourceKeep frame.selected source
        normalized }

normalizedItems pattern evidence sites :
  { normalized : Region common //
    Instantiation.ItemsResult
      (identityBoundary pattern) frame.sourceKeep frame.selected source
        normalized }

normalizedItem pattern evidence sites :
  { normalized : Region common //
    Instantiation.ItemResult
      (identityBoundary pattern) frame.sourceKeep frame.selected source
        normalized }
```

Each accepts the exact original Instantiation evidence and the exact
evidence-indexed `RegionSites` / `ItemsSites` / `ItemSites`; no endpoint is
supplied by a caller. The matching mutually recursive theorems return:

```lean
ScopePreservation result (normalizedRegion pattern evidence sites).1
ScopePreservation result (normalizedItems pattern evidence sites).1
ScopePreservation result (normalizedItem pattern evidence sites).1
```

`ScopePreservation` contains exactly:

- source canonicality implies target canonicality;
- inherited incidence nonemptiness is equivalent in both directions;
- inherited rooted two-endedness is preserved source-to-target.

The constructor coverage is complete:

- `RegionSites.mk`: preserves the material result through exact
  `Region.adjoinAt ... .nil`, including host-local roots.
- `ItemsSites.nil`: definitional blank preservation.
- `ItemsSites.cons`: calls `Region.conjoin_preserves_scope` directly.
- retained atom and identity: definitional preservation.
- selected atom: generates
  `Instantiation.instantiate (identityBoundary pattern) ports`, calls the
  shared `Instantiation.instantiate_canonical`, and characterizes incidence
  and rootedness by the exact `ports.countIndex`.
- cut: recurses through the exact `RegionResult`, then preserves paths under
  the single cut-path prefix.

## Theorem-driven RED / GREEN receipts

All definitions and private preservation dependencies elaborated before the
owning theorem entered RED.

RED command:

```text
lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

With only `EqualityNormalization.normalizeItemsScope` proved by `sorry`, the
command exited `0` and produced exactly:

```text
VisualProof/Rule/Completeness/Comprehension/Compiler.lean:1472:8: warning: declaration uses `sorry`
```

The theorem statement was unchanged when its kernel-checked proof replaced the
RED body.

GREEN command:

```text
lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

Output: none. Exit status: `0`.

## Final validation receipts

All commands ran from
`/home/ahart/Documents/VisualProofAssistant/.worktrees/signature-indexed-wires`.

Focused Diagram elaboration:

```text
lake env lean VisualProof/Diagram/Scope/Rename.lean
```

Exit status: `0`. It reports only the unused-simp warnings at lines 60 and
1306 already present in this module's surrounding code.

Focused Compiler elaboration:

```text
lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

Output: none. Exit status: `0`.

Proof-hole audit:

```text
rg -n '\b(sorry|admit)\b|^\s*axiom\b' VisualProof
```

Output: none. Exit status: `1` (no matches).

Forbidden-transport and out-of-scope addition audit:

```text
git diff --unified=0 -- \
  VisualProof/Diagram/Scope/Rename.lean \
  VisualProof/Rule/Completeness/Comprehension/Compiler.lean | \
  rg '^\+' | \
  rg -n '\b(cast|Eq\.rec)\b|occurrenceCongr|WireSever|\bxor\b|\bXor\b|BoundaryPlan|Relation\.ReflTransGen|\bStep\b|\bDerives\b|\bDischarge\b'
```

Output: none. Exit status: `1` (no matches).

Public-surface audit:

```text
git diff --unified=0 -- \
  VisualProof/Diagram/Scope/Rename.lean \
  VisualProof/Rule/Completeness/Comprehension/Compiler.lean | \
  rg '^\+(theorem|def|structure|inductive) '
```

Exact output:

```text
+theorem Region.conjoin_preserves_scope
+theorem normalizeItemsScope
```

All other task helpers are private and have direct callers.

Diff hygiene:

```text
git diff --check
```

Output: none. Exit status: `0`.

Full validation:

```text
lake build
```

Exit status: `0`; exact completion line:

```text
Build completed successfully (77 jobs).
```

The build reports only the unused-simp warnings in
`VisualProof/Diagram/Isomorphism.lean` and
`VisualProof/Diagram/Scope/Rename.lean`.

## Files

- `VisualProof/Diagram/Scope/Rename.lean`
- `VisualProof/Rule/Completeness/Comprehension/Compiler.lean`
- `.superpowers/sdd/2026-08-20-comprehension-erasure-completeness/task-6b1-report.md`

## Self-review and concerns

- Exact dependent indices generate the normalized endpoint and every
  Instantiation witness; there is no endpoint equality transport, `cast`, or
  `Eq.rec`.
- The conjoin theorem handles different leading item counts structurally and
  is called immediately by the authoritative `ItemsSites.cons` preservation
  case.
- The selected case uses `identityBoundary` and the sole shared
  `Instantiation.instantiate_canonical` authority.
- The public Compiler theorem exposes only the exact normalized result and the
  validity facts required by the later reachability task.
- No synthetic theorem/example, alternate context authority, Exposure API,
  reachability rule, or BoundaryPlan path is present in this task.
- No correctness blocker or remaining mutual preservation case is known.
