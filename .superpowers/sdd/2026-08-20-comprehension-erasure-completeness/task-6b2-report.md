# Task 6b2 implementation report

Date: 2026-08-21

## Status

**GREEN.** The exact evidence-indexed normalization fold now carries
bidirectional reachability across every annotated comprehension site. The sole
new Compiler handoff returns the private fold's exact normalized region,
`Instantiation.ItemsResult (identityBoundary pattern)`, exact endpoint
validity, and both `Relation.ReflTransGen Step` directions from the caller's
actual occurrence.

Commit subject: `feat(lean): normalize all comprehension sites`.

This task does not modify `BoundaryPlan` or public compiler integration.

## Owning signatures

The public all-sites handoff is:

```lean
theorem EqualityNormalization.normalizeItemsEquates
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
        ∃ targetCanonical : (occurrence.context.fill normalized).Canonical,
          ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill normalized),
            Equates occurrence normalized targetCanonical
              targetExternalTwoEnded
```

The single public Exposure equivalence owner used by the selected-site case is:

```lean
theorem Erasure.Exposure.equates
    (description : Erasure.Description outer)
    (occurrence : Occurrence description.source source)
    (materialCanonical : description.material.Canonical)
    (exposedCanonical :
      (occurrence.context.fill
        (exposedRegion description materialCanonical)).Canonical)
    (exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposedRegion description materialCanonical))) :
    Equates occurrence (exposedRegion description materialCanonical)
      exposedCanonical exposedExternalTwoEnded
```

Its arbitrary retained-host construction uses symmetric structural pin phases
internally. The public result exposes both directions; callers needing one
direction project the corresponding component.

The five private relational definitions have these exact roles and indices:

- `normalizedRegionStrict`: an occurrence of `result.renameWires rename` is
  nonemptily equivalent in both directions to the same rename of the reviewed
  `normalizedRegion` output.
- `normalizedItemsStrict`: the arbitrary-host dispatcher relates the exact
  `Region.adjoinAt hostLocals hostItems (result.renameWires rename)` endpoint
  to the exact `normalizedItems` endpoint.
- `normalizedItemsSupportedStrict`: the structural item-sequence recursion at
  a canonical retained host whose inherited wires are incident.
- `normalizedItemWithTailStrict`: the exact leading-item phase while retaining
  the caller's actual tail.
- `normalizedItemStrict`: the item constructors, including the direct
  `equatesIdentityBoundary` selected case and nested cut recursion.

`StrictEquates` is the shared nonempty internal relation used for presentation
transport. `StrictEquates.toEquates` supplies the public optional
`ReflTransGen` result. Mutual termination is measured by
`5 * sizeOf sites + rank`, where ranks strictly decrease across the two
same-site dispatcher/worker handoffs and constructor recursion decreases
`sizeOf sites`.

## Construction coverage

- Selected atoms are presented from renamed instantiation syntax to mapped
  ports, call `equatesIdentityBoundary` directly, and present the normalized
  target back through `RegionIso`/`OpenDiagramIso`.
- Retained atoms, identities, and nil use `StrictEquates.refl`.
- Cuts use `Occurrence.nest`, the composed `DiagramContext`, and symmetric
  forward/reverse `transGen_iso` composition.
- Cons and current-level siblings use the existing conjoin/adjoin
  presentations. One structural support-pin batch establishes the host
  invariant used by the shared Exposure owner; no second context syntax is
  introduced.
- The public theorem returns `(normalizedItems pattern evidence sites).1` and
  its dependent evidence directly. Canonicality and external two-endedness
  come from the reviewed `normalizedItems_scope` preservation owner.

No reachability proof is transported through endpoint equality. Structural
equalities are used only to prove validity facts or construct explicit region
and open-diagram presentations.

## Theorem-driven RED / GREEN

Every definition in the owning theorem's dependency closure elaborated before
RED. In particular, all five mutually recursive relational definitions were
kernel checked with no proof hole.

RED command:

```text
lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

With only `EqualityNormalization.normalizeItemsEquates` proved by `sorry`, the
command exited `0` and reported:

```text
VisualProof/Rule/Completeness/Comprehension/Compiler.lean:3634:8: warning: declaration uses `sorry`
```

The theorem statement was unchanged for GREEN. Its kernel-checked proof then
made the same focused command exit `0` with no output.

## Validation

All commands ran from
`/home/ahart/Documents/VisualProofAssistant/.worktrees/signature-indexed-wires`.

Focused elaboration:

```text
lake env lean VisualProof/Rule/Completeness/Reachability.lean
lake env lean VisualProof/Rule/Completeness/Erasure/Exposure.lean
lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

Each command exited `0` with no output.

Proof-hole audit:

```text
rg -n '\b(sorry|admit)\b|^\s*axiom\b' VisualProof
```

Exit status `1`; no matches.

Forbidden added-line audit covered `cast`, `Eq.rec`, `occurrenceCongr`, direct
`ArgumentProjection`, `WireSever`, and polarity-XOR spellings. It found no
matches in the three task-owned production diffs.

The private-helper caller audit found at least one production reference in
addition to every new private declaration. The Exposure surface audit reports
one public equivalence owner, `Erasure.Exposure.equates`; the Compiler surface
adds only `EqualityNormalization.normalizeItemsEquates`.

Diff hygiene:

```text
git diff --check
```

Exit status `0`.

Full package build:

```text
lake build
```

Exit status `0`; 77 jobs completed successfully. The replayed warnings are the
existing unused-simp warnings in `VisualProof/Diagram/Isomorphism.lean` and
`VisualProof/Diagram/Scope/Rename.lean`; all touched modules are warning-free
under their focused checks.

## Self-review

- The output endpoint and dependent evidence are generated solely by the
  reviewed private normalization fold.
- No caller supplies an endpoint, edit, partition, rule description, `Step`,
  reachability witness, discharge object, result object, or callback.
- Sibling layout changes are explicit isomorphism presentations, and every
  selected site reaches the single Exposure equivalence owner through the
  reviewed one-site theorem.
- Cut recursion uses the exact composed occurrence and both symmetric chains;
  it introduces no directed deep rule or polarity dispatch.
- The final public relation is exactly bidirectional
  `Relation.ReflTransGen Step` at the caller's occurrence.
- Every new private helper has an immediate production caller. Shared
  reachability operations live at their cross-module ownership boundary.
- No synthetic examples or theorem fixtures were added.
- No BoundaryPlan or public compiler integration was changed.

## Concerns

No correctness blocker remains. The nonempty `StrictEquates` layer realizes
unchanged cases by a symmetric Vacuity round trip so later endpoint
presentations can be transported kernel-safely; the public theorem projects
this to the requested optional reachability relation.
