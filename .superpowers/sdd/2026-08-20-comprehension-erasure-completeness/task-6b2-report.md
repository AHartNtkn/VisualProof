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

## Fix round 1: authoritative validity, exposure, ownership, and reflexivity

Date: 2026-08-21

**GREEN.** This section records the current contracts and supersedes the
earlier surface and unchanged-case descriptions above.

### Current owning contracts

The selected-site owner now has the approved three-explicit-argument call
shape. The retained host is inferred from the occurrence index, and callers
supply no target endpoint or validity proof:

```lean
theorem EqualityNormalization.equatesIdentityBoundary
    {boundary outer arguments : List Sig}
    (pattern : OpenDiagram arguments)
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (ports : Vars (outer ++ hostLocals) arguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (Instantiation.instantiate pattern ports)) source) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Instantiation.instantiate
              (identityBoundary pattern) ports))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Instantiation.instantiate
                (identityBoundary pattern) ports))),
        Equates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Instantiation.instantiate (identityBoundary pattern) ports))
          targetCanonical targetExternalTwoEnded
```

It computes hosted scope preservation, the exact normalized combined
canonical proof, and external-two-ended validity internally. The
`selectedAtom` branch calls it directly as
`equatesIdentityBoundary pattern mappedPorts presentedOccurrence`.

The single public Exposure owner preserves the Task 2 premises and returned
validity witnesses while strengthening reachability symmetrically:

```lean
theorem Erasure.Exposure.equates
    (description : Rule.Erasure.Description outer)
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    ∃ materialCanonical : description.material.Canonical,
      ∃ exposedCanonical :
          (occurrence.context.fill
            (exposedRegion description materialCanonical)).Canonical,
        ∃ exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (exposedRegion description materialCanonical)),
          Equates occurrence
            (exposedRegion description materialCanonical)
            exposedCanonical exposedExternalTwoEnded
```

After destructuring the returned validity witnesses, Task 2's forward
reachability is `equivalent.1`; the all-sites fold uses both components. There
is one public Exposure equivalence theorem and no parallel forward wrapper.

### Private ownership and exact unchanged dispatch

`Occurrence.nest`, `StrictEquates` and its algebra, structural pin generation,
`contextPins`, pin incidence/canonical facts, and
`adjoinPinsEquatesNonempty` are private Compiler implementation details.
`Reachability.lean` is byte-identical to the reviewed `f4dfb727` base.

The five private relational definitions now accept positive selected-site
evidence before entering strict recursion. `normalizedItemsEquates` first
computes `itemsHaveSelection sites`:

- when it is false, `normalizedItems_eq_of_noSelection` proves that the
  normalized region is definitionally unchanged, the normalization phase is
  exactly `⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩`, and no
  presentation, support-pin, worker, or target-pin phase runs;
- the one `StrictEquates.refl` at this public boundary bridges only the
  caller's arbitrary `Occurrence.host_iso` to its exact filled endpoint;
- when it is true, positive selection proofs route recursion only through
  selected items or selected descendants. Unchanged head/tail siblings are
  proved equal and skipped. Nil, retained atoms, and retained identities do
  not create strict cycles;
- structural pins are batched only when `outer ++ hostLocals` is nonempty.
  The empty ambient branch establishes canonicality directly and invokes the
  selected worker without pin/cycle/unpin phases.

The remaining internal `StrictEquates.refl` use is local to
`strictEquates_of_equates`: the public Exposure result is optional, while an
actual selected phase must be nonempty to transport a distinct endpoint
presentation. No unchanged normalization path uses that bridge.

### Theorem-driven RED / GREEN receipts

Exposure RED, with only the owning `Exposure.equates` proof admitted:

```text
$ lake env lean VisualProof/Rule/Completeness/Erasure/Exposure.lean
VisualProof/Rule/Completeness/Erasure/Exposure.lean:3264:8: warning: declaration uses `sorry`
```

Exit status `0`. Its dependencies and strengthened statement elaborated.

The selected-site owner RED, with only
`EqualityNormalization.equatesIdentityBoundary` admitted:

```text
$ lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
VisualProof/Rule/Completeness/Comprehension/Compiler.lean:3392:8: warning: declaration uses `sorry`
```

Exit status `0`.

After the exact unchanged dispatcher and all five relational definitions
were complete, the public all-sites RED was repeated with only
`normalizeItemsEquates` admitted:

```text
$ lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
VisualProof/Rule/Completeness/Comprehension/Compiler.lean:4921:8: warning: declaration uses `sorry`
```

Exit status `0`. Restoring each owning proof produced GREEN with no proof
holes.

### Validation receipts

Focused elaboration:

```text
$ lake env lean VisualProof/Rule/Completeness/Reachability.lean
$ lake env lean VisualProof/Rule/Completeness/Erasure/Exposure.lean
$ lake env lean VisualProof/Rule/Completeness/Comprehension/Compiler.lean
```

All three exited `0` with no output.

Task 2/current Exposure contract audit:

```text
$ rg -n '^theorem equates$|\(erasedCanonical :|∃ materialCanonical|Equates occurrence' \
    VisualProof/Rule/Completeness/Erasure/Exposure.lean
```

Exit status `0`; it found the public owner at line 3264, erased-target
canonicality at line 3269, returned material validity at line 3274, and the
symmetric result at line 3282.

Surface audits:

```text
$ rg -n 'Exposure\.(derives|equatesEmptyHost)' VisualProof
$ rg -n '^(theorem|def|structure) (StrictEquates|contextPins|contextPins_incidence_nonempty|pinnedHostCanonical|adjoinPinsEquatesNonempty|pinnedHost_incidence_nonempty|Occurrence\.nest)' \
    VisualProof/Rule/Completeness/Comprehension/Compiler.lean \
    VisualProof/Rule/Completeness/Erasure/Exposure.lean \
    VisualProof/Rule/Completeness/Reachability.lean
```

Both exited `1` with no matches. Caller scans found direct production uses for
every task-owned private helper.

Proof-hole and forbidden-construction audits:

```text
$ rg -n '\b(sorry|admit)\b|^\s*axiom\b' VisualProof
$ git diff --unified=0 f4dfb727 -- \
    VisualProof/Rule/Completeness/Reachability.lean \
    VisualProof/Rule/Completeness/Erasure/Exposure.lean \
    VisualProof/Rule/Completeness/Comprehension/Compiler.lean | \
    rg '^\+.*\b(cast|Eq\.rec|occurrenceCongr|Argument\.Projection|WireSever|xor|Xor)\b'
```

Both exited `1` with no matches.

Diff hygiene and the full build:

```text
$ git diff --check
$ lake build
```

`git diff --check` exited `0`. `lake build` exited `0` with all 77 jobs
successful. Its only output was the established replayed unused-simp warnings
in `Diagram/Isomorphism.lean` and `Diagram/Scope/Rename.lean`; all touched
modules remain warning-free under focused elaboration.

### Fix-round self-review and concerns

- The approved selected-site owner has no caller-supplied normalized endpoint
  or validity premises.
- Exposure preserves the original erased-target premise/result contract and
  provides symmetric reachability through one public theorem.
- General strict algebra and every structural pin fact are private to the
  Compiler implementation that uses them.
- The unchanged result is proven from the exact evidence/sites indices and
  uses a literal reflexive normalization phase before any selected machinery.
- Selected sibling and cut composition retain the accepted explicit
  Region/ItemSeq presentations and symmetric occurrence composition.
- No BoundaryPlan or compiler integration code is in scope.

No correctness concern or validation blocker remains.
