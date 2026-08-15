# Task 4B report — higher-order identity presentation invariance

## Status

DONE

Baseline: `9b8b8239035817ccd88b7b8c92c18bdf1067a479`

## Result

Implemented the presentation-invariance identity family in three independent
modules:

- `VisualProof/Rule/Presentation.lean`
- `VisualProof/Rule/Executable/Presentation.lean`
- `VisualProof/Rule/Soundness/Presentation.lean`

The local operation replaces positive-arity identity-node configurations of
one signature at one region. It retains the same locals and exact non-selected
item sequence, preserves the selected wire support, and requires equality of
the generated finite equivalence relation. The computed target is admitted
only when every locally owned wire remains rooted with at least two
incidences; existing context validity owners lift that exact local condition
to global `Canonical` and `ExternalTwoEnded` evidence.

## Representation and architecture

`Presentation.Node` stores `extraArity : Nat` and ports indexed by
`Fin (extraArity + 1)`. Nullary nodes are therefore unrepresentable in this
rule and remain exclusively in vacuity.

`Presentation.Configuration` is a flat `List Node`. It is replacement data,
not syntax, a graph, or a recursive diagram representation. Its `items`
function emits the sole active `ItemSeq` syntax.

The exact local source and computed target have the form:

```text
Region.mk locals (retained.append configuration.items)
```

This canonical suffix form does not restrict physical item placement.
`Occurrence.host_iso` uses the existing `ItemSeqIso` permutation to align an
arbitrarily placed source configuration with its suffix presentation, while
the relation's target isomorphism closes over arbitrary physical target
placement. The permutation never reconciles different node counts: each
physical endpoint and its corresponding suffix presentation have the same
count, while the rule itself owns the source-to-target count change.

The suffix boundary also keeps every retained cut at the same item index.
Consequently, surviving nested wires have a direct structural map through the
unchanged retained prefix, with no path casts or reindexing authority.

No target diagram, syntax search, occurrence discovery, normalization,
stored scope, global wire table, second recursive syntax, component/assembly
authority, `HEq`, cast reconciliation, or raised elaboration limit was added.

## Relation

`Configuration.SameSupport` compares the exact finite set of typed wire
indices occurring in the two configurations. Positive node arity means every
selected node touches that support; same support means every selected wire
occurs on both sides.

`Configuration.Generated` is the proof-only reflexive, symmetric, transitive
closure of co-membership in one identity node. `SameRelation` is pointwise
iff equality of those closures. It is used only as the mathematical equality
predicate; runners do not evaluate it to find or normalize configurations.

`Applicability` contains:

- same selected-wire support;
- the same generated finite equivalence relation;
- `RootedTwo` evidence for every locally owned wire in the computed target.

`replacementValidity` proves the exact endpoint `Canonical` and
`ExternalTwoEnded`. Equal support first proves per-wire hole-incidence
nonemptiness is unchanged. `DiagramContext.replaceCanonical` then preserves
ancestor DCA placement and local floors, and
`OpenDiagram.externalTwoEnded_of_nonempty_iff` preserves external-wire
validity.

The contextual rule is ungated, polarity-independent through symmetry, and
bidirectional. It provides source- and target-isomorphism closure plus an
explicit symmetry theorem.

## Executable coverage

`ForwardIndex` contains only:

- exact retained regional syntax;
- the exact source configuration;
- replacement configuration data;
- an exact source `Occurrence`;
- applicability evidence for the computed endpoint.

It contains no target `OpenDiagram`, search state, or rule witness.
`runForward` constructs the target directly from the replacement suffix and
the endpoint validity theorem. `runBackward` is an ordinary computable runner
over the same source-indexed index family.

`forward_exact` and `backward_exact` prove iff coverage of the relation up to
target isomorphism in both directions. Reverse-orientation exactness derives
the reverse local rooted guard from the already-established relation endpoint
validity; it does not discover an occurrence or inspect syntax.

## Semantic and scope proofs

`Configuration.Denotes.generated_eq` proves that a denoting identity
configuration equates every pair in its generated relation.
`denotes_of_generated_eq` proves the converse. Equal generated relations
therefore yield equivalent configuration denotations.

`denote_region_iff` retains the same local witnesses and non-selected
conjuncts while replacing only the equivalent identity configuration.
`Local.sound_iff` and `Presentation.sound_iff` expose local and open-diagram
semantic equivalence. No inhabitedness axiom is needed because all selected
nodes have positive arity.

Wire survival and DCA scope preservation are explicit in both directions:

- `Local.existsPresentedWire_scopePath` maps every source wire to a target
  wire with exactly the same computed `scopePath`;
- `Local.existsSourceWire_scopePath` maps every target wire back to a source
  wire with exactly the same computed `scopePath`.

The maps preserve external wires definitionally and preserve internal owner
paths through the unchanged retained prefix and existing
`DiagramContext.mapInternalWire` owner.

## Theorem-driven RED/GREEN

All definitions in each production theorem's dependency closure were
complete before its RED check.

- Relation RED: `Presentation.lean` elaborated with only production theorem
  proofs admitted.
- Executable RED: both exactness declarations elaborated over complete index
  and runner definitions.
- Soundness RED: semantic declarations elaborated over complete denotation
  definitions.
- GREEN: all three modules elaborate with kernel-checked proofs and no
  `sorry`.

No fixture module, redundant `example`, or synthetic test theorem was added.

## Validation

Strict warning-as-error checks passed independently:

```text
lake env lean -DwarningAsError=true VisualProof/Rule/Presentation.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Presentation.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Presentation.lean
```

Focused build passed:

```text
lake build VisualProof.Rule.Presentation \
  VisualProof.Rule.Executable.Presentation \
  VisualProof.Rule.Soundness.Presentation
Build completed successfully (23 jobs).
```

Lean code generation compiled both public runners:

```text
VisualProof.Rule.Presentation.runForward
VisualProof.Rule.Presentation.runBackward
```

Trust inspection reported only the standard logical axioms `propext` and
`Quot.sound` for:

- `forward_exact`
- `backward_exact`
- `replacementValidity`
- both scope-preservation theorems
- `sound_iff`

Admission, authority, and forbidden-pattern scans found no `sorry`, `admit`,
custom axiom, `HEq`, cast reconciliation, target diagram in an index, search,
normalization, stored scope, or raised limit. `git diff --check` passed.

## Concerns

None.
