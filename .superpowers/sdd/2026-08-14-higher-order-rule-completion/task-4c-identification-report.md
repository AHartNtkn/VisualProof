# Task 4C report — higher-order identity identification

## Status

DONE

Baseline: `69137280fbee7697c20b15d4c815eb89e472f380`

## Result

Implemented identification in three independent modules:

- `VisualProof/Rule/Identification.lean`
- `VisualProof/Rule/Executable/Identification.lean`
- `VisualProof/Rule/Soundness/Identification.lean`

The rule is one ungated bidirectional operation at one retained identity node
and one signature.  It supports locally owned absorbed wires at any recursive
region and root external absorbed wires, including an exact ordered boundary
partition.

## Representation and architecture

The selected identity uses one source-indexed `PortExpansion` witness.  Its
`retain` and `absorb` constructors describe the exact arbitrary physical
interleaving and multiplicity of retained and absorbed ports.  Retained ports
occur exactly once and in order, every fresh absorbed wire is required to occur,
and no removed absorbed port is copied onto the survivor.  The survivor remains
an exact retained port of the selected identity.

The exact selected identity is a canonical item-sequence prefix.  Existing
`ItemSeqIso` permutations cover arbitrary physical node placement without
widening `ItemIso.identity` or introducing a second syntax representation.

All other incidences use the existing `ItemSeq.PortPartition` as the sole
incidence-distribution traversal.  `Region.Port.IsNonIdentity`,
`Item.Port.IsNonIdentity`, and `ItemSeq.Port.IsNonIdentity` are proof-only
classifiers over an already selected port witness.  They accept atom head and
argument incidences and recursively selected cut-descendant incidences, but no
identity-node incidence.

The reusable `PortPartition` owner also provides exactly two internal-wire maps
and their owner-path laws:

- `Region.InternalWire.partitionOutput`
- `ItemSeq.InternalWire.partitionOutput`
- `Region.InternalWire.ownerPath_partitionOutput`
- `ItemSeq.InternalWire.ownerPathFrom_partitionOutput`

These follow the existing partition recursion and do not perform another
operation-local traversal.  Identification adds only the selected-prefix
head/tail elimination and uses `DiagramContext.mapInternalWire` for contextual
lifting.

No target diagram or rule witness is stored in an executable index.  No search,
normalization, rehoming, alternate diagram representation, stored scope, `HEq`,
cast reconciliation, or raised elaboration limit was added.

## Relation and applicability

Local data appends a positive number of distinct fresh current-region local
wires.  Each fresh wire must receive:

- one selected-identity port through the exact `PortExpansion`; and
- one exact non-identity away incidence selected through the active
  `ItemSeq.PortPartition`.

The away condition excludes the selected identity and every other identity
node.  Local retained external support is preserved exactly so the existing
context replacement theorem derives both endpoint `Canonical` and
`ExternalTwoEnded` validity.

Open data appends a positive number of distinct external wires.  The selected
identity is typed over `external ++ locals`; its designated survivor is proved
to be the retained external survivor, while its other retained ports may be
external or local.  Every fresh external wire receives a selected-identity port
and either an ordered boundary occurrence or an exact non-identity body
incidence.  Exact collapsed and exposed boundary partitions and their
surjectivity obligations construct both valid open endpoints.

The relation is the disjunction of contextual symmetric local identification,
forward open identification, and reverse open identification.  General
source/target isomorphism closure, both target-isomorphism closure directions,
and explicit symmetry are kernel checked.

## Executable coverage

`ForwardIndex` has four direct source-indexed constructors:

- local exposure;
- local collapse;
- open exposure;
- open collapse.

Each constructor stores the exact selected node, retained survivor, structural
port expansion, away port partition, and root boundary partition when
applicable.  `runForward` and `runBackward` construct the endpoint directly.
They do not discover an occurrence, search syntax, normalize a diagram, or
store a target diagram.

`forward_exact` and `backward_exact` prove iff coverage up to target
isomorphism in both directions.

## Semantic and scope proofs

`NodeData.denote_items_iff_of_rename` is the shared one-point lemma for local
and open identification.  The active port partition relates the away syntax,
while the exact selected-node expansion shows all absorbed values equal the
retained survivor value.  It proves the converse by projecting every retained
port back through the structural expansion.

`Local.sound_iff`, `Open.Data.denote_region_iff_of_rename`,
`Open.sound_iff`, `Identification.sound`, and
`Identification.sound_iff` establish semantic equivalence for local, exact
open, and full relation presentations.

Surviving-wire scope preservation is explicit for both required exact
presentation forms:

- `Local.existsPresentedWire_scopePath` maps every collapsed local contextual
  presentation wire to the exposed presentation with identical computed
  `scopePath`;
- `Open.existsPresentedWire_scopePath` maps every collapsed exact root
  presentation wire to the exposed presentation with identical computed
  `scopePath`.

External wires remain root-scoped.  Current-region local wires remain owned by
the same region.  Nested wires use the shared PortPartition transport and retain
the same numeric owner path; local occurrences lift that fact through the
existing diagram context map.  Exact presentation paths are stated directly;
arbitrary endpoint isomorphisms may permute item positions.

## Theorem-driven RED/GREEN

All definitions in each owning theorem's dependency closure were complete
before RED.

- Relation RED elaborated only the intended endpoint, isomorphism, and scope
  theorem proofs with admissions.
- Executable RED elaborated `forward_exact` and `backward_exact` over complete
  index and runner definitions.
- Soundness RED elaborated the owning semantic theorem declarations over the
  complete one-point definitions.
- GREEN has no `sorry` or other admissions in the complete dependency closure.

No fixture module, redundant `example`, or synthetic test theorem was added.

## Ownership and size

| File | Total LOC | Task-owned change |
|---|---:|---:|
| `VisualProof/Diagram/PortPartition.lean` | 694 | +136 |
| `VisualProof/Rule/Identification.lean` | 676 | +676 |
| `VisualProof/Rule/Executable/Identification.lean` | 230 | +230 |
| `VisualProof/Rule/Soundness/Identification.lean` | 513 | +513 |
| **Task-owned total** |  | **1555** |

The local/open relation, executable, and soundness towers total 1419 LOC,
within the 2100 LOC architecture gate.

## Validation

Strict warning-as-error checks passed independently:

```text
lake env lean -DwarningAsError=true VisualProof/Diagram/PortPartition.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Identification.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Executable/Identification.lean
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Identification.lean
```

Focused build passed:

```text
lake build VisualProof.Rule.Identification \
  VisualProof.Rule.Executable.Identification \
  VisualProof.Rule.Soundness.Identification
Build completed successfully (27 jobs).
```

Lean C code generation emitted public symbols for both runners:

```text
VisualProof.Rule.Identification.runForward
VisualProof.Rule.Identification.runBackward
```

Trust inspection reported only the standard logical axioms `propext` and
`Quot.sound` for exactness, endpoint validity, both scope theorems, semantic
equivalence, and the generic owner-path laws.

All four authority audits passed.  Admission and forbidden-pattern scans found
no `sorry`, `admit`, custom axiom, `HEq`, cast API, target diagram in an index,
search, normalization, stored scope, or raised limit.  `git diff --check`
passed.

## Concerns

None.
