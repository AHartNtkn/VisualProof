# Concrete Subgraph Algebra and Exact Matcher — Design Specification

**Date:** 2026-07-13  
**Status:** decision-ready  
**Foundation:** `/tmp/visualproof-foundation-20260713-lean-formalization-v8.xml`

## 1. Problem

The checked concrete graph now has one exact well-formedness authority, total
elaboration into the intrinsic diagram calculus, and identifier-invariant
semantics. The next slice must formalize the finite subgraph operations on which
rule application depends:

- checked selections and their exact closure;
- open extraction with ordered wire and binder interfaces;
- removal with dense-identifier transport;
- capture-avoiding splice, including attachment aliasing;
- the extract-remove-splice inverse up to concrete isomorphism;
- an independent declarative occurrence relation; and
- an executable exact matcher that is sound and complete for that relation.

This design does not claim general logical completeness. Exact finite structural
matching is the only completeness result in scope. Beta-eta matching remains a
separate certificate- or fuel-bounded mode with correspondingly conditional
claims.

## 2. Evidence and Independent Inputs

The design was checked against four independent architecture passes and a fifth
adversarial pass. The available execution environment supported four concurrent
agents including the lead, so the fifth perspective was obtained as a deliberately
different second pass rather than a fifth simultaneously running agent.

- **Tide / mosaic / hinge / seed / telescope:** one private open/closed compiler,
  ordered-boundary-preserving open isomorphism, checked selection, a central
  decomposition certificate, and intrinsic-only semantics.
- **Delta / loom / orchard / prism / anchor:** proof-independent surgery with
  explicit finite reindexing, shared closure, and exact finite enumeration.
- **Forge / estuary / lattice / compass / membrane:** decomposition as a proof
  technique rather than a graph or matcher authority; explicit survivor maps;
  transitive attachment closure; pure binder-prefix interfaces; and an independent
  occurrence relation.
- **Cairn:** hostile review of representation boundaries and theorem ownership;
  it identified the required derived occurrence/extraction compatibility theorem.
- **Ember / canopy / braid / sluice / astrolabe:** a materially different
  decomposition-first matcher proposal. Its shared-cut insight is retained for
  surgery; defining or enumerating matches through cuts is rejected as the
  reference matcher because it would make matcher completeness depend on the
  extraction algorithm.

Local controlling evidence was the existing Lean concrete and intrinsic layers,
the TypeScript selection/extraction/removal/splice/matcher modules, and
`../diagegraph`'s finite-function enumeration proofs. The latter contributes an
enumerate-then-filter proof pattern, not its graph class, DPO layer, canonicalizer,
or Mathlib dependencies.

## 3. Considered Architectures

### 3.1 Direct port of the TypeScript operations

This would translate the current mutable/string-identifier algorithms and prove
post-hoc properties about their outputs. It has the shortest superficial path to
behavioral correspondence, but it would duplicate closure logic, conceal dense
`Fin` reindexing, and preserve operational accidents as formal authorities. It is
rejected.

### 3.2 General categorical graph rewriting

This would import a general DPO/pushout framework and encode VisualProof diagrams
as a specialization. It gives elegant generic laws but introduces a second graph
representation, a much larger proof surface, and no direct solution for lexical
relation binders or the existing intrinsic semantics. It is rejected for this
formalization boundary.

### 3.3 Hybrid checked algebra with an independent matcher

The selected architecture has three one-way authorities:

1. the existing total concrete graph plus checked, computable subgraph operations;
2. an independent declarative occurrence relation over finite maps; and
3. the existing intrinsic calculus as the only semantic authority.

A deterministic decomposition certificate is the shared owner of selection
closure, extraction, and removal data. It is not a second graph representation,
not the definition of occurrence, and not assigned a denotation. The exact matcher
enumerates finite candidate maps and filters by the declarative occurrence
predicate. This architecture makes the surgery inverse tractable without making
matching circular.

## 4. Shared Finite Infrastructure

The generic finite utilities currently private to concrete elaboration move to a
Std-only `VisualProof.Data.Finite` module. The old location is migrated completely;
there is no compatibility re-export.

The module owns:

- `allFin`, `filterFin`, `indexOf?`, and finite sequence enumeration;
- exhaustive enumeration of functions between finite types, with membership iff;
- filtered-fiber survivor maps and their inverse laws;
- the project-owned `FiniteEquiv`, moved from the private compiler if it is needed
  outside elaboration; and
- deterministic bounded transitive closure for relations on `Fin n`.

Every executable output is computed from raw finite data. Proofs certify the
output; they never choose identifiers, representatives, orderings, or maps.

## 5. Checked Open Concrete Elaboration

`OpenConcreteDiagram` retains its ordered, repeatable concrete boundary list. Its
external intrinsic classes are the first-occurrence `eraseDups` of that list.
Repeated positions therefore name the same external class. Root-scoped wires not
present in the boundary remain root-local existential wires.

The private compiler is generalized only at the root partition:

- closed elaboration supplies no ambient wires and all root-scoped wires as local;
- open elaboration supplies exposed boundary classes as ambient wires and the
  remaining root-scoped wires as local; and
- all descendant compilation continues to use the existing exact lexical
  contexts.

There remains one private compilation authority. Public APIs are total checked
elaboration, open denotation through `Core.denoteOpen`, and proof-irrelevance.

`OpenConcreteIso` extends `ConcreteIso` by pointwise preservation of ordered
boundary occurrences. Plain graph isomorphism is intentionally insufficient for
an interface. Open isomorphism transports well-formedness, open elaboration, and
open denotation.

## 6. Selection and Closure

A raw `SelectionRequest d` contains only:

- an anchor region;
- direct child subtree roots;
- direct nodes; and
- explicitly selected anchor-scoped wires.

`SelectionRequest.Valid` requires duplicate-free lists, exact direct ownership,
and endpoints of every explicit wire to belong to selected nodes. A checker
returns a checked request and proves exact acceptance. This checker validates an
operation input; it does not compete with graph well-formedness.

Closure is computed, never stored as user input:

- selected regions are descendants of selected direct child roots;
- selected nodes are direct selected nodes or nodes owned by selected regions;
- internal wires are scoped in selected regions or explicitly selected; and
- touching wires are noninternal wires incident to selected nodes.

In particular, an anchor-scoped wire is not promoted to internal merely because
all its endpoints are selected. This caller-controlled distinction is part of the
existing selection semantics.

The closure API proves membership iff its defining predicate, duplicate freedom,
internal/touching disjointness, and exact ownership and incidence consequences.

## 7. Lossless Decomposition

For a checked host and checked selection, `decompose` computes one certificate
containing:

- the closure;
- a checked frame obtained by removal;
- a checked open fragment obtained by extraction;
- boundary attachments ordered with the fragment boundary;
- a pure outermost-first binder-stub chain and aligned host binder targets;
- survivor maps for retained regions, nodes, and wires; and
- origin maps for copied fragment regions, nodes, and wires.

The frame and fragment separately are not lossless. The decomposition, including
the seam and provenance, is. Removal and extraction are projections from it, so
they cannot disagree about the closure, touching wires, or external binders.

The raw frame, fragment, maps, and interfaces are computed first. The checked
constructor proves their laws and well-formedness; there is no second
"decomposition validator" and no proof-selected executable field.

Dense `Fin` reconstruction is explicit. Survivor/origin receipts replace any
temptation to preserve counts with tombstones, retain obsolete identifiers, or
recover a canonical naming after the fact.

## 8. Binder Interface

Extraction may externalize bound-relation dependencies only through a typed,
transparent interface. Its binder stubs form a pure prefix chain above the
fragment body:

- every layer is a bubble;
- layers are ordered outermost first;
- each layer has exactly the next layer or body as its sole child;
- prefix layers contain no nodes;
- prefix layers contain no nonboundary wires; and
- the exposed binder arity and every rebound atom agree.

This is intentionally narrower than arbitrary bubble deletion. It exactly models
extraction-generated stubs and permits capture-avoiding reattachment. Peeling the
prefix yields an intrinsic body under a relation context; reattachment is an
existing `RelationRenaming` to exact host `RelVar`s. Recursive lifting under nested
bubbles provides capture avoidance. No second term or relation syntax is added.

## 9. Splice

A checked splice input contains a checked frame, checked open pattern, site,
position-indexed wire attachments, binder interface, and aligned binder targets.
Admissibility proves wire visibility, site enclosure, binder kind/arity agreement,
and the pure-prefix contract.

If two boundary positions name the same pattern wire, their host attachments
generate an equivalence relation. Splice computes its finite transitive closure,
coalesces each host attachment class deterministically, and then copies pattern
material into the coalesced frame. Distinct pattern boundary identities are allowed
to attach to the same host wire; boundary maps are not injective. Pattern internal
wires remain injective and disjoint from newly exposed boundary structure.

The two computational phases are explicit:

1. `coalesceFrame`, which performs only the host wire quotient; and
2. `plugRaw`, which block-copies and reindexes pattern material.

The scope of a merged host wire is the deterministic outermost scope of its class,
with a fixed finite tie-break. Endpoints from every host class member are merged;
each pattern boundary wire contributes its endpoints exactly once.

The primary structural law is:

```lean
theorem reassemble_original_iso
    (d : Decomposition host selection) :
  ConcreteIso (plugOriginalFragment d) host.val
```

The user-facing extract-remove-splice inverse follows by projection. It is an
isomorphism, not identifier equality or fingerprint equality.

## 10. Intrinsic Subgraph Algebra and Semantics

Concrete surgery has no interpreter. Its meaning is established by a commuting
square into existing intrinsic operations.

At a common lexical context, `Region.conjoin` block-sums local wires and appends
renamed item sequences. It has denotation-as-conjunction and associative,
commutative, and unit laws up to existing `RegionIso`. Existing
`DiagramContext.fill`, wire renaming/substitution, and relation renaming remain the
only context and substitution language.

After elaboration, a host decomposition has the form, up to intrinsic isomorphism:

```text
outerContext.fill (frameAtAnchor.conjoin selectedFragment)
```

Removal fills the same context with `frameAtAnchor`. General splice first renames
the frame by the host attachment quotient, substitutes the pattern boundary, peels
and renames the binder prefix, and conjoins the result at the site. The quotient
must precede ordinary boundary substitution: a `BoundaryAssignment` alone cannot
map one pattern boundary class to two distinct pre-quotient host wires.

The central bridge is an elaboration-isomorphism theorem for checked splice. Its
denotation theorem follows only from intrinsic conjoin, context, substitution,
renaming, and isomorphism laws. The inverse semantic corollary follows through
`ConcreteIso.denote_iff`.

## 11. Declarative Occurrence

`OccurrenceData` is proof-free finite data: a host site plus material-region,
node, and wire maps. Ordered boundary attachments are derived from the wire map;
they are not duplicated stored state.

`ScopedOccurrence pattern host options candidate : Prop` is independent of
selection, extraction, and decomposition. It states directly:

- the effective pattern root maps to the site;
- root content uses subset semantics;
- every mapped proper descendant uses exact reflected child, node, and internal
  wire content;
- constructors, parents, ownership, bubble arities, term shapes, named identities,
  named arities, atom binders, and positional arguments are preserved;
- material region and node maps are injective;
- internal wire maps are injective and disjoint from boundary images;
- internal incidence is exact modulo endpoint permutation;
- boundary incidence is included in the host attachment, whose scope encloses the
  site;
- repeated boundary positions preserve one boundary-wire identity; and
- distinct boundary identities may share a host attachment.

Endpoint list order is nonsemantic. Term ports and relation arguments are
positional. Exact structural term equality is the mode covered by unconditional
matcher completeness. Seeded attachment restrictions are options on the relation.
The formal reference relation permits unseeded bare boundaries to range over the
finite visible host wires; the current optimized TypeScript refusal is not elevated
to mathematical impossibility.

The two authorities are connected by a derived compatibility theorem. From an
occurrence, its finite image determines a checked selection and decomposition;
extraction of that selection corresponds to the pattern by material isomorphism,
ordered boundary incidence, and binder-interface agreement. Conversely, such a
compatible extraction reconstructs an occurrence:

```lean
theorem occurs_iff_extraction_compatible :
  ScopedOccurrence pattern host options candidate ↔
    ExtractionCompatible
      pattern
      (decompose host (candidate.occurrenceSelection))
      candidate
```

`ExtractionCompatible` permits several pattern boundary identities to cover one
seam attachment, so it is not incorrectly reduced to ordinary graph isomorphism.
The theorem is derived in both directions and does not define occurrence or make
extraction a matcher. It ensures matcher and surgery cannot silently disagree.

## 12. Exact Matcher

The reference matcher enumerates all finite candidate sites and maps, then filters
them with the decidable occurrence predicate. It deliberately favors a transparent
completeness oracle over performance:

```lean
def exactMatcher ... : List OccurrenceData

theorem exactMatcher_sound :
  o ∈ exactMatcher pattern host options →
    ScopedOccurrence pattern host options o

theorem exactMatcher_complete :
  ScopedOccurrence pattern host options o →
    o ∈ exactMatcher pattern host options

theorem mem_exactMatcher_iff :
  o ∈ exactMatcher pattern host options ↔
    ScopedOccurrence pattern host options o
```

The reference result is not deduplicated by footprint; literal candidate
membership gives the strongest and simplest completeness statement. A later
optimized matcher may use refinement, incidence-determined maps, symmetry
breaking, or footprint deduplication only after proving an extensional existence
equivalence with the reference matcher.

Beta-eta matching remains a separate interface using checked conversion
certificates or bounded search. Its completeness theorem is conditional on the
supplied certificates or absence of exhausted comparisons; it cannot inherit the
unconditional exact-structural theorem.

## 13. Authoritative Validation

The slice is complete only when:

- open elaboration preserves ordered aliases, hidden root locals, proof
  irrelevance, open isomorphism, and open denotation;
- the selection checker has exact acceptance and closure membership iff the
  intended predicates;
- decomposition produces checked frame and fragment plus exact seam/provenance;
- general splice handles transitive attachment aliases and preserves
  well-formedness;
- extract-remove-splice reconstructs the host by `ConcreteIso`;
- concrete operations commute with the intrinsic algebra and their denotation
  theorems use no concrete interpreter;
- `mem_exactMatcher_iff` is proved for the independent occurrence relation;
- `occurs_iff_extraction_compatible` proves exact agreement between the matcher
  relation and the ordered wire/binder interface consumed by surgery;
- examples cover root subset versus nested exactness, endpoint permutation,
  repeated boundary aliases, distinct boundary identities sharing an attachment,
  unseeded bare boundaries, external binders, and transitive host-wire coalescence;
- clean focused and full Lean builds pass;
- `#print axioms` shows only accepted Lean quotient/propositional principles; and
- source scans find no `sorry`, `admit`, custom axiom, alternate graph authority,
  second validator/interpreter, canonical-string shortcut, tombstone IDs, or
  generated Lake artifacts.

## 14. Implementation Boundaries

Work is split into two theorem-first plans:

1. shared finite infrastructure, checked open elaboration, selection,
   decomposition, removal/extraction, intrinsic conjoin, splice, and inverse; then
2. independent occurrence, exhaustive exact matching, soundness/completeness, and
   its compatibility theorems with the subgraph algebra.

Within Lean tasks, the initial red state is a correctly stated theorem admitted
temporarily with `sorry`. Initial module scaffolding does not pretend to have a
separate TDD red phase. Every task removes its admissions before commit, then uses
type checking, axiom inspection, and semantic examples as validation.
