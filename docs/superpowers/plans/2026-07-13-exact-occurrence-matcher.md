# Exact Occurrence Matcher Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` task by
> task, with independent specification and code-quality reviews.

**Goal:** Define a decidable scoped-hypergraph occurrence relation independent of
subgraph surgery and implement an exhaustive Std-only matcher with literal
soundness and completeness, then prove exact compatibility with extraction and
splice interfaces.

**Architecture:** `OccurrenceData` is proof-free finite map data. `Occurs` states
the graph laws directly. The reference matcher enumerates every finite candidate
and filters by `decide Occurs`; it is intentionally not optimized or deduplicated.
Surgery and matching remain independent authorities joined by a proved
bidirectional compatibility theorem.

**Prerequisite:** The concrete subgraph algebra plan is complete.

**Design:**
`docs/superpowers/specs/2026-07-13-concrete-subgraph-and-matcher-design.md`

**Tech stack:** Lean 4.30.0, Std only.

## Global Constraints

- The exact relation uses structural term equality only. Fuel, beta-eta
  uncertainty, normalization, certificates, and symmetry pruning are absent from
  this slice.
- Boundary wire maps may be noninjective. Internal wire maps are injective and
  disjoint from boundary images.
- Root content is subset matching; every proper mapped subtree is exact.
- Endpoint preservation is membership/permutation, never list order.
- Matcher results contain raw candidates, not proof-selected witnesses.
- Completeness is literal list membership for every candidate satisfying `Occurs`.
- No admission, custom axiom, canonical graph, or optimized fallback remains at
  review or commit.

---

### Task 1: Material support and occurrence data

**Files:**
- Create: `VisualProof/Diagram/Concrete/Matcher/Occurrence.lean`
- Create: `VisualProof/Diagram/Concrete/Matcher.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** Proof-free finite candidate maps and exact pattern material support.

- [ ] Define the effective body container after peeling a checked terminal-body
  binder spine and finite material-region support excluding the sheet and every
  explicitly designated proxy. No bubble is transparent by shape.
- [ ] Define `OccurrenceOptions` with optional site and boundary attachment seeds.
- [ ] Define `OccurrenceData` with site, a map whose domain is only material
  regions, a node map, and a wire map. Derive the body-container location as the
  site, keep external binder images separate from material locations, and derive
  ordered attachments from the pattern boundary and wire map.
- [ ] Define helper predicates for mapped ownership, positional endpoint mapping,
  nested reflection, attachment visibility, and seed agreement.
- [ ] Give every helper a decidable instance and theorem-owned computation
  examples.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 2: Independent declarative occurrence relation

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Matcher/Occurrence.lean`

**Produces:** `ScopedOccurrence` with direct graph-theoretic laws.

- [ ] State the full relation before proving its decidability: derived
  body-container/site location,
  root subset, nested exact reflection, region kinds/parents/arities, node
  ownership/constructors, exact structural terms, named identity/arity, internal
  material binders and exact external proxy binders, positional arguments, wire
  scopes, exact internal
  incidence, included boundary incidence, injection/disjointness, attachment
  visibility, repeated aliases, and seed agreement.
- [ ] Prove the relation is decidable using only finite data and the exact
  structural term equality already present.
- [ ] Prove projection lemmas for every conjunct so later matcher and bridge proofs
  do not unfold the entire relation.
- [ ] Add positive/negative examples for root subset versus nested exactness,
  endpoint permutation, binder mismatch, named identity mismatch, repeated boundary
  aliases, distinct boundary identities sharing an attachment, and bare unseeded
  boundary attachment.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 3: Exhaustive reference matcher

**Files:**
- Create: `VisualProof/Diagram/Concrete/Matcher/Exact.lean`
- Modify: `VisualProof/Diagram/Concrete/Matcher.lean`

**Produces:** Literal exhaustive enumeration and the exact iff theorem.

- [ ] Enumerate candidate sites and every finite region, node, and wire function
  using `VisualProof.Data.Finite`; apply option seeds only as decidable filters.
- [ ] Define `exactMatcher` as enumeration followed by `decide ScopedOccurrence`.
  Do not deduplicate, canonicalize, infer incidence-determined maps, or prune
  symmetries.
- [ ] Prove candidate-enumeration membership iff each constituent map belongs to
  its finite function enumeration.
- [ ] Prove `exactMatcher_sound`, `exactMatcher_complete`, and
  `mem_exactMatcher_iff` for literal `OccurrenceData` membership.
- [ ] Derive emptiness iff no occurrence and a decidability theorem for existence.
- [ ] Add executable examples containing multiple literal witnesses and verify
  every declared witness is present.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 4: Occurrence–extraction compatibility

**Files:**
- Create: `VisualProof/Diagram/Concrete/Matcher/Compatibility.lean`
- Modify: `VisualProof/Diagram/Concrete/Matcher.lean`

**Produces:** The noncircular bridge proving matcher and surgery agree exactly.

- [ ] Compute `occurrenceSelection` from an occurrence candidate's material image
  and prove it is a valid selection when `ScopedOccurrence` holds.
- [ ] Define `ExtractionCompatible` using material concrete isomorphism plus
  ordered boundary coverage and ordered binder-interface agreement. Permit several
  pattern boundary identities to cover one extracted seam wire.
- [ ] Prove every occurrence yields a compatible decomposition/extraction.
- [ ] Prove every compatible extraction yields the original declarative
  occurrence, including root subset and nested exact reflection.
- [ ] Prove `occurs_iff_extraction_compatible`.
- [ ] Derive that splicing a matched pattern through its reported attachments is
  accepted by the checked splice interface.
- [ ] Add diagonal-boundary and external-binder examples that would fail if the
  bridge used plain graph isomorphism or unordered interfaces.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 5: Conditional beta-eta matching boundary

**Files:**
- Create: `VisualProof/Diagram/Concrete/Matcher/BetaEta.lean`
- Modify: `VisualProof/Diagram/Concrete/Matcher.lean`

**Produces:** A sound extension boundary without weakening exact completeness.

- [ ] Define a separate candidate-check result whose term comparisons are proved
  by conversion certificates or explicitly reported as exhausted/undecided.
- [ ] Prove certificate-backed matches imply the semantic beta-eta node relation.
- [ ] Prove bounded-search soundness only for successful comparisons.
- [ ] State completeness only conditionally on certificates or a no-exhaustion
  hypothesis. Do not alter `mem_exactMatcher_iff`.
- [ ] Add nonnormalizing/exhausted examples showing no negative conclusion follows.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 6: Independent integration review and conformance

**Files:** Modify only defects found in Tasks 1-5 and umbrella imports.

- [ ] Review that `ScopedOccurrence` does not unfold or existentially quantify
  extraction/decomposition, while compatibility is proved both ways.
- [ ] Review boundary noninjectivity, internal injectivity, endpoint permutation,
  subset/exact scope split, binder order, and unseeded bare boundaries.
- [ ] Run a clean full build and all matcher examples.
- [ ] Inspect axioms of occurrence decidability, matcher soundness/completeness,
  compatibility, and beta-eta soundness.
- [ ] Scan for admissions, project axioms, deduplication, canonicalization,
  unproved pruning, proof-bearing result data, and generated Lake artifacts.
- [ ] Append a scoped `<conformance>` section to the foundation record without
  altering pre-action sections; commit review repairs and conformance.
