# Concrete Subgraph Algebra Implementation Plan

> **For agentic workers:** Use `superpowers:subagent-driven-development` task by
> task. Each implementation task receives an independent specification review and
> code-quality review before it is accepted.

**Goal:** Implement checked open concrete elaboration, exact selection closure,
lossless extraction/removal decomposition, capture-avoiding splice, intrinsic
subgraph semantics, and the extract-remove-splice inverse up to `ConcreteIso`.

**Architecture:** The existing concrete graph remains the only finite graph
authority and the intrinsic calculus remains the only semantic authority. One
deterministic decomposition owns the shared closure, seam, and provenance behind
extraction/removal/splice. Proofs certify computed data and never select it.

**Design:**
`docs/superpowers/specs/2026-07-13-concrete-subgraph-and-matcher-design.md`

**Tech stack:** Lean 4.30.0, Std only.

## Global Constraints

- Lean work is theorem-first. State the public theorem before proving it; a
  transient `sorry` may mark that exact obligation during the task. No admission,
  custom axiom, or unsafe declaration may remain at review or commit.
- Initial module/type scaffolding has no artificial test-first red phase.
- `ConcreteDiagram.WellFormed` remains the graph validity authority. Selection and
  splice admissibility validate operation inputs only.
- Raw executable outputs depend only on raw finite inputs. Do not eliminate `Prop`
  to obtain data.
- Do not add a second graph syntax, validator, concrete interpreter, canonical
  form, tombstone identifier, compatibility re-export, or default/fallback result.
- Endpoint order is never semantic. Boundary order, term ports, and relation
  arguments are semantic.
- Preserve touching wires even when removal leaves them with zero endpoints.
- Every accepted task runs focused build, relevant examples, axiom inspection,
  forbidden-token scan, and `git diff --check`.

---

### Task 1: General finite infrastructure migration

**Files:**
- Create: `VisualProof/Data/Finite.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration/Finite.lean`
- Modify imports under: `VisualProof/Diagram/Concrete/Elaboration/`
- Modify: `VisualProof.lean`

**Produces:** One reusable Std-only finite enumeration/indexing authority.

- [x] Move `allFin`, `filterFin`, `indexOf?`, and `sequenceFin` with all existing
  proofs into `VisualProof.Data.Finite`.
- [x] Add enumeration of `Fin n → Fin m` and prove literal membership iff.
- [x] Add duplicate-free filtered-fiber indexing and explicit forward/backward
  survivor maps with inverse laws.
- [x] Add deterministic reflexive-symmetric-transitive closure over a decidable
  relation on `Fin n`; prove it is the least equivalence containing the generators.
- [x] Migrate every elaboration consumer to the new owner and delete the old
  declarations. The old module may remain only if it owns genuinely
  elaboration-specific facts; it must not re-export moved names.
- [x] Add small theorem examples for empty/nonempty function spaces, a deleted
  finite fiber, and a three-edge transitive closure.
- [x] Run focused/full builds and commit independently.

---

### Task 2: Checked open elaboration

**Files:**
- Create: `VisualProof/Diagram/Concrete/Open.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration/Compile.lean`
- Modify: `VisualProof/Diagram/Concrete/Elaboration.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** Stable boundary classes, hidden root locals, and one private
open/closed compiler authority.

- [ ] Define first-occurrence exposed root wires and filtered hidden root wires.
  Prove boundary positions map to equal external classes iff they name equal
  concrete wires, external-class surjectivity, and the exact root-local
  characterization.
- [ ] Generalize the private root compilation entry to take a deterministic
  ambient/local partition. Keep all recursive compiler definitions private.
- [ ] Recover existing closed elaboration as the empty-external specialization and
  prove its public result is unchanged.
- [ ] Expose total checked open elaboration into the existing `OpenDiagram`, with
  proof irrelevance and computation theorems.
- [ ] Define open concrete denotation only through intrinsic `denoteOpen`.
- [ ] Add examples for repeated boundary aliases, an unexposed root bare wire, and
  an empty boundary agreeing with closed elaboration.
- [ ] Inspect public axioms and private visibility; commit independently.

---

### Task 3: Ordered open concrete isomorphism

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Concrete/Open.lean`

**Produces:** `OpenConcreteIso` and open elaboration equivariance.

- [ ] Define `OpenConcreteIso` as a `ConcreteIso` whose wire equivalence preserves
  every ordered boundary position pointwise.
- [ ] Prove reflexivity, symmetry, transitivity, open well-formedness transport,
  exposed-class equivalence, and hidden-root-wire equivalence.
- [ ] Extend the synchronized private equivariance proof to open root contexts.
- [ ] Prove open elaborations intrinsically isomorphic with boundary positions
  commuting, then prove open denotation invariance.
- [ ] Add a nontrivial region/node/wire permutation whose endpoint order is
  reversed and whose boundary contains a repeated wire.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 4: Checked selection and exact closure

**Files:**
- Create: `VisualProof/Diagram/Concrete/Subgraph/Selection.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph.lean`
- Modify: `VisualProof/Diagram/Concrete.lean`

**Produces:** Raw requests, exact operation-input validation, and one computed
closure.

- [ ] Define `SelectionRequest`, `SelectionRequest.Valid`, structured
  `SelectionError`, checked selections, and `checkSelection`.
- [ ] Prove input preservation, checker soundness/completeness, and exact
  acceptance.
- [ ] Compute selected regions, selected nodes, internal wires, and touching wires
  using finite filters.
- [ ] Prove membership iff the intended predicates, duplicate freedom,
  internal/touching disjointness, endpoint consequences, and closure monotonicity.
- [ ] Prove an unselected anchor-scoped wire remains touching even if every one of
  its endpoints is selected; uncontacted bare anchor wires remain outside closure.
- [ ] Add examples for direct node, whole child subtree, explicit anchor wire,
  all-endpoints-but-not-explicit, and crossing wire cases.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 5: Mapped removal and extraction decomposition

**Files:**
- Create: `VisualProof/Diagram/Concrete/Subgraph/Reindex.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Decomposition.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Remove.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Extract.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph.lean`

**Produces:** One deterministic lossless cut with checked projections.

- [ ] Define reusable region/node/wire survivor and origin receipts using filtered
  finite fibers and block embeddings.
- [ ] Compute removal: delete selected regions/nodes/internal wires, trim selected
  endpoints from touching wires, retain every other wire including newly bare
  touching wires, and compact all carriers.
- [ ] Compute extraction: copy selected material beneath a fresh sheet, create
  root-scoped boundary stubs for touching wires in deterministic incidence order,
  and expose aligned original host attachments.
- [ ] Derive every external binder used by selected atoms, prove they form an
  ancestry chain, and create a pure outermost-first bubble prefix with aligned
  host targets and exact arities.
- [ ] Define the raw decomposition from the shared closure and the checked
  decomposition that proves frame/fragment well-formedness, provenance exactness,
  seam exactness, and binder-prefix exactness.
- [ ] Expose removal and extraction only as projections of the checked
  decomposition.
- [ ] Add examples covering a trimmed-to-bare touching wire, repeated boundary
  occurrences, nested external binders, and dense identifier compaction.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 6: Intrinsic conjunction and scoped frame laws

**Files:**
- Create: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/Context.lean`
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof.lean`

**Produces:** The intrinsic operation needed to describe selection replacement
without a second context language.

- [ ] Define `Region.conjoin` by block-extending the two local-wire spaces and
  appending their renamed item sequences.
- [ ] Prove denotation iff conjunction.
- [ ] Prove left/right unit, associativity, and commutativity up to existing
  `RegionIso`, using item-sequence permutation rather than list equality.
- [ ] Prove naturality under wire and relation renaming.
- [ ] Prove `DiagramContext.fill` respects conjoin and the relevant renamings at
  the hole.
- [ ] Add calculation examples with bare locals and reordered conjuncts.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 7: Checked splice and finite attachment pushout

**Files:**
- Create: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph.lean`

**Produces:** Executable coalescing and plugging with checked well-formed output.

- [ ] Define raw splice data, pure binder-interface view, structured input errors,
  admissibility, and exact checked-input acceptance.
- [ ] Generate host-wire equations only from two boundary positions naming the
  same pattern wire. Prove distinct boundary wires may share one attachment
  without generating an additional equation.
- [ ] Compute the equivalence closure, deterministic representative, merged
  endpoint collection modulo permutation, and outermost scope of each host class.
- [ ] Implement `coalesceFrame` and prove its quotient/survivor receipts exact.
- [ ] Implement `plugRaw` using finite blocks; copy every pattern boundary wire's
  endpoints exactly once and internal wires injectively.
- [ ] Prove checked splice preserves all eleven concrete well-formedness clauses.
- [ ] Add examples for a repeated alias joining two host wires, transitive alias
  closure, distinct boundary wires sharing a host wire, and binder reattachment.
- [ ] Build, inspect axioms, and commit independently.

---

### Task 8: Inverse and semantic commuting square

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Decomposition.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Semantics.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph.lean`

**Produces:** The structural inverse and semantics of general replacement.

- [ ] State `reassemble_original_iso` before its proof and construct its region,
  node, and wire equivalences from survivor/origin receipts.
- [ ] Prove endpoint preservation with `List.Perm`/membership and prove the
  original-fragment splice induces no nontrivial attachment quotient.
- [ ] Derive the public extract-remove-splice inverse up to `ConcreteIso`.
- [ ] Prove checked decomposition elaborates, up to intrinsic isomorphism, to a
  `DiagramContext.fill` of frame conjoined with fragment.
- [ ] Prove binder-prefix peeling and capture-avoiding relation reattachment using
  existing relation renaming.
- [ ] Prove general splice elaboration commutes with host-wire quotient, boundary
  substitution, relation renaming, conjoin, and context fill.
- [ ] Derive splice and inverse denotation results solely through intrinsic
  semantics and `ConcreteIso.denote_iff`.
- [ ] Build focused/full project, inspect theorem axioms, scan forbidden
  authorities and admissions, and commit independently.

---

### Task 9: Independent integration review and conformance

**Files:** Modify only defects found in Tasks 1-8 and umbrella imports.

- [ ] Review responsibility ownership, executable proof independence, endpoint
  permutation, alias generation, binder capture avoidance, and open/closed compiler
  uniqueness against the design and foundation record.
- [ ] Run a clean full build and all example modules.
- [ ] Inspect axioms of open elaboration, selection exact acceptance,
  well-formedness preservation, inverse, splice commuting square, and denotation.
- [ ] Scan for `sorry`, `admit`, project axioms, duplicate finite utilities,
  alternate validators/interpreters, compatibility aliases, canonicalization, and
  generated Lake artifacts.
- [ ] Append a scoped `<conformance>` section to the foundation record without
  changing its pre-action sections.
- [ ] Commit review repairs and conformance separately.
