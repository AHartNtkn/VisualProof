# Comprehension and Erasure Completeness Implementation Plan

**Goal:** Prove that `Comprehension` and `Erasure` are subrelations of
`Relation.TransGen Step`, using the current primitive calculus without adding
executors or changing rule semantics.

**Public theorems:**

```lean
theorem Comprehension.complete
    (step : Comprehension source target) :
    Relation.TransGen Step source target

theorem Erasure.complete
    (step : Erasure source target) :
    Relation.TransGen Step source target
```

## Controlling design

- Use `Relation.TransGen Step` at the public boundary and
  `Relation.ReflTransGen Step` only for internal phases that may be empty.
- Represent internal derivations by a proposition indexed by an actual
  `Occurrence`, its polarity, its exact target region, and proofs that the
  filled target is canonical and externally two-ended. Do not define a
  derivability relation over bare regions.
- State the comprehension compiler telescope-parametrically from its first
  leaf theorem. The telescope is a predicate over actual `Region` expressions
  and pending binders, not a new diagram datatype.
- State every constructor theorem parametrically in polarity. Instantiate the
  direction only when injecting a primitive step.
- Directed wire primitives act only at the comprehension binder's home
  occurrence. Any step applied below that home must be symmetric. This is a
  maintained invariant of the proof. Equality plumbing below cuts therefore
  needs context composition but no polarity-XOR dispatch.
- Each intermediate's validity is proved by the phase that constructs it.
  Inspect existing executable proofs for relevant arguments, but place any
  reusable structural lemma in its owning Diagram or relational rule module.
  Completeness must not depend on runners, validators, indices, or
  decidability as proof authority.
- Every helper theorem lands with an immediate production-theorem caller.

## Target module layout

```text
VisualProof/Rule/Completeness/Reachability.lean
VisualProof/Rule/Completeness/Comprehension/Telescope.lean
VisualProof/Rule/Completeness/Comprehension/Compiler.lean
VisualProof/Rule/Completeness/Comprehension.lean
VisualProof/Rule/Completeness/Erasure/Exposure.lean
VisualProof/Rule/Completeness/Erasure.lean
VisualProof/Rule/Completeness.lean
```

The existing relation modules remain unchanged except for imports needed to
publish the completed theorems.

## Task 1: Establish the minimal reachability kernel

**Files:**

- Create `VisualProof/Rule/Completeness/Reachability.lean`.
- Create the initial
  `VisualProof/Rule/Completeness/Comprehension/Telescope.lean` with the blank
  pattern theorem as the immediate client.

**Work:**

1. Define an occurrence-indexed internal derivation proposition. Its target
   must be the exact `OpenDiagram` obtained by filling the occurrence context
   with the target region and the supplied validity proofs.
2. Prove endpoint-isomorphism transport for `Relation.TransGen Step` and
   `Relation.ReflTransGen Step` by induction using `Step.iso`.
3. Prove the compositions actually needed by the blank client:
   `ReflTransGen` before a `TransGen` core, a `TransGen` core before
   `ReflTransGen`, and consecutive occurrence-indexed phases.
4. Inject one `Contextual` primitive at the occurrence's current polarity.
5. Define the minimal actual-region telescope predicate in the final form
   required by compound patterns: it records pending constructor binders and
   the fully instantiated endpoint without introducing new diagram syntax.
6. State and GREEN the polarity-parametric blank-pattern telescope theorem
   using `Ends.spawn`. This is the first caller of the reachability kernel and
   fixes the generalized leaf signature used by later tasks.

Do not add context nesting or polarity-composition lemmas in this task.

**Validation:**

```bash
lake env lean VisualProof/Rule/Completeness/Reachability.lean
lake env lean VisualProof/Rule/Completeness/Comprehension/Telescope.lean
rg -n "sorry" VisualProof/Rule/Completeness
lake build
```

**Commit:** `feat(lean): establish completeness reachability kernel`

## Task 2: GREEN the erasure exposure phase

This is an early effort and exact-shape gate, not a semantic feasibility gate.
Failure means replacing the exposure construction; guarded Ends absorption
already supplies the required final semantic move.

**File:** Create
`VisualProof/Rule/Completeness/Erasure/Exposure.lean`.

**Production theorem:** Given an `Erasure.Description` and the validity of its
actual occurrence endpoints, construct a `ReflTransGen Step` from the directly
renamed material presentation to a region isomorphic to one exact
`Comprehension.Instantiation.instantiate` block.

**Work:**

1. Prove that source canonicality extracts canonicality of the material's
   internal locals through `Region.spliceAt` and its renaming.
2. Define a support-completed open pattern:
   - one boundary position for every `materialWire`;
   - the ordered identity boundary map;
   - the original material body;
   - one unary support pin for each external material wire with no body
     incidence.
3. Prove boundary surjectivity, body canonicality, and
   `OpenDiagram.ExternalTwoEnded` for that pattern.
4. Prove the one-wire exposure theorem:
   - insert one Vacuity pin that will become the boundary equality;
   - insert the support pin when the material external is unused;
   - use Identification to expose a fresh local and redirect exactly the
     chosen structural ports;
   - preserve all previously exposed wires and the required host support.
5. Construct the desired exposed away-region first and obtain its partition
   from `ItemSeq.exists_partition_of_renamed` or
   `Region.exists_partition_of_renamed`. This must cover noninjective
   `wireMap`; structural port occurrences, not wire values, select each group.
6. Fold the one-wire theorem over `materialWires`.
7. Prove the fold endpoint is isomorphic to
   `Instantiation.instantiate supportPattern ports`.

The production theorem must cover repeated signatures, repeated `wireMap`
images, unused external wires, nested cuts, and arbitrary material locals.

**Validation:**

```bash
lake env lean VisualProof/Rule/Completeness/Erasure/Exposure.lean
rg -n "sorry" VisualProof/Rule/Completeness/Erasure/Exposure.lean
lake build
```

**Commit:** `feat(lean): expose erasure material as comprehension instance`

## Task 3: Define the telescope-parametric comprehension compiler

**File:** Extend
`VisualProof/Rule/Completeness/Comprehension/Telescope.lean`.

**Work:**

1. Define a predicate over actual regions representing a sequence of pending
   constructor binders and its final fully instantiated region by extending
   the minimal predicate from Task 1. It must not duplicate `Region`,
   `Instantiation`, or `Transform` syntax.
2. State the strengthened compiler mutually over existing
   `Instantiation.RegionResult`, `ItemsResult`, and `ItemResult` evidence.
   The theorem parameters must include:
   - the pending actual-region telescope;
   - the actual occurrence and endpoint validity;
   - polarity;
   - exact endpoint isomorphisms required by the next constructor.
3. Preserve a nonempty `TransGen` core whenever a comprehension application
   is being compiled; optional telescope preparation may use `ReflTransGen`.
4. Use the blank theorem from Task 1 directly as the first mutual branch;
   changing its statement is a design failure to resolve before adding more
   leaves.

This task exists to prevent leaf theorems from being restated after the first
compound pattern.

**Validation:** focused elaboration, `sorry` scan, then `lake build`.

**Commit:** `feat(lean): define comprehension telescope compiler`

## Task 4: GREEN the comprehension leaf constructors

**File:** Create
`VisualProof/Rule/Completeness/Comprehension/Compiler.lean`.

Prove each theorem in the generalized polarity-parametric telescope form:

1. Blank through Ends.
2. Singleton atom through FormalApplication.
3. Identity item through IdentityLeaf.

For each leaf:

- construct the shared `Transform` edit from the existing instantiation site
  evidence;
- construct every intermediate canonicality and two-endedness proof;
- inject the primitive only at the binder's home occurrence;
- make the resulting theorem an immediate branch of the mutual compiler.

Before proving new validity lemmas, inspect the corresponding
`Executable/WirePrimitive` proof for arguments about the same transform
output. Move any generally reusable structural statement to its owning
Diagram or relational rule module before importing it into completeness.

**Validation:** focused elaboration after every GREEN theorem, then full build.

**Commit:** `feat(lean): compile comprehension leaf patterns`

## Task 5: GREEN the structural pattern constructors

**File:** Extend
`VisualProof/Rule/Completeness/Comprehension/Compiler.lean`.

Prove in order:

1. Cut bodies using the child telescope result and CutShape.
2. Item-sequence conjunction using both child results and ParallelShape.
3. Pattern-local wires using Arity, including the required pin supplied by its
   current relation.
4. Boundary order, repetition, and omission using ArgumentPermutation,
   ArgumentDuplicate, and ArgumentProjection.

At each rung, the induction hypothesis must consume and produce the actual
pending telescope endpoints. Do not patch endpoint mismatches with casts or a
parallel representation; strengthen the relevant induction principle over
the existing syntax.

**Validation:** focused elaboration after each constructor, then full build.

**Commit:** `feat(lean): compile structural comprehension patterns`

## Task 6: Compile deep equality plumbing

**Files:**

- Extend `VisualProof/Rule/Completeness/Reachability.lean`.
- Extend `VisualProof/Rule/Completeness/Comprehension/Compiler.lean`.

**Work:**

1. Prove occurrence nesting using `DiagramContext.comp` and `fill_comp`, with
   canonicality and external-two-endedness threaded from the actual endpoints.
2. Prove lifting for the symmetric rules used below the binder home:
   Identification, Vacuity, and Presentation if presentation normalization is
   required by the exact identity shape.
3. Record in theorem hypotheses that every deep rule is symmetric. Do not add
   a polarity-XOR dispatch unless a directed deep rule is actually discovered.
4. Compile `Instantiation.Equalities` at arbitrary selected sites under cuts.
5. Fold this plumbing into the telescope compiler's boundary phase.

**Tripwire:** If a directed rule is required below the binder home, stop and
reassess the architecture before adding polarity-composition machinery.

**Validation:** focused elaboration, `sorry` scan, then full build.

**Commit:** `feat(lean): compile comprehension equality plumbing`

## Task 7: Prove `Comprehension.complete`

**File:** Create `VisualProof/Rule/Completeness/Comprehension.lean`.

**RED theorem:** State the public theorem exactly as shown at the top of this
plan, with `sorry` as its sole incomplete proof in the dependency closure.

**GREEN proof:**

1. Unpack the `Contextual` comprehension witness.
2. Invoke the polarity-parametric telescope compiler once.
3. Compose optional preparation and cleanup around its nonempty core.
4. Transport the packaged source and target isomorphisms.

**Validation:**

```bash
lake env lean VisualProof/Rule/Completeness/Comprehension.lean
rg -n "sorry" VisualProof/Rule/Completeness
lake build
```

**Commit:** `feat(lean): prove comprehension step completeness`

## Task 8: Prove exact two-site duplication

**File:** Create `VisualProof/Rule/Completeness/Erasure.lean`.

**Work:**

1. Build the `NestedOccurrence` selecting the single exact instantiation block
   produced by the exposure phase.
2. Choose Iteration freshening that copies the block's local wires while
   retaining its actual application ports.
3. Prove `Iteration.freshPins` is empty for this copy. Each fresh pattern
   external has:
   - one equality incidence; and
   - either a material-body incidence or the support pin.
   All other copied locals inherit canonical rooted-two evidence.
4. Prove the Iteration endpoint is region-isomorphic to the exact conjunction
   of two `Instantiation.instantiate` blocks. Construct and name the required
   region/OpenDiagram isomorphism for conjoin order and local-wire naming.
5. Construct `Comprehension.Instantiates` for those two sites.
6. Prove the quantified relation wire has exactly two depth-zero rooted
   incidences.

**Validation:** focused elaboration, `sorry` scan, then full build.

**Commit:** `feat(lean): construct two-site erasure comprehension`

## Task 9: Prove erasure factorization and completeness

**File:** Complete `VisualProof/Rule/Completeness/Erasure.lean`.

**Proposed factor theorem to create:**

```lean
theorem Erasure.factor
    (step : Erasure source target) :
    ∃ specialized quantified,
      Relation.ReflTransGen Step source specialized ∧
      Comprehension specialized quantified ∧
      Relation.ReflTransGen Step quantified target
```

Adjust namespace qualification if necessary to distinguish the `step`
argument from `Rule.Step`.

**Work:**

1. Compose exposure with exact two-site Iteration.
2. Insert the `Comprehension` relation proved by the two-site witness.
3. Construct guarded `Ends.absorb` for the two selected atoms. Both are at
   depth zero inside the relation binder, so both guards are `.positive`.
4. Assemble the positive contextual direction.
5. Assemble the negative direction by selecting the converse of each local
   symmetric phase and the polarity-parametric comprehension/Ends directions.
   Do not reverse an arbitrary `Step` chain.
6. GREEN `Erasure.factor`.
7. Compose the factor's reflexive phases around
   `Comprehension.complete` to GREEN the strict public `Erasure.complete`.

The mandatory comprehension segment supplies the nonempty core even when the
material is blank; no artificial no-op cycle is needed.

**Validation:** focused elaboration, `sorry` scan, then full build.

**Commit:** `feat(lean): prove erasure step completeness`

## Task 10: Publish and validate the completeness layer

**Files:**

- Create `VisualProof/Rule/Completeness.lean` importing both public theorems.
- Import it from `VisualProof.lean` only after every dependency is GREEN.

**Validation:**

```bash
rg -n "sorry" VisualProof/Rule/Completeness VisualProof/Rule/Completeness.lean
lake build
git status --short
```

Kernel elaboration of the owning theorems and the full build are
authoritative.

**Commit:** `feat(lean): publish completeness theorems`

## Named risks and responses

1. **Telescope endpoint alignment.** Addressed by stating the compiler in its
   strengthened telescope-parametric form before proving atom and identity
   leaves.
2. **Exposure bookkeeping under noninjective `wireMap`.** Addressed by the
   early whole-boundary exposure theorem and existing partition-existence
   lemmas. A failure changes the exposure construction, not the erasure
   reduction's semantic basis.
3. **Intermediate validity.** Every phase constructs validity for its exact
   output. No checker or executor evidence enters the theorem statements.
4. **Deep-site polarity.** Only symmetric rules may run below the binder home.
   Context composition is scheduled explicitly; directed deep steps trigger
   architectural reassessment.
5. **Iteration pin residue.** Prove support completion makes `freshPins` empty
   before claiming the copied block is a second exact instantiation.
6. **Iteration endpoint shape.** Name and prove the isomorphism between
   Iteration's copy order/local naming and the two-site Instantiates source.
7. **Strict closure.** Keep optional phases reflexive internally and compose
   them around the mandatory comprehension core.
