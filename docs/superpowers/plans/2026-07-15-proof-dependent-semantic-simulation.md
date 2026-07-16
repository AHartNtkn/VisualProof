# Proof-Dependent Semantic Simulation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rebuild the shared Lean compiler simulation so every accepted rule,
including boundary-coalescing theorem application and scope-changing wire join,
can receive a public successful-receipt soundness proof.

**Architecture:** Keep structural compiler correspondence unconditional, but move
all target semantic witness choices after the active source denotation. Restrict
context extension to exact contexts produced by the compiler, retain one shared
recursive traversal, and migrate every rule consumer before deleting the old
witness model.

**Tech Stack:** Lean 4, Lake, the existing intrinsic/extrinsic diagram
formalization, Vitest/TypeScript correspondence checks.

## Global Constraints

- Do not introduce `sorry`, `admit`, or a custom axiom.
- Do not claim general proof-system completeness.
- Preserve exact finite matcher completeness and conditional beta-eta matcher
  completeness as separate results.
- There must be one compiler-simulation authority; no compatibility alias,
  parallel witness API, or rule-local recursive fallback may remain.
- Lean proof development uses theorem statements and typechecking as its feedback
  loop; conventional TDD is not required and no redundant test theorem should be
  added merely to create a RED state.
- Preserve unrelated worktree changes and stage only task-owned files.

---

### Task 1: Rebuild the proof-dependent witness core

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Elaboration/Simulation.lean`

**Interfaces:**
- Consumes: `ContextIndexRelation`, `extendedEnvironment`, `rootEnvironment`,
  `ItemSeqSimulation`, and `RegionSimulation`.
- Produces: proof-dependent `DirectionalLocalWitness`,
  `DirectionalRootWitness`, `DirectionalBoundaryWitness`, and exact-context
  `ConcreteSemanticSimulation.extendContext`.

- [ ] **Step 1: Change local witness dependency order**

Define `DirectionalLocalWitness` with `model`, `named`, `relEnv`, `sourceItems`,
and `targetItems`. In the forward branch, accept `sourceLocal` and
`denoteItemSeq ... sourceItems` before returning `targetLocal` and extended
environment agreement. In the backward branch, accept `targetLocal` and the
target item denotation before returning the source local and agreement.

- [ ] **Step 2: Change root witness dependency order**

Give `DirectionalRootWitness` the compiled source and target item sequences. Its
forward and backward branches must receive the active item-sequence proof before
constructing the opposite hidden-wire environment and combined agreement.

- [ ] **Step 3: Change ordered boundary dependency order**

Give `DirectionalBoundaryWitness` the source and target open bodies, model, and
named environment. The forward branch receives
`denoteRegion ... sourceAssignment.classes ... source.body` before returning the
target assignment and agreement; the backward branch is dual.

- [ ] **Step 4: Restrict context extension**

Change `ConcreteSemanticSimulation.extendContext` so construction of the
extended `ContextWitness` requires:

```lean
(sourceContext.extend region).Exact region →
(targetContext.extend (regionMap region)).Exact (regionMap region) →
ContextWitness (sourceContext.extend region)
  (targetContext.extend (regionMap region))
```

Thread these exactness proofs through every invocation. Do not retain an
unrestricted helper with the old type.

- [ ] **Step 5: Reorder the three lifting theorems**

Update `finishRegion_denote`, `finishRoot_denote`, and `denoteOpen_lift` so each
destructs the active denotation first, passes the resulting item/body proof to
the witness, then applies item/body simulation and reconstructs the target.

- [ ] **Step 6: Update shared recursive traversal**

Pass compiled source/target item sequences and their compile equations into
`ConcreteSemanticSimulation.localWitness`. Construct the exact-context witness
only after both exactness proofs are available. Preserve
`compileRegion_denote` and `compileRoot_denote` as the only recursive traversal.

- [ ] **Step 7: Typecheck the core**

Run:

```bash
lake build VisualProof.Diagram.Concrete.Elaboration.Simulation
```

Expected: exit 0 with no declaration using `sorry`, `admit`, or a custom axiom.

### Task 2: Migrate existing conversion and wire-sever simulations

**Files:**
- Modify: `VisualProof/Rule/Soundness/Equational.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`

**Interfaces:**
- Consumes: Task 1 proof-dependent witnesses and exact-context extension.
- Produces: `applyConversion_sound` and the existing `applyWireSever_sound` on
  the rebuilt shared API.

- [ ] **Step 1: Migrate conversion context construction**

Retain the green regular-region and root partition lemmas. Replace its
unrestricted extension and pre-denotation environment helpers with witnesses
that accept exactness and the active compiled-item proof. Complete
`RootContextSimulation`, ordered boundary transport, and
`applyConversion_sound`.

- [ ] **Step 2: Migrate wire sever**

Adapt `severSimulation`, its root context, and `severBoundaryWitness` to the new
quantifier order. Preserve ordered repeated boundary positions and ensure the
public theorem still has type:

```lean
SuccessfulReceiptSound context input orientation (.wireSever wire keep)
```

- [ ] **Step 3: Remove displaced recursion**

Delete conversion- or sever-owned semantic recursion now discharged by
`ConcreteSemanticSimulation`. Retain only local rule laws and structural map
proofs.

- [ ] **Step 4: Typecheck both consumers**

Run:

```bash
lake build VisualProof.Rule.Soundness.Equational
lake build VisualProof.Rule.Soundness.Structural
```

Expected: both exit 0.

### Task 3: Prove canonical theorem replacement with unequal alias partitions

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Named.lean`
- Modify: `VisualProof/Rule/Soundness/HighLevel.lean`

**Interfaces:**
- Consumes: canonical remove-then-splice presentation, the rebuilt shared
  simulation, `theoremPayload_forward_local`,
  `theoremPayload_backward_local`, and `contextualizeCitation`.
- Produces: `applyTheorem_sound` for both orientations and both local implication
  directions.

- [ ] **Step 1: Add generic two-input splice presentation**

Prove the plug-layout, quotient-wire, and coalesced-frame equalities relating the
original reassembly input to a replacement input with the same ordered boundary
arity. Specialize the result to `PinnedOccurrence` in `Named.lean`.

- [ ] **Step 2: Build the focused proof-dependent kernel**

Use the active source pattern denotation before constructing any target boundary
assignment whose classes are coarser. Apply the theorem payload implication,
then use the canonical splice presentation to reconstruct the target focus and
its ancestors through the shared simulation.

- [ ] **Step 3: Add both strict-partition validation examples**

State and prove one forward example where the target boundary partition is
strictly coarser and one backward example where the source partition is strictly
coarser. In each example, the needed equality must be obtained from the active
diagram denotation; no unconditional equality premise is allowed.

- [ ] **Step 4: Expose the public receipt theorem**

Finish `applyTheorem_sound` as `SuccessfulReceiptSound` and remove any superseded
`CanonicalLocalReplacementSimulation` field that still requires a preselected
boundary witness.

- [ ] **Step 5: Typecheck high-level soundness**

Run:

```bash
lake build VisualProof.Rule.Soundness.HighLevel
```

Expected: exit 0, including both alias-partition examples.

#### Corrected shared transport prerequisite

Before completing the paired replacement kernel, replace the displaced split
between `DirectionalLocalWitness`/`DirectionalRootWitness` and later item
simulation with implication-shaped local/root transports. The transport consumes
the active local valuation and compiled-item proof and returns the opposite
valuation and compiled-item proof together. Provide an adapter for conversion,
wire severing, and other structurally total simulations, migrate their call
sites, and delete the agreement-only authoritative path.

Validate the correction with a masked-cut example where the enclosing
proposition is true without a focused valuation. The paired splice proof must
advance its focus trace through the existing `compileRegion_denote` recursion
and use contextual implication; it must not call a second compiler traversal to
extract the focus.

### Task 4: Prove scope-changing wire join on concrete contexts

**Files:**
- Modify: `VisualProof/Rule/Soundness/Structural.lean`

**Interfaces:**
- Consumes: exact-context `extendContext` and actual retained/absorbed wire
  relation.
- Produces: `applyWireJoin_sound` without a total arbitrary-region lookup law.

- [ ] **Step 1: Define the concrete join context witness**

Relate indices in the exact source and target compiler contexts by their actual
retained/absorbed wire classes. Prove extension only when the supplied source and
target extended contexts are exact at the corresponding region.

- [ ] **Step 2: Prove proof-dependent environment transport**

For the absorbed wire whose binding scope moves to the retained outer scope,
derive target locals from the active source item proof at the exact region where
the equality is semantically available. Do not assert lookup-membership
equivalence for unrelated regions.

- [ ] **Step 3: Complete and typecheck the public theorem**

Implement `applyWireJoin_sound`, then run:

```bash
lake build VisualProof.Rule.Soundness.Structural
```

Expected: exit 0.

### Task 5: Complete all remaining rule-family receipts

**Files:**
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Soundness/Structural.lean`
- Modify: `VisualProof/Rule/Soundness/Equational.lean`
- Modify: `VisualProof/Rule/Soundness/HighLevel.lean`

**Interfaces:**
- Consumes: the single rebuilt simulation API.
- Produces: one `applyX_sound` theorem for every `StepTag` constructor.

- [ ] **Step 1: Complete structural receipts**

Prove iteration, deiteration, double-cut introduction/elimination, anchored wire
split/contract, fusion, fission, and vacuous introduction/elimination. Reuse
canonical extraction/splice facts and exact occurrence certificates; do not add
a second traversal.

- [ ] **Step 2: Complete equational receipts**

Prove congruence join and head strip using the scoped relation-definition DAG and
lambda conversion certificates already formalized.

- [ ] **Step 3: Complete high-level receipts**

Prove comprehension instantiate/abstract and relation unfold/fold using the same
canonical local-replacement simulation used by theorem application.

- [ ] **Step 4: Audit the inventory**

Check `StepTag.all` against theorem names for all 25 constructors: open term
spawn, relation spawn, bound relation spawn, wire join, erasure, wire sever,
iteration, deiteration, double-cut intro, double-cut elim, conversion,
congruence join, anchored wire split, anchored wire contract, head strip, closed
term intro, fusion, fission, comprehension instantiate, comprehension abstract,
theorem, vacuous intro, vacuous elim, relation unfold, and relation fold.

- [ ] **Step 5: Typecheck every family**

Run:

```bash
lake build VisualProof.Rule.Soundness
lake build VisualProof.Rule.Soundness.Structural
lake build VisualProof.Rule.Soundness.Equational
lake build VisualProof.Rule.Soundness.HighLevel
```

Expected: all exit 0.

### Task 6: Exhaustive dispatcher, replay, and authoritative validation

**Files:**
- Create: `VisualProof/Rule/Soundness/All.lean`
- Modify: `VisualProof/Proof/Replay.lean`
- Modify: `VisualProof.lean`
- Create or modify: `VisualProof/Audit.lean`
- Modify: `scripts/check-formalization.mjs`
- Modify: `/tmp/visualproof-foundation-20260716-proof-dependent-simulation-v14.xml`

**Interfaces:**
- Consumes: all 25 public receipt soundness theorems.
- Produces: exhaustive `applyStep_sound`, replay/theory validity, and final
  conformance evidence.

- [ ] **Step 1: Implement exhaustive dispatch**

Pattern-match every `Rule.Step` constructor in `applyStep_sound` and call its
family theorem. Do not use a wildcard branch.

- [ ] **Step 2: Connect replay and theory semantics**

Make `Replay.lean` import `Rule.Soundness.All`, then prove replayed proofs and
registered theorem/theory entries preserve the declared directed semantics.

- [ ] **Step 3: Add audit checks**

Have `Audit.lean` check the public theorem inventory and print axioms for the
top-level results. Extend `scripts/check-formalization.mjs` to reject the old
witness signatures, rule-local recursive simulation definitions, `sorry`,
`admit`, and custom axioms.

- [ ] **Step 4: Run full validation**

Run:

```bash
node scripts/check-formalization.mjs
npm test
```

Expected: full Lake build and audit pass; 25 Lean/TypeScript tags agree; matcher
fixtures agree; TypeScript typecheck passes; the complete runtime suite passes.

- [ ] **Step 5: Append foundation conformance**

Append `<conformance>` to the foundation record without altering its pre-action
sections. Record the new witness ownership, deleted old model, migrated rule
families, exact commands and results, and proof that no displaced path remains.
