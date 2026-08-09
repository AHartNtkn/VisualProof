# Iteration Refinement Simplification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove successful concrete iteration and deiteration refine the corrected recursive iteration rule through one coherent witness assembly, while bringing the iteration implementation below the repository size gate and eliminating repeated empty/nonempty and route-normalization proofs.

**Architecture:** The owning theorem is proposition-valued: it proves `Nonempty (Rule.Iteration.Base exactSource exactReceiptTarget)`. Inside that proof, routes, compiler views, finite equivalences, and recursive isomorphisms remain Type-valued and may be selected classically. Related maps are constructed as one local assembly and then composed; they are not required to equal a separately chosen global presentation. Empty and nonempty compiler paths supply a small dependent fragment input to one root/proper assembler. Public refinement exposes only the exact represented receipt target and `Rule.Iteration`.

**Tech Stack:** Lean 4, Lake, the corrected `Rule.Iteration.WireFreshening`, existing Concrete splice/compiler evidence, existing recursive isomorphism hierarchy.

## Global Constraints

- This plan starts after the semantic, request, computability, and audit gates
  in `2026-08-09-iteration-contract-correction.md` are GREEN. The recorded
  `formal:size` RED for the 8,399-line iteration owner is this plan's first
  quantitative obligation.
- Preserve the exact canonical source `source.checked.elaborate.castArity source.boundary_length` and exact `spliceTarget` receipt endpoint.
- Preserve deterministic concrete allocation, provenance, boundary transport, and replay. Proof-side choices never enter the executable closure.
- Keep `Rule.Iteration.Base` and recursive isomorphisms Type-valued.
- Return `Nonempty Base` from the owning theorem. Add a private `noncomputable def` selecting a `Base` only if a real local consumer projects its fields.
- Choose a coherent dependent package once. Do not independently choose a route, carrier, and map and later prove them equal to a fixed canonical map.
- No persistent operation-specific field may exist solely to equate an isomorphism's internal map with `anchorLocalEquiv`, `rootLocalEquiv`, or another preselected presentation.
- No compatibility alias, adapter module, duplicate certificate, alternate witness authority, or fallback proof path.
- `Classical.choice` is allowed in proof-only construction. `VisualProof/ComputabilityAudit.lean` is the controlling fence.
- `sorry` is allowed only in the currently owning production theorem during RED.
- Preserve `VisualProof/Refinement/Implementation/Deiteration.lean` until Task 6 explicitly integrates the inverse theorem.
- Each production file must remain below 3,000 physical lines.
- The final total of `VisualProof/Refinement/Implementation/Iteration*.lean` must be at most 12,000 physical lines. Current measured total is 20,177.
- The final root empty/nonempty adapters must contain no common normalization body longer than 100 lines. Shared work belongs in one assembler, not in two branches.
- A source-size reduction is not sufficient by itself: the final proof must preserve the exact receipt target and pass all semantic-free dependency audits.

---

## Complexity Ledger

| Category | Current evidence | Final owner |
|---|---|---|
| Essential behavior | `Concrete.execute` and `applyIteration` deterministically produce the receipt target | Concrete; unchanged |
| Essential proof state | Recursive endpoint isomorphisms while their maps are composed | Local Type-valued assembly |
| Essential invariant | Exact boundary order/aliasing and exact represented target | `StateRepresents`, `OpenDiagramIso`, receipt endpoint |
| Essential rule data | Interface, outer/descendant contexts, selected region, remainder, copy freshening, source/target iso | `Rule.Iteration.Base` |
| Derived data | Compiler branch, route, factor, local counts, carrier casts | Private theorem proof |
| Accidental state | Exact-map projection fields and branch-specific target normalizers | Absent from final records |
| Power leak | Requiring all consumers to use one named `FiniteEquiv` presentation | Replaced by composing the selected assembly's actual map |

Measured tar-pit evidence:

- `IterationBase.lean`: 8,399 lines.
- `IterationSourceFactor.lean`: 2,600 lines in the working tree.
- all `Iteration*.lean` implementation files: 20,177 lines.
- `rootAtStartOfEmptyIso` and `rootAtStartOfNonemptyIso`: 2,380 identical lines.
- largest repeated target-normalization section: 962 of 966 lines identical.
- current `retained_target` surface: net 545 lines in `IterationSourceFactor.lean`, with no consumer outside its constructor path.
- `IterationPathAlignment.lean` repeats the permutation/index-equivalence block already owned by `IterationPartition.lean`.

These are responsibility failures, not isolated tactic verbosity: compiler branch selection, canonical-map selection, and endpoint normalization are interleaved in each branch.

---

### Task 1: Establish a clean, measurable implementation boundary

**Files:**

- Modify `VisualProof/Refinement/Implementation/IterationSourceFactor.lean`
- Modify `VisualProof/Refinement/Implementation/IterationPartition.lean`
- Migrate remaining imports from `VisualProof/Refinement/Implementation/IterationPathAlignment.lean`
- Modify task-owned iteration reports only if they are active validation inputs

**Steps:**

- [ ] Record SHA-256 hashes and line counts for every current `Iteration*.lean` file before editing.
- [ ] Replace the unfinished `retained_target` record surface with the last strict-GREEN `SourceFactorResult` responsibility while preserving unrelated user work.
- [ ] Move the shared permutation/index equivalence and compiler occurrence permutation proof to `IterationPartition.lean` as the single owner.
- [ ] Migrate all consumers to that owner and leave no `IterationPathAlignment` module in the final import graph.
- [ ] Run `rg` for every moved declaration and confirm one definition/theorem owner.
- [ ] Compile the dependency closure strictly before introducing a new theorem hole.
- [ ] Run `npm run formal:size` and record the expected current failure caused by the untracked 8,399-line owner; this is the quantitative RED for the architecture, not the Lean theorem RED.
- [ ] Commit as `Consolidate iteration proof infrastructure`.

**Acceptance:** This task establishes one owner for shared structural facts. It does not preserve the unfinished target-map experiment under a renamed field.

---

### Task 2: Introduce one dependent fragment compiler input

**Files:**

- Create `VisualProof/Refinement/Implementation/IterationFragment.lean`
- Modify `VisualProof/Refinement/Implementation/IterationSourceFactor.lean`
- Modify `VisualProof/Concrete/Subgraph/Splice/Input/CompilerSource.lean`

**Required private data:**

Define one private dependent fragment package owned by refinement. It contains exactly the arguments already consumed by `sourceFactor_complete`:

- fragment relation context;
- compiler fuel;
- extraction wire context;
- binder context;
- binder enumeration at `layout.bodyContainer`;
- exactness of the wire context;
- compiled `ItemSeq`;
- the exact `compileOccurrencesWith? = some items` computation.

Provide two constructors:

```lean
private noncomputable def fragmentOfEmpty
    (empty : spliceInput.binderSpine.proxyCount = 0) :
    FragmentInput source selection layout spliceInput

private noncomputable def fragmentOfNonempty
    (nonempty : spliceInput.binderSpine.proxyCount ≠ 0) :
    FragmentInput source selection layout spliceInput
```

The empty constructor uses `compiledSpliceOpenRootItems`; the nonempty constructor uses `compiledSpliceTerminalView`. All later factor and endpoint code accepts only `FragmentInput` and does not case-split on the binder spine.

**Steps:**

- [ ] Complete both constructors with no theorem hole.
- [ ] Compile `IterationFragment.lean` strictly.
- [ ] Change the generic source-factor constructor to accept `FragmentInput` instead of seven independent compiler arguments.
- [ ] Replace the `TerminalCompilerView` compatibility abbreviation in `CompilerSource.lean` with direct uses of `PatternTerminalCompilerView`.
- [ ] Confirm the empty/nonempty distinction is absent from `IterationSourceFactor.lean` after the two constructors.
- [ ] Commit as `Unify iteration fragment compilation`.

**Acceptance:** The branch packages authoritative compiler evidence. It does not contain host quotient, route, Base, or target-normalization logic.

---

### Task 3: Replace canonical-map fields with one coherent factor assembly

**Files:**

- Modify `VisualProof/Refinement/Implementation/IterationSourceFactor.lean`
- Modify `VisualProof/Refinement/Implementation/IterationRootSourceFactor.lean`
- Modify `VisualProof/Refinement/Implementation/IterationActualSplice.lean`
- Modify neutral compiler projection modules only if their now-orphaned declarations have no remaining consumer

**Architecture:**

The source-factor theorem constructs a single local dependent package containing every Type object that must agree:

- selected region presentation;
- a source-carrier partition placing hidden explicit wires in the surrounding
  anchor-local block and exposed explicit wires in the inherited interface
  block;
- route alignment and descendant/remainder split;
- source `RegionIso`;
- material `RegionIso`;
- concrete-to-abstract copy `WireFreshening` required by the corrected Base.

The package's isomorphisms are constructed together from one partition and one compiler witness. Later maps are derived by projecting the first selected isomorphism and composing it. The package exposes no equality to a separately named canonical map.

**Steps:**

- [ ] State and compile the private package type before RED.
- [ ] Replace `SourceFactorResult.selected_local` by constructing `selected`
  directly with copy-selected wires as outer parameters. Its local wire count
  must not contain the concrete explicit-wire block.
- [ ] Partition concrete explicit wires into source indices in the inherited
  interface block or the surrounding hidden anchor-local block; use the
  selection's nodup proof to build `copyWires.sourceOfFresh_injective`.
- [ ] Replace `SourceFactorResult.source_local`, `material_local`, and `retained_target` with local coherence proved inside the package constructor.
- [ ] Make `sourceFactor_complete` return `Nonempty FactorAssembly` if no downstream Type-level consumer exists; otherwise keep a private noncomputable selector adjacent to its sole consumer.
- [ ] Replace the root certificate's exact `source_local = rootLocalEquiv.symm` field with a source endpoint isomorphism derived from the same factor assembly.
- [ ] Replace the actual-splice PSigma/decomposition surface with the final `RegionIso` consumed by assembly; keep decomposition fields private to its proof.
- [ ] Run `rg` for `source_local`, `material_local`, `retained_target`, and `rootLocalEquiv`; any remaining use must be either a generic structural theorem or an actual final-assembly projection.
- [ ] Re-evaluate the compiler local-map projection declarations introduced solely for these equalities. If they have no current consumer, restore the smaller compiler API rather than retaining speculative projection surface.
- [ ] Strict-compile SourceFactor, RootSourceFactor, and ActualSplice.
- [ ] Commit as `Couple iteration factor witnesses`.

**Acceptance:** Coherence still exists, but it is established once by construction. No downstream proof must show two independently selected `FiniteEquiv` values equal a global canonical function.

---

### Task 4: Prove one root-at-start assembler

**Files:**

- Create `VisualProof/Refinement/Implementation/IterationAssembly.lean`
- Replace the untracked `VisualProof/Refinement/Implementation/IterationBase.lean` owner with the shared assembly

**Owning RED theorem:**

```lean
theorem rootAtStart_exists
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (targetNotSelected : ¬ selection.val.SelectsRegion selection.val.anchor)
    {result : Concrete.Checked}
    (success : (iterationInput source.diagram selection selection.val.anchor
      ).spliceChecked = .ok result) :
    Nonempty (Rule.Iteration.Base
      (source.checked.elaborate.castArity source.boundary_length)
      (spliceTarget source selection selection.val.anchor success))
```

**Steps:**

- [ ] Complete all supporting definitions and fragment adapters first.
- [ ] Introduce `sorry` only as the body of `rootAtStart_exists` and compile RED.
- [ ] Destructure `Nonempty FactorAssembly` inside the theorem proof.
- [ ] Build one root host/quotient/source chain and one target chain parameterized by `FragmentInput`.
- [ ] Compose the assembly's actual local equivalences; do not normalize them to `rootLocalEquiv` or `anchorLocalEquiv` unless an endpoint boundary theorem directly observes that map.
- [ ] Construct `Rule.Iteration.Base.copyWires` from the concrete selection partition, including fresh copy locals for explicitly selected exposed wires.
- [ ] Prove exact target alignment to `spliceTarget`, including output arity transport, once after the common assembler.
- [ ] Use `fragmentOfEmpty` or `fragmentOfNonempty` only to provide the `FragmentInput`; no subsequent branch-specific normalization is permitted.
- [ ] Replace the theorem hole and compile strict GREEN.
- [ ] Require `IterationAssembly.lean` to be below 2,500 lines at this checkpoint.
- [ ] Commit as `Prove root iteration assembly`.

**Acceptance:** Both binder-spine cases close through the same theorem body. A second root target normalizer, branch-specific certificate, or duplicated arity transport fails review.

---

### Task 5: Extend the assembler over proper routes

**Files:**

- Modify `VisualProof/Refinement/Implementation/IterationRoute.lean`
- Modify `VisualProof/Refinement/Implementation/IterationActualSplice.lean`
- Modify `VisualProof/Refinement/Implementation/IterationAssembly.lean`

**Owning RED theorem:**

```lean
theorem baseOfSplice_exists
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (target : Fin source.diagram.val.regionCount)
    (encloses : source.diagram.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    {result : Concrete.Checked}
    (success : (iterationInput source.diagram selection target).spliceChecked =
      .ok result) :
    Nonempty (Rule.Iteration.Base
      (source.checked.elaborate.castArity source.boundary_length)
      (spliceTarget source selection target success))
```

**Steps:**

- [ ] Complete a single proper-route fragment/actual-splice adapter before RED. It consumes a Type-valued route and `FragmentInput` and returns the final `RegionIso` required by assembly.
- [ ] Keep the exact route path only while composing context maps. Do not expose head positions, cast-path data, or terminal-inherited equivalences without a current consumer.
- [ ] Introduce `sorry` only at `baseOfSplice_exists` after the adapter compiles.
- [ ] Inside the proposition-valued theorem, destruct the route existence proof directly. Use classical choice only when a Type-returning local helper materially reduces dependent transport.
- [ ] Handle anchor-at-start by `rootAtStart_exists`; handle a proper route through the single adapter. The empty/nonempty choice remains confined to `FragmentInput` construction.
- [ ] Build the final Base once and wrap it in `Nonempty.intro`.
- [ ] Replace the theorem hole and compile strict GREEN.
- [ ] Confirm there is no private unresolved `Base` witness, success-shaped fallback, or unreachable branch.
- [ ] Commit as `Prove iteration splice refinement base`.

**Acceptance:** Every successful admissible splice reaches the exact receipt target. Proper routes do not reintroduce the root normalizer under new names.

---

### Task 6: Add public iteration and deiteration refinement

**Files:**

- Create `VisualProof/Refinement/Step/Iteration.lean`
- Modify `VisualProof/Refinement/Step.lean`
- Modify `VisualProof/Refinement/Implementation/Deiteration.lean` only for the inverse family theorem

**Public signatures:**

```lean
theorem iteration
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.iteration selection target) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.Iteration sourceDiagram targetDiagram
       | .backward => Rule.Iteration targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram

theorem deiteration
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    (witness : Concrete.DeiterationWitness source selection)
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.deiteration selection witness) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.Iteration targetDiagram sourceDiagram
       | .backward => Rule.Iteration sourceDiagram targetDiagram) ∧
      StateRepresents receipt.target targetDiagram
```

**Steps:**

- [ ] Follow the established `Refinement.Step.DoubleCut` observer shape: canonical source, exact canonical receipt target, representation uniqueness, and rule isomorphism transport.
- [ ] For iteration, obtain `Nonempty Base` directly from `baseOfSplice_exists`; do not select a stable Base unless a field is immediately required.
- [ ] For deiteration, prove the inverse family against the same `Rule.Iteration` relation; do not create a parallel deiteration rule.
- [ ] Add the family to `VisualProof/Refinement/Step.lean` only after both theorems are GREEN.
- [ ] Run strict family and aggregate compilation and the implementation audit.
- [ ] Commit as `Prove iteration execution refinement`.

---

### Task 7: Enforce the simplification boundary

**Files:**

- Modify `scripts/check-source-size.mjs` only if it needs a total-family budget in addition to its existing per-file limit
- Modify `scripts/audit-lean-authority.sh` only for semantic responsibility checks, not declaration-name snapshots
- Modify active goal/task receipts

**Steps:**

- [ ] Run `wc -l` over every final `Iteration*.lean` implementation module.
- [ ] Require every file to be at most 3,000 lines and the family total to be at most 12,000 lines.
- [ ] Inspect the final import graph. Any iteration module with no importer and no intentional public API fails the gate.
- [ ] Inspect public structures. Every proof-only field must be projected by the final Base assembly or have at least two genuine current consumers.
- [ ] Search for `source_local`, `material_local`, `retained_target`, `boundaryDisjoint`, compatibility markers, branch-specific `rootAtStartOfEmptyIso`/`rootAtStartOfNonemptyIso`, and unresolved local Base witnesses; all displaced surfaces must be absent from the active closure.
- [ ] Review empty/nonempty adapters side by side and reject any repeated normalization body over 100 lines.
- [ ] Run `VisualProof/ComputabilityAudit.lean`; proof-side choice is accepted only while executable roots still compile.
- [ ] Update the active goal state so downstream completeness/rejection work depends on the corrected Base and the reflection gate, not the prior Task 9 constraints.
- [ ] Commit as `Enforce simplified iteration architecture`.

**Acceptance:** Validation proves the selected responsibility model. A renamed tower, generic dumping-ground module, line wrapping, generated copy, or source-substring fixture does not satisfy this task.

---

### Task 8: Validate end to end and unlock later work

**Files:** No new production declarations unless a validation failure identifies a real missing owner.

**Steps:**

- [ ] Run the boundary-overlap product regressions and the full relevant TypeScript suite.
- [ ] Run `npm run typecheck` and `npm run formal:size`.
- [ ] Strict-compile every modified Lean owner.
- [ ] Run `VisualProof/ComputabilityAudit.lean`.
- [ ] Run the four authority audit modes.
- [ ] Run `VisualProof/Audit.lean` and inspect axioms for `Rule.Iteration.sound` and the public iteration/deiteration refinement theorems.
- [ ] Run `LEAN_NUM_THREADS=1 lake build`.
- [ ] Run `git diff --check` and inspect staged scope.
- [ ] Obtain an independent architecture review against these questions:

  - Does concrete execution remain the only allocator?
  - Does the abstract Base model the actual fresh/shared wire pattern?
  - Is every proof-only representative local or genuinely observed?
  - Is empty/nonempty logic confined to fragment compilation?
  - Is route logic confined to route traversal?
  - Is endpoint normalization performed once?
  - Does the exact receipt target remain the represented target?
  - Are the size budgets met by responsibility consolidation rather than relocation?

- [ ] Commit final task-owned validation wiring as `Validate simplified iteration refinement`.

**Unlock condition:** Resume aggregate soundness, reflection, completeness, and rejection work only when Tasks 1–8 are GREEN and `Iteration.reflect_base` from the contract plan has either passed or is the sole explicitly active next theorem.

---

## Final Validation Commands

```bash
npm test -- --run tests/kernel/rules/iteration.test.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts
npm run typecheck
npm run formal:size
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Iteration.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Iteration.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Implementation/IterationFragment.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Implementation/IterationSourceFactor.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Implementation/IterationActualSplice.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Implementation/IterationAssembly.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Step/Iteration.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Refinement/Step.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh proof
scripts/audit-lean-authority.sh roster
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Audit.lean
LEAN_NUM_THREADS=1 lake build
git diff --check
```

## Plan Falsifiers

- A final Base field requires exact equality with a globally named carrier map because an actual endpoint observer compares that map.
- The concrete boundary-overlap splice cannot be related to the generalized Base by `OpenDiagramIso`.
- A route or compiler witness must be serialized, replayed, displayed, or compared independently.
- The total falls below the line budget only by moving the same normalization into a neutral or generated module.
- The root-at-start slice still needs separate empty and nonempty endpoint proofs after `FragmentInput` exists.
- Proof-side choice enters any executable compile root.
- Exact one-step reflection fails for a structurally valid Base; then the Base must gain the precise exclusivity invariant before later completeness work starts.
