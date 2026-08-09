# Iteration Contract Correction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Lean certify the durable iteration operation—including an explicitly selected wire that is also exposed at the open boundary—while keeping execution computable and allowing noncomputable choice only for proof-layer witnesses.

**Architecture:** The concrete operation remains the deterministic authority for graph allocation, receipts, replay, and boundary transport. The recursive rule gains one structural freshening witness that distinguishes inherited copy wires from freshly rebound copy wires. `Rule.Iteration.Base` and recursive isomorphisms remain proof-relevant `Type` data; `Rule.Iteration`, refinement, soundness, and completeness remain propositions. The exact concrete receipt target is always preserved by `target_iso`; only the hidden proof presentation may be chosen classically.

**Tech Stack:** Lean 4, Lake, TypeScript, Vitest, the existing `VisualProof` diagram/rule/concrete/refinement layers.

## Global Constraints

- Preserve `VisualProof/Refinement/Implementation/Deiteration.lean` throughout this plan.
- Do not use the untracked `IterationBase.lean` proof as authority for the rule shape. It is addressed by the follow-on simplification plan after this contract is GREEN.
- Every executable declaration in the value-dependency closure of `Concrete.execute`, the operation appliers, splice checking, and `Proof.replay` must remain compilable by Lean's code generator.
- `Classical.choice` is permitted in theorem proofs and proof-only noncomputable definitions. It is forbidden only when code generation proves it lies in the executable value closure.
- `RegionIso`, `ItemIso`, `ItemSeqIso`, `DiagramContextIso`, `ContextPathAlignment`, `OpenDiagramIso`, and `Rule.Iteration.Base` remain Type-valued.
- The only `sorry` permitted during RED is the owning production theorem's proof. Definitions and supporting lemmas must compile before RED.
- Rule and rule-soundness modules must not import Concrete or Refinement.
- Do not preserve the boundary-disjoint request model through an alias, compatibility constructor, alternate rule, or fallback branch.
- Commit only task-owned files. The pre-existing working-tree changes in iteration implementation files are not part of this plan's early commits.

---

## Evidence and Decision

### Observed product contract

The durable TypeScript proof step stores exactly `selection` and `target`:

- `src/kernel/proof/step.ts`
- `src/kernel/proof/json.ts`
- `src/app/copy-planner.ts`

`src/kernel/rules/iteration.ts` validates enclosure and target exclusion, extracts the selected subgraph, and splices it. It does not inspect an open theorem boundary.

Lean currently adds this proof-only request field in `VisualProof/Concrete/Step.lean`:

```lean
selection.val.explicitWires.Disjoint source.checked.val.boundary
```

`Concrete.execute` ignores that field and calls `applyIteration` with only the selection and target.

### Falsifying example

Let the source be an open root diagram containing `P(w)`, with root wire `w` exposed at the boundary. Select the atom and explicitly select `w`, then iterate at the root.

The current product operation was executed against this repository. Its result retained source wire `w` and allocated a distinct copy wire `w0_0` for copied node `n0_0`:

```text
{"sourceWire":"w0","sourceStillPresent":true,"sourceEndpoints":1,
 "copiedNode":"n0_0","copiedWire":"w0_0",
 "copiedWireScope":"r0","copiedWireEndpoints":1}
```

The recursive shape is `P(w) ∧ ∃y. P(y)`, not `P(w) ∧ P(w)`. These targets are semantically equivalent in this context but are not recursively isomorphic: they differ in binding and sharing. Therefore `OpenDiagramIso` cannot repair the current `Rule.Iteration.Base`; the rule itself must represent fresh rebinding.

### Proof/computation boundary

Current observers establish the following responsibility model:

| Artifact | Required boundary |
|---|---|
| Concrete state, selection, request, allocation, receipt, provenance, boundary transport | Computable `Type` |
| `Concrete.execute`, splice checking, operation appliers, `Proof.replay` | Computable definitions |
| Recursive isomorphisms, routes, alignments, `Rule.Iteration.Base` | Proof-relevant `Type`; noncomputable selection permitted |
| `Rule.Iteration`, `Rule.Step`, representation, refinement, soundness, completeness | `Prop` |
| Exact representative identity | Required only for an executable, serialized, or compared observer |

This repository already confirms the executable fence with `Lean.compileDecls`; compiling `VisualProof.Concrete.execute` and `VisualProof.Proof.replay` succeeds.

### Mechanical cause of the failed architecture

The prior plan imposed two independent constraints:

1. every recursive witness used during composition must be Type-valued; and
2. proof-producing code could not use classical choice, so every map had to be constructively recoverable as a persistent canonical field.

The first constraint is valid. The second is not implied by execution, replay, serialization, semantics, or completeness.

Mechanically, a proposition established the existence of a route, factor, compiler presentation, or isomorphism. A downstream helper returned Type data. Prop-to-Type elimination failed. Instead of selecting one proof-only witness locally, the implementation fixed a particular carrier map in advance and expanded upstream records until that exact map could be projected. The commit sequence records the expansion:

- `Retain iteration source local equivalence`
- `Retain iteration material factor map`
- `Retain root source local map`
- `Retain open elaboration local map`

Every independently constructed presentation then had to be transported back to the selected map through `Fin.cast`, reassociated finite sums, local-count equalities, compiler reindexing, and context alignment. The two current root branches share 2,380 identical lines; their largest normalization sections are 962 of 966 lines identical. The structural-foundation interval from `788b8dfd` through current `HEAD` changed 4,723 lines in and 2,407 lines out, a net growth of 2,316 lines. The current untracked `IterationBase.lean` is 8,399 lines, and the dirty `IterationSourceFactor.lean` change is another net 545 lines.

The correction is not to turn all witnesses into propositions. It is to construct or choose one coherent proof assembly, compose its actual maps, and expose only propositional membership at the rule/refinement boundary.

---

### Task 1: Lock the durable boundary-overlap behavior

**Files:**

- Modify `tests/kernel/rules/iteration.test.ts`
- Modify `tests/kernel/proof/step.test.ts`
- Modify `tests/kernel/proof/json.test.ts`

**Steps:**

- [ ] Add an operation regression that constructs a root atom `P(w)`, explicitly selects root wire `w`, and calls `applyIteration` at the root.
- [ ] Assert that the original wire remains present with its original endpoint, the copied node exists, and the copied node is attached to a distinct fresh root-scoped wire.
- [ ] Add a receipt regression using `applyStepWithReceipt` and `transportBoundary`; assert that the original boundary position maps to the surviving original wire and never to the fresh copy wire.
- [ ] Add a durable JSON round-trip for the same `ProofStep`; assert that the encoded iteration payload contains only `rule`, `sel`, and `target`, including `sel.wires = [w]`.
- [ ] Run the focused tests:

```bash
npm test -- --run tests/kernel/rules/iteration.test.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts
```

- [ ] Commit as `Test boundary-overlap iteration replay`.

**Acceptance:** The test proves the actual graph distinction that invalidates the current Lean premise. A snapshot, source-string assertion, or test that merely checks request fields is insufficient.

---

### Task 2: Add the structural wire-freshening witness

**Files:**

- Modify `VisualProof/Rule/Iteration.lean`

**Interface:**

Add one structural witness in `VisualProof.Rule.Iteration`:

```lean
structure WireFreshening
    (sourceWires targetWires freshWires : Nat)
    (inherited : Fin sourceWires → Fin targetWires) where
  sourceOfFresh : Fin freshWires → Fin sourceWires
  sourceOfFresh_injective : Function.Injective sourceOfFresh
  wire : Fin sourceWires → Fin (targetWires + freshWires)
  wire_fresh : ∀ fresh,
    wire (sourceOfFresh fresh) = Fin.natAdd targetWires fresh
  wire_inherited : ∀ source,
    (∀ fresh, sourceOfFresh fresh ≠ source) →
      wire source = Fin.castAdd freshWires (inherited source)
```

Change `Iteration.Base` by adding:

```lean
copyLocal : Nat
copyWires : WireFreshening
  (ancestorWires + anchorLocal) descendantWires copyLocal
  descendant.outerWire
```

Define the copied region once:

```lean
def Base.copy (step : Base source target) :
    Region step.descendantWires step.descendantRels :=
  Region.adjoinAt step.copyLocal .nil
    ((step.selected.renameWires step.copyWires.wire).renameRelations
      step.descendant.outerRelation)
```

`selected` must present copy-selected concrete wires as outer parameters of the
selected region. A concrete explicit wire that is hidden in the open source is
bound by the source's surrounding `anchorLocal`; an explicit wire already
exposed by the open interface is inherited through `ancestorWires`. Both are
indices in `ancestorWires + anchorLocal`, and `copyWires.sourceOfFresh` maps a
new copy-local binder back to that source index. Do not leave concrete explicit
wires as `selected.localCount`; doing so would reproduce the boundary-overlap
failure.

Use `step.copy` in `target_iso`. Keep the current source normal form and all endpoint isomorphisms. Update `Base.iso` to transport the new fields unchanged.

**Steps:**

- [ ] Compile all new definitions before introducing a theorem hole.
- [ ] Add the production theorem that proves the environment equation used by soundness:

```lean
theorem WireFreshening.env_eq
    (freshening : WireFreshening sourceWires targetWires freshWires inherited)
    (sourceEnv : Fin sourceWires → D)
    (targetEnv : Fin targetWires → D)
    (inheritedEq : targetEnv ∘ inherited = sourceEnv) :
    ∃ freshEnv : Fin freshWires → D,
      extendWireEnv targetEnv freshEnv ∘ freshening.wire = sourceEnv
```

- [ ] Establish RED with `sorry` only in `WireFreshening.env_eq`.
- [ ] Prove it by assigning `freshEnv fresh := sourceEnv (sourceOfFresh fresh)`, splitting whether each source index lies in `sourceOfFresh`, and using injectivity to identify the unique fresh index.
- [ ] Compile strict GREEN:

```bash
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Iteration.lean
```

- [ ] Commit as `Generalize iteration copy freshening`.

**Acceptance:** The fresh identity belongs to the abstract copy construction, not concrete allocation. No names, allocation IDs, concrete imports, or choice enter this module.

---

### Task 3: Reprove iteration soundness for inherited and fresh wires

**Files:**

- Modify `VisualProof/Rule/Soundness/Iteration.lean`

**Steps:**

- [ ] State the existing `Iteration.Base.sound_iff` signature unchanged.
- [ ] Establish RED with `sorry` only in `Base.sound_iff` after the new `Base.copy` compiles.
- [ ] In the copy-transport argument, use descendant reachability for inherited wires and `WireFreshening.env_eq` for copy locals.
- [ ] Prove denotation of `Region.adjoinAt copyLocal .nil ...` by choosing the `freshEnv` supplied by `env_eq` and reusing the original selected-region witnesses.
- [ ] Keep `Iteration.sound` as the proposition-level elimination of `Nonempty Base`.
- [ ] Run strict GREEN and the rule dependency audit:

```bash
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Iteration.lean
scripts/audit-lean-authority.sh rules
```

- [ ] Inspect kernel axioms:

```bash
printf '%s\n' \
  'import VisualProof.Rule.Soundness.Iteration' \
  '#print axioms VisualProof.Rule.Iteration.Base.sound_iff' \
  '#print axioms VisualProof.Rule.Iteration.sound' \
  | LEAN_NUM_THREADS=1 lake env lean --stdin -DwarningAsError=true
```

- [ ] Commit as `Prove freshened iteration sound`.

**Acceptance:** Soundness uses only structural denotation. It does not mention concrete selection eligibility, execution, or boundary lists.

---

### Task 4: Align Lean's executable request with the durable request

**Files:**

- Modify `VisualProof/Concrete/Step.lean`
- Modify `VisualProof/Concrete/StepTags.lean` only where constructor pattern arity requires it
- Modify tracked direct constructor call sites found by `rg '\.iteration' VisualProof --glob '*.lean'`

**Interface:**

Replace the Lean constructor with the durable request:

```lean
| iteration
    (selection : CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
```

Update the inversion theorem to:

```lean
theorem execute_iteration_success
    (selection : CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
    (success : execute orientation source (.iteration selection target) = .ok receipt) :
    ∃ result : OperationReceipt source.diagram,
      applyIteration source.diagram selection target = .ok result ∧
      result.toReceipt source = some receipt ∧
      source.checked.val.diagram.Encloses selection.val.anchor target ∧
      ¬ selection.val.SelectsRegion target ∧
      Splice.Input.spliceChecked
        (iterationInput source.diagram selection target) = .ok result.result ∧
      result.Realizes
        (iterationInput source.diagram selection target).plugLayout.plugRaw
        (iterationWireProvenance source.diagram selection target)
        (iterationWireTransport source.diagram selection target)
```

**Steps:**

- [ ] Update `execute` to match `.iteration selection target`.
- [ ] Update the successful inversion theorem and all tracked callers.
- [ ] Leave no alternate boundary-disjoint constructor or smart constructor.
- [ ] Compile strict:

```bash
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Concrete/Step.lean
scripts/audit-lean-authority.sh roster
```

- [ ] Commit as `Align Lean iteration request with replay`.

**Acceptance:** Lean and TypeScript now expose the same durable iteration information. This task does not yet claim refinement; that is owned by the follow-on plan.

---

### Task 5: Add an elaborated executable-computability audit

**Files:**

- Create `VisualProof/ComputabilityAudit.lean`
- Modify `package.json` only if a named script is needed by CI

**Implementation:**

`VisualProof/ComputabilityAudit.lean` imports `Lean.Compiler` and the executable roots, then calls `Lean.compileDecls`:

```lean
import Lean.Compiler
import VisualProof.Concrete.Step
import VisualProof.Proof.Replay

open Lean

run_meta Lean.compileDecls #[
  ``VisualProof.Concrete.execute,
  ``VisualProof.Concrete.finish,
  ``VisualProof.Concrete.applyWireJoin,
  ``VisualProof.Concrete.applyWireSever,
  ``VisualProof.Concrete.applyErasure,
  ``VisualProof.Concrete.applyIteration,
  ``VisualProof.Concrete.applyDeiteration,
  ``VisualProof.Concrete.applyDoubleCutIntro,
  ``VisualProof.Concrete.applyDoubleCutElim,
  ``VisualProof.Concrete.applyVacuousIntro,
  ``VisualProof.Concrete.applyVacuousElim,
  ``VisualProof.Concrete.Splice.Input.spliceChecked,
  ``VisualProof.Proof.replay
]
```

**Steps:**

- [ ] Compile the audit under strict warnings.
- [ ] Confirm the audit fails temporarily if a compile root is changed to `noncomputable def`, then restore the executable definition. Do not commit the induced failure.
- [ ] Keep existing axiom and import-direction audits separate; this file proves value-level compilability rather than source vocabulary.
- [ ] Run:

```bash
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
```

- [ ] Commit as `Audit executable Lean value closure`.

**Acceptance:** Proof/refinement modules may use `Classical.choice`; any such dependency entering a listed executable root makes this audit fail.

---

### Task 6: Replace stale plan and goal constraints

**Files:**

- Modify `docs/superpowers/plans/2026-08-06-recursive-rewrite-authority.md`
- Modify `docs/goals/recursive-rewrite-authority/state.yaml`
- Modify `.superpowers/sdd/2026-08-06-recursive-rewrite-authority/task-9-brief.md`

**Steps:**

- [ ] Replace every requirement that iteration requests carry boundary-disjointness with the two-field selection/target request.
- [ ] Replace every instruction to keep `Rule.Iteration` unchanged with the freshening-aware `Base` contract from Tasks 2–3.
- [ ] Replace the global proof-side no-choice rule with the elaborated executable audit from Task 5.
- [ ] Reframe Task 9 as the follow-on simplification plan, not as architectural authority.
- [ ] Reframe later reflection/completeness tasks so they may start only after the generalized Base has an exact structural reflection theorem. Do not claim that a boundary-disjoint proof can be constructed for every Base.
- [ ] Record the product regression and the kernel theorem names as receipts.
- [ ] Validate the YAML and plan references with the repository's goal-state validator used by this goal.
- [ ] Commit as `Correct iteration authority plan`.

**Acceptance:** No active task, queued task, audit task, or task brief can reinstate the disproved boundary restriction or a blanket proof-side choice ban.

---

### Task 7: Contract gate before refinement simplification

**Files:** No new production declarations.

**Steps:**

- [ ] Run all focused TypeScript tests from Task 1.
- [ ] Run `npm run typecheck`.
- [ ] Run strict Lean checks for `Rule.Iteration`, its soundness, `Concrete.Step`, and `VisualProof/ComputabilityAudit.lean`.
- [ ] Run all four authority audit modes.
- [ ] Run `npm run formal:size` and confirm its only iteration failure is the
  known untracked 8,399-line `IterationBase.lean` owner handed to the follow-on
  simplification plan. No file modified by this contract plan may add a size
  violation.
- [ ] Run `lake build` with `LEAN_NUM_THREADS=1`.
- [ ] Run `git diff --check` and inspect the exact staged scope.
- [ ] Confirm all of the following before starting refinement work:

  - boundary-overlap execution and replay pass;
  - the new abstract target has a fresh binder for the copied explicit wire;
  - `Rule.Iteration.Base.sound_iff` is kernel checked;
  - the durable Lean request is selection plus target;
  - executable compile roots remain code-generatable;
  - proof-only choice is not prohibited by source scans;
  - the sole outstanding size RED is assigned to the simplification plan.

- [ ] Commit any final task-owned audit wiring as `Validate iteration contract correction`.

**Stop condition:** If the concrete boundary-overlap target cannot inhabit the generalized Base up to `OpenDiagramIso`, do not add transport laws. Revise `WireFreshening` so it models the concrete sharing/binding structure, then repeat Tasks 2–3.

---

## Reflection Gate for the Larger Goal

The original goal also requests one-step execution completeness. Soundness of the generalized rule does not by itself prove every abstract freshening is one concrete selection.

Before the completeness task starts, require a production theorem with this shape in the syntactic refinement layer:

```lean
theorem Iteration.reflect_base
    (step : Rule.Iteration.Base source target)
    (sourceRep : StateRepresents concrete source) :
    ∃ (request : Concrete.Step concrete)
      (receipt : Concrete.Receipt concrete),
      request.tag = .iteration ∧
      Concrete.execute orientation concrete request = .ok receipt ∧
      StateRepresents receipt.target target
```

The theorem may use classical choice because its conclusion is existential in `Prop`; the request it produces remains ordinary computable data. If the theorem fails because `WireFreshening` permits a freshened wire that no valid concrete selection can own, strengthen the Base with the required structural exclusivity condition. Do not weaken completeness, restrict the executor, or add a second implementable-iteration relation.

The follow-on simplification plan may prove execution refinement before this reflection theorem, but the larger completeness tasks remain blocked until it is GREEN.

---

## Final Validation

```bash
npm test -- --run tests/kernel/rules/iteration.test.ts tests/kernel/proof/step.test.ts tests/kernel/proof/json.test.ts
npm run typecheck
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Iteration.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Iteration.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/Concrete/Step.lean
LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh proof
scripts/audit-lean-authority.sh roster
LEAN_NUM_THREADS=1 lake build
git diff --check
```

Run `npm run formal:size` as a recorded RED at this boundary. It becomes a
required GREEN command in the follow-on simplification plan after the 8,399-line
iteration owner has been replaced.

## Plan Falsifiers

- A durable serializer, replay engine, UI, receipt, or theorem checker begins storing or comparing `Rule.Iteration.Base` or its carrier maps.
- `Concrete.execute` or `Proof.replay` computes from a proof-selected structural representative.
- The concrete boundary-overlap result is structurally isomorphic to the old shared-wire target after all; the regression and recursive isomorphism check would have to demonstrate this.
- `WireFreshening` cannot prove semantic transport without adding a semantic premise to the rule witness.
- The generalized Base cannot be structurally reflected into a concrete request even after adding the exact wire-exclusivity condition.
- The product intentionally rejects explicit selection of an exposed wire through an authoritative runtime check and durable format change. No such check exists now.
