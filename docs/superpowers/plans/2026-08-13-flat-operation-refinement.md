# Flat Operation Refinement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that every successful concrete structural operation realizes its corresponding abstract rule between the source and receipt target canonical diagrams.

**Architecture:** Keep `CompilerCall`/`CompiledRegion` as the sole compiler authority and canonical source focus as the sole navigation authority. Each flat primitive gets one source-derived elaboration theorem: contextual graft for splice/replacement and wire-fiber refinement for quotient/split. Family proofs invert `Concrete.execute`, consume one primitive theorem, provide only their local rule constructor and polarity evidence, and then lift through neutral replacement evidence.

**Tech Stack:** Lean 4, Lake, VisualProof signature-indexed concrete compiler, flat structural operations, neutral contextual rule relations.

## Global Constraints

- Use theorem-driven RED/GREEN: existing family theorem proofs are the owning RED declarations; supporting definitions and lemmas must be GREEN before entering each owner proof.
- Never search the target for a focus, route, occurrence order, or compiler presentation.
- Do not add a configurable compiler simulation, compatibility adapter, target witness argument, receipt proof payload, heartbeat override, or recursion-depth override.
- Construct target compiler results from source compiler evidence and identify them with checked target compilation by determinism.
- Keep operation-specific local semantic evidence in the corresponding refinement family; generic elaboration modules return neutral replacement evidence only.
- Preserve unrelated working-tree changes and commit each independently GREEN boundary.

## Complexity Ledger

- **Essential behavior:** ten concrete request constructors refine the five abstract rule families with the executor-selected direction.
- **Essential state:** primitive success/composition equations, canonical source compiler result/focus, checked source invariants, and flat allocation maps.
- **Integrity constraints:** target computation is source-derived; contextual polarity equals concrete cut-depth parity; selection partitions are stable and exhaustive; wire split/join preserves the exact boundary map.
- **Derived data:** target compiled trees, endpoint contexts, local before/after bodies, selection material, freshening maps, and endpoint isomorphisms.
- **Accidental state prohibited:** target focuses/routes, stored context mirrors, separately selected target bodies, caller-supplied compiler callbacks, and duplicate replacement presentations.
- **Accidental control prohibited:** separate root/nested traversal families, operation-specific whole-tree recursions when a primitive theorem already exists, and elaborator-limit increases.
- **Power boundary:** generic modules expose only `ContextReplacement`, `NestedContextReplacement`, or the existing `WireSever.Open`; family files expose only canonical `DirectedStep` theorems.

---

### Task 1: Shared contextual polarity and splice-family lifting

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/Compiled.lean`
- Create: `VisualProof/Refinement/Step/Splice.lean`
- Modify: `VisualProof/Refinement/Step/Erasure.lean`

**Interfaces:**
- Consumes: `CompiledSite.context`, `CompiledSite.splice`, `Concrete.execute_success_composition`, `ContextReplacement.lift`, `Rule.Erasure.Local.erase`.
- Produces: `CompiledSite.context_cutDepth`; a private splice-erasure local-evidence constructor; GREEN `boundRelationSpawn`.

- [ ] Prove `CompiledSite.context_cutDepth source site : (CompiledSite.context source site).cutDepth = concreteCutDepth source.checked.val.diagram site` by one fold over the canonical zipper, matching cut/bubble parent recurrence.
- [ ] Add a proof-only helper in `Refinement/Step/Splice.lean` which rewrites `CompiledSite.splice_before`/`splice_after`, constructs `Rule.Erasure.Local.erase`, selects converse evidence from `contextPolarity_of_spawnPolarity`, and returns the directed `Rule.Step.erasure` for the executor orientation.
- [ ] Replace the `boundRelationSpawn` owner `sorry` by execution inversion, `CompiledSite.splice`, and that helper.
- [ ] Run strict checks for `Compiled.lean`, `Splice.lean`, `SpliceRootCompilation.lean`, and `Refinement/Step/Erasure.lean`; commit the GREEN slice.

### Task 2: Fused selection replacement elaboration

**Files:**
- Create: `VisualProof/Concrete/Elaboration/SelectionReplacementCompilation.lean`
- Modify: `VisualProof/Concrete/Elaboration.lean`

**Interfaces:**
- Consumes: `CompiledSelection.partition/factorization`, `replaceSelectionRaw_composition`, prepared frame allocation maps, and the endpoint splice construction.
- Produces: `CompiledSelection.replace`, returning one `ContextReplacement` whose `before` is the source anchor body and whose `after` is `Region.spliceAt` of retained source items and replacement material.

- [ ] Define the source-derived local replacement body from `CompiledSelection.retainedIntrinsic`, the replacement pattern body, and the prepared splice wire/relation maps; do not expose the prepared frame compiler result.
- [ ] Prove the endpoint compiler construction directly from the source selection partition plus the prepared splice endpoint theorem; braid retained/material source order exactly once through `CompiledSelection.factorization`.
- [ ] Fold the endpoint construction through the canonical source zipper using the existing `DiagramContextIso` frame boundary, returning target compilation plus one context alignment.
- [ ] Enter the owning `CompiledSelection.replace` theorem only after all dependencies compile; prove its target endpoint by checked compiler determinism and expose ordinary context/before/after projection theorems.
- [ ] Run strict warning-as-error checks, the focused replacement closure build, admission/authority/limit scans, and commit.

### Task 3: Erasure, deiteration, double-cut, and vacuity families

**Files:**
- Modify: `VisualProof/Refinement/Step/Erasure.lean`
- Modify: `VisualProof/Refinement/Step/Iteration.lean`
- Modify: `VisualProof/Refinement/Step/DoubleCut.lean`
- Create: `VisualProof/Refinement/Step/Vacuity.lean`
- Modify: `VisualProof/Refinement/Step.lean`

**Interfaces:**
- Consumes: `CompiledSelection.replace`, primitive composition witnesses, wrapper/recognition equations, `ContextReplacement.lift`, and local constructors for Erasure/DoubleCut/Vacuity.
- Produces: GREEN `erasure`, `deiteration`, `doubleCutIntro`, `doubleCutElim`, `vacuousIntro`, and `vacuousElim`.

- [ ] Prove empty replacement projects to the retained anchor body and use `Rule.Erasure.Local.erase` plus `contextPolarity_of_erasurePolarity` for `erasure`.
- [ ] Use the same neutral replacement in the inverse direction with the supplied certificate to prove `deiteration` after the iteration nested law is available; do not add a second removal theorem.
- [ ] Prove the double-cut wrapper body equals `Rule.DoubleCut.wrap` of the extracted source material, then lift `Rule.DoubleCut.Local.introduce`; prove elimination by recognition, the extracted-body replacement, and `Rule.DoubleCut.symm`.
- [ ] Prove the analogous vacuous wrapper equality and lift `Rule.Vacuity.Local.introduce`; prove elimination by recognition and `Rule.Vacuity.symm`.
- [ ] Strict-check each family after its owner becomes GREEN and commit independently reviewable family slices.

### Task 4: Nested iteration replacement

**Files:**
- Create: `VisualProof/Concrete/Elaboration/IterationCompilation.lean`
- Modify: `VisualProof/Concrete/Elaboration.lean`
- Modify: `VisualProof/Refinement/Step/Iteration.lean`

**Interfaces:**
- Consumes: source selection partition, the canonical anchor and descendant focuses, `CompiledSite.splice`, extraction maps, and `Rule.Iteration.WireFreshening`.
- Produces: one neutral `NestedContextReplacement` for a successful `iterationSpliceInput`; GREEN `iteration` and `deiteration`.

- [ ] Derive the descendant zipper by structurally restricting the canonical target-site zipper beneath the selected anchor; reject any design requiring independently compared path lists.
- [ ] Factor the source anchor body into selected material conjoined with the descendant context using `CompiledSelection.factorization` and the checked `Encloses`/not-selected premises.
- [ ] Construct the extraction wire freshening from actual fragment layout allocation and prove its inherited/fresh equations.
- [ ] Combine the splice target isomorphism with the source factorization into `NestedContextReplacement`; the local `after_eq` must be exactly `Rule.Iteration.Local.copy`.
- [ ] Replace the `iteration` and `deiteration` owner proofs by primitive inversion, nested lifting, and `Rule.Iteration.symm` where required; strict-check and commit.

### Task 5: Wire quotient/split elaboration

**Files:**
- Create: `VisualProof/Concrete/Elaboration/WireCompilation.lean`
- Modify: `VisualProof/Concrete/Elaboration.lean`
- Modify: `VisualProof/Refinement/Step/WireSever.lean`

**Interfaces:**
- Consumes: `quotientWiresRaw_result`, `splitWireRaw_result`, source compilation, concrete wire endpoint/boundary equations, and `Rule.WireSever` local/open witnesses.
- Produces: `elaborate_quotientWiresRaw`, `elaborate_splitWireRaw`, GREEN `wireJoin`, and GREEN `wireSever`.

- [ ] Define the target-to-source wire collapse induced by quotient/split and prove port, scope, boundary, surjectivity, and local-context equations from the flat primitive allocation.
- [ ] Prove one compiler wire-fiber theorem by induction over the source signature-indexed compiler result; instantiate it in opposite directions for quotient and split without a universal transformation record.
- [ ] Package hidden-wire changes as contextual `Rule.WireSever.Local.sever` and exposed-wire changes as `Rule.WireSever.Open`; select the case from the affected wire scope.
- [ ] Prove `wireJoin` and `wireSever` from execution composition, polarity, and the neutral wire evidence; strict-check and commit.

### Task 6: Exhaustive dispatcher and representation transport

**Files:**
- Modify: `VisualProof/Refinement/Step.lean`
- Modify: `VisualProof/ComputabilityAudit.lean` only if its authoritative symbol roster requires the now-GREEN refinement declarations.

**Interfaces:**
- Consumes: all ten GREEN family theorems and `DirectedStep.ofCanonical`.
- Produces: GREEN `execute_refinesCanonical` and `execute_refines`.

- [ ] Exhaustively case-split `Concrete.Step`, invoking exactly one family theorem per constructor.
- [ ] Define `execute_refines` solely as `DirectedStep.ofCanonical sourceRep (execute_refinesCanonical success)`.
- [ ] Run strict warning-as-error checks over the entire refinement closure and require an empty `sorry` scan in that closure.
- [ ] Run the computability and authority audits, focused family builds, full `lake build`, and `git diff --check`.
- [ ] Commit the dispatcher/audit slice and verify only unrelated user changes remain unstaged.

## Self-Review

- **Spec coverage:** Tasks 1–5 supply all four generic primitive elaboration laws and all ten family theorems; Task 6 supplies both aggregate theorems.
- **Placeholder scan:** Every task names its owning theorem, evidence source, proof boundary, validation, and commit point; no implementation choice is deferred to a compatibility layer.
- **Type consistency:** Primitive theorems return neutral diagram relations; only family files introduce abstract rule constructors; dispatcher inputs and conclusions retain the existing canonical signatures.
