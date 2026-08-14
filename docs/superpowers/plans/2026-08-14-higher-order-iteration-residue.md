# Higher-Order Iteration Residue Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define sound, directly executable higher-order iteration and deiteration whose fresh and inherited wires retain canonical DCA ownership through unary-identity residues.

**Architecture:** Keep the recursive typed syntax and computed-DCA ownership unchanged. A copy derives fresh-wire pins from the copied selected material; removal derives inherited-wire pins from the exact removed copy and surviving remainder. Both residues are local functions of the indexed rule instance, and enclosing canonicality is lifted through the existing recursive contexts without normalization or wire movement.

**Tech Stack:** Lean 4.30.0, Lake, typed recursive diagrams, computed DCA canonicality, proposition-valued rules, direct computable runners.

## Global Constraints

- Keep `Region`, `Item`, `ItemSeq`, and computed DCA scope unchanged.
- Do not search the source, normalize the target, move wire binders, or add stored scope.
- Keep one source occurrence authority and one iteration relation.
- Fresh-wire pins occur directly at the copied region root exactly when copied incidences are empty or have non-root DCA.
- Deiteration residue pins occur directly at the descendant hole root exactly when the removed copy used an inherited wire and the remainder does not.
- Unary identities are semantically true; proof fields may certify canonical targets but runner results depend only on computational index data.
- Every theorem dependency is complete before RED; `sorry` may appear only in an owning theorem proof during RED.
- Stop if canonicality requires inspecting or rebuilding unrelated regions, or if a second representation of scope or navigation appears.

---

### Task 1: Factor the generic unary-identity kernel

**Files:**
- Create: `VisualProof/Diagram/UnaryIdentity.lean`
- Create: `VisualProof/Diagram/Semantics/UnaryIdentity.lean`
- Modify: `VisualProof/Rule/Erasure.lean`
- Modify: `VisualProof/Rule/Soundness/Erasure.lean`

**Interfaces:**
- Consumes: typed `Var`, `WireRenaming`, incidence paths, and unary `Item.identity`.
- Produces: `ItemSeq.pinWires`, `ItemSeq.needsRootPin`, structural canonicality lemmas, incidence membership/absence lemmas, and semantic truth.

- [ ] Move the generic typed `pinWires` definition out of the erasure rule and rename direct consumers to `ItemSeq.pinWires`.
- [ ] Move its children-canonical, selected-wire membership, and absent-wire incidence lemmas into the same structural owner.
- [ ] Define `ItemSeq.needsRootPin items wire := decide (not (paths nonempty and DCA paths = []))` once and use it from erasure.
- [ ] Move the generic unary-pin denotation theorem into the separate semantic owner imported by both rule soundness modules; keep the structural owner free of semantic imports.
- [ ] Strict-check erasure, rebuild its soundness/executable closure, scan for the displaced definition, and commit the green extraction.

### Task 2: Migrate exact nested occurrences

**Files:**
- Replace: `VisualProof/Diagram/NestedOccurrence.lean`

**Interfaces:**
- Consumes: typed `OpenDiagram`, `DiagramContext`, `Region.adjoinAt`, and canonical `withBody`.
- Produces: one typed `NestedOccurrence selected before source`, its source canonicality, and direct `replace after targetCanonical`.

- [ ] Replace natural-number wire counts and relation contexts with exact `List Sig` contexts.
- [ ] Store the canonicality proof of the source body assembled from the outer context, selected region, descendant context, and before region.
- [ ] Make `replace` accept the canonicality proof of the filled target and call `OpenDiagram.withBody` directly.
- [ ] Remove the replacement-record constructor and its dependency on the stale replacement module; no compatibility definition remains.
- [ ] Strict-check and focused-build `NestedOccurrence`, scan for numeric/relation fields, and commit the green boundary.

### Task 3: Define typed iteration copies and both residues

**Files:**
- Modify: `VisualProof/Diagram/Scope.lean`
- Replace: `VisualProof/Rule/Iteration.lean`

**Interfaces:**
- Produces: typed `WireFreshening`; `freshenedCopy`; `copied`; `uncopyResidue`; canonicality and hole-wire nonemptiness laws; and the exact higher-order iteration relation.

- [ ] Replace `WireFreshening` with typed signature-preserving maps: inherited wires, an injective fresh-to-source map, and the combined source-to-target-plus-fresh map.
- [ ] Define the freshened selected region, conditional fresh-root pins, and `copied` as the pinned copied block conjoined with the remainder.
- [ ] Define conditional inherited residue pins from removed-copy usage and remainder non-usage, then define `uncopyResidue` by adjoining those pins to the remainder without new locals.
- [ ] Add only the one-sided DCA/rootedness and incidence-append facts required to prove copy canonicality; move the operation-neutral context replacement canonicality theorem from the erasure namespace into `Diagram.Scope` and reuse it for the removal iff boundary rather than duplicate a context traversal.
- [ ] Prove `copied` canonical and enclosing-context canonical by monotonicity from the exact nested occurrence.
- [ ] Prove `uncopyResidue` canonical and enclosing-context canonical by inherited-wire nonemptiness equivalence.
- [ ] Define the local relation with copy and residue-removal constructors, and define the whole rule as its symmetric exact nested-context lift.
- [ ] Strict-check, focused-build, scan for normalization/search/stored scope, and commit the green rule kernel.

### Task 4: Prove iteration and deiteration sound

**Files:**
- Replace: `VisualProof/Rule/Soundness/Iteration.lean`

**Interfaces:**
- Consumes: exact typed freshening, pin truth, copy/residue definitions, and recursive context equivalence.
- Produces: local equivalence for both constructors and `Iteration.sound`.

- [ ] Prove typed `WireFreshening.env_eq` by constructing fresh values from the source values identified by `sourceOfFresh`.
- [ ] Enter the copy local-equivalence owner theorem as RED only after pin denotation and environment transport compile.
- [ ] Prove copy equivalence by the existing selected witness, fresh environment, relation-free renaming semantics, conjunction, and pin truth.
- [ ] Enter and prove residue-removal equivalence; residue identities contribute only truth, while the copied selected factor follows from the surviving original through the descendant context.
- [ ] Lift both local equivalences through the exact outer and descendant contexts and open isomorphisms.
- [ ] Strict-check, focused-build, scan for admissions and secondary traversals, and commit the green soundness slice.

### Task 5: Implement exact forward and backward runners

**Files:**
- Replace: `VisualProof/Rule/Executable/Iteration.lean`

**Interfaces:**
- Produces: computable `runForward`, computable `runBackward`, and exact coverage of `Rule.Iteration` in both directions up to `OpenDiagram.Isomorphic`.

- [ ] Define four direct forward index shapes: copy, plain removal with target-canonical proof, residue removal, and the converse residue-to-copy case; define the corresponding backward family without storing a target diagram.
- [ ] Implement each runner as one `NestedOccurrence.replace` using the indexed body and derived or supplied canonical proof.
- [ ] Enter `forward_exact` as RED after both runners compile without admissions; prove it by eliminating the exact relation or index constructor.
- [ ] Enter and prove `backward_exact`, reusing symmetry of the established rule rather than duplicating relation reasoning.
- [ ] Strict-check the rule, soundness, and executable modules; run focused builds, admission/forbidden scans, and `git diff --check`.
- [ ] Run the architectural gates against the final diff, commit the green executable slice, and leave the worktree clean.
