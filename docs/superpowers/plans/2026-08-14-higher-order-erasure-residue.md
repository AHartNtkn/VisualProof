# Higher-Order Erasure Residue Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define sound, directly executable recursive erasure whose immediate result replaces every erased occurrence of a surviving wire with a unary identity and whose two executable directions exactly cover the rule up to open-diagram isomorphism.

**Architecture:** Keep `Region` / `Item` / `ItemSeq` and computed-DCA canonicality unchanged. Complete the typed structural and semantic modules in erasure's import closure, define one recursive material-to-residue projection, and make `Erasure.Local` replace the material block by that residue. The runner consumes an explicitly indexed residue and never searches the source; proof fields establish that the supplied residue is the canonical structural projection.

**Tech Stack:** Lean 4.30.0, Lake, indexed recursive syntax, proposition-valued rule relations, direct computable runners.

## Global Constraints

- Keep the recursive syntax and DCA ownership model unchanged.
- A unary identity is `Item.identity signature 1 (fun _ => wire)`.
- Emit one unary identity per erased port occurrence of an inherited material wire, in recursive structural order.
- Ignore material-local wires because they disappear with the erased material.
- Do not search the source or construct a target witness inside either runner.
- Do not add stored scope, wire rehoming, whole-diagram normalization, compatibility types, or a second erasure relation.
- Every production theorem dependency is complete before RED; only the owning theorem proof may contain `sorry` during RED.
- Stop if canonicality requires rebuilding unrelated regions or if semantic soundness requires a non-structural traversal.

---

### Task 1: Complete erasure's typed structural boundary

**Files:**
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Occurrence.lean`
- Modify: `VisualProof/Rule/Relation.lean`

**Interfaces:**
- Consumes: typed `Var`, `Vars`, `WireRenaming`, cut-only `DiagramContext`, canonical `OpenDiagram`.
- Produces: signature-preserving `WireEquiv`, recursive `RegionIso`/`ItemIso`/`ItemSeqIso`, typed `spliceAt`, proof-bearing occurrences, and typed contextual rules.

- [ ] **Step 1:** Replace numeric finite-wire isomorphisms by `WireEquiv source target`, containing forward and inverse `WireRenaming`s and both inverse laws.
- [ ] **Step 2:** Replace `RegionIso`, `ItemIso`, and `ItemSeqIso` directly over typed contexts; retain item-sequence permutation and delete relation-context and bubble cases.
- [ ] **Step 3:** Port only structural reflexivity, symmetry, transitivity, append, and context-fill laws required by open isomorphism and contextual erasure.
- [ ] **Step 4:** Port `Region.adjoinAt` and `Region.spliceAt` using `WireRenaming`; no relation-renaming parameter remains.
- [ ] **Step 5:** Make `Occurrence` carry the canonicality proof for its filled source, and make `Contextual` carry the canonicality proof for its filled target.
- [ ] **Step 6:** Run strict checks for all five modules and commit the independently green boundary.

### Task 2: Complete erasure's typed semantic boundary

**Files:**
- Modify: `VisualProof/Diagram/Environment.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/Semantics/Context.lean`
- Modify: `VisualProof/Diagram/Semantics/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics/Algebra.lean`
- Modify: `VisualProof/Rule/Soundness/Contextual.lean`

**Interfaces:**
- Consumes: recursive typed syntax and typed isomorphisms.
- Produces: typed signature values, typed environments, recursive denotation, semantic isomorphism transport, context polarity transport, and contextual soundness.

- [ ] **Step 1:** Define `Sig.denote`, typed environment tuples, lookup, append, renaming, and `Vars` evaluation.
- [ ] **Step 2:** Define denotation by the existing recursive cases: existential local environment, relation-valued atom head application, all-equal identity, cut negation, and sequence conjunction.
- [ ] **Step 3:** Define open denotation using an external typed environment whose boundary projection equals the supplied typed boundary values.
- [ ] **Step 4:** Port isomorphism invariance by the existing mutual structural induction and context monotonicity/antitonicity by the existing cut-context induction.
- [ ] **Step 5:** Port the typed `spliceAt` host implication used by erasure soundness.
- [ ] **Step 6:** Run strict checks and commit the independently green semantic boundary.

### Task 3: Define canonical unary erasure residue

**Files:**
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/Scope.lean`

**Interfaces:**
- Produces: `WireProjection`, `Region.erasureResidue`, `Region.eraseAt`, residue denotation, incidence-count preservation, and canonicality preservation.

- [ ] **Step 1:** Define a signature-preserving partial `WireProjection source target` and its extension across locally owned wires, mapping inherited wires and rejecting new locals.
- [ ] **Step 2:** Define mutually recursive residue functions over regions, items, item sequences, and argument tuples. Every projected port emits `.cons (.identity signature 1 (fun _ => projectedWire))`; cut contents flatten into the residue; unprojected local ports emit nothing.
- [ ] **Step 3:** Define:

  ```lean
  def Region.eraseAt
      (hostItems : ItemSeq (outer ++ hostLocals))
      (material : Region materialOuter)
      (wireMap : WireRenaming materialOuter (outer ++ hostLocals)) :
      Region outer :=
    .mk hostLocals
      (hostItems.append
        (material.erasureResidue (WireProjection.total wireMap)))
  ```

- [ ] **Step 4:** Prove every residue sequence denotes truth for every typed environment.
- [ ] **Step 5:** Prove `Region.eraseAt` is canonical whenever the corresponding `Region.spliceAt` source is canonical. The proof must use local incidence-path/DCA lemmas; it must not inspect an enclosing open diagram.
- [ ] **Step 6:** Validate strict compilation and commit the residue kernel.

### Task 4: Replace erasure relation and executable coverage

**Files:**
- Modify: `VisualProof/Rule/Erasure.lean`
- Modify: `VisualProof/Rule/Executable/Erasure.lean`

**Interfaces:**
- Produces: residue-based `Erasure.Local.erase`, direct `runForward`/`runBackward`, and exact forward/backward coverage up to `OpenDiagram.Isomorphic`.

- [ ] **Step 1:** Replace the local constructor endpoints with `Region.spliceAt hostItems material wireMap` and `Region.eraseAt hostItems material wireMap`.
- [ ] **Step 2:** Replace both index families with typed host/material contexts, `WireRenaming`, an exact occurrence, polarity evidence, and the target canonicality derived from `Region.eraseAt_canonical` plus context canonicality.
- [ ] **Step 3:** Keep runners direct: each branch calls `withBody` on the indexed replacement and supplied/derived canonical proof. No runner traverses `source` or recomputes the residue.
- [ ] **Step 4:** Enter `forward_exact` and `backward_exact` as RED only after all index and runner definitions compile without admissions.
- [ ] **Step 5:** Prove exactness by eliminating indices and contextual relation witnesses; remove every old constructor and parameter shape.
- [ ] **Step 6:** Run strict checks and commit the green relation/execution slice.

### Task 5: Prove erasure soundness and audit the adjacent iteration boundary

**Files:**
- Modify: `VisualProof/Rule/Soundness/Erasure.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Read-only audit: `VisualProof/Rule/Iteration.lean`
- Read-only audit: `VisualProof/Rule/Executable/Iteration.lean`
- Read-only audit: `VisualProof/Rule/Soundness/Iteration.lean`

**Interfaces:**
- Produces: `Erasure.Local.sound` and whole-diagram `Erasure.sound` for typed boundary environments.

- [ ] **Step 1:** Enter `Erasure.Local.sound` as RED with the exact implication from the spliced source to the residue target.
- [ ] **Step 2:** Prove it by decomposing `spliceAt`, retaining host denotation, and satisfying the residue conjunct with the generic residue-truth theorem.
- [ ] **Step 3:** Prove whole-diagram soundness through `Contextual.sound` without a new traversal.
- [ ] **Step 4:** Run strict erasure relation, executable, and soundness checks; build their aggregate import closure; scan for displaced relation/bubble syntax, admissions, `HEq`, target search, and raised limits.
- [ ] **Step 5:** Audit deiteration only far enough to determine whether removing copied incidences requires the same residue or whether the surviving original already supplies DCA evidence. Do not edit iteration in this task. Stop and report any semantic decision or representation conflict.
- [ ] **Step 6:** Run `git diff --check`, commit the soundness slice, and report validation and the iteration audit.
