# Lean Module Boundary Reconstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan task-by-task. Subagents are
> disabled by repository instruction.

**Goal:** Replace all oversized maintained Lean files with responsibility-focused
modules and enforce a hard 3,000-line source-file ceiling.

**Architecture:** Preserve declaration statements and order while moving
contiguous responsibility groups into explicit dependency-chain modules. Keep the
former public paths as import-only umbrellas and make the source-size audit part
of the normal formalization oracle.

**Tech Stack:** Lean 4, Lake, Node.js.

## Global Constraints

- No repository-owned text artifact may exceed 3,000 physical lines. Exclusions
  are limited to version-control metadata, dependencies, caches, and derived
  build outputs.
- No `sorry`, `admit`, or project `axiom`.
- Do not duplicate declarations or retain a legacy implementation body.
- Preserve unrelated user changes.
- Lean typechecking is the authoritative implementation check; no artificial TDD
  red phase is required for declaration moves.

---

### Task 1: Split the concrete elaboration compiler

**Files:**

- Replace: `VisualProof/Diagram/Concrete/Elaboration/Compile.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile/Kernel.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile/Region.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile/Elaborate.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile/Certified.lean`
- Create: `VisualProof/Diagram/Concrete/Elaboration/Compile/Occurrence.lean`

**Interfaces:**

- `Kernel` owns node and occurrence compilation.
- `Region` owns `finishRegion`, `finishRoot`, `compileRegion?`, `compileRoot?`,
  completeness, and ordinary equivariance.
- `Elaborate` owns checked/open elaboration APIs.
- `Certified` owns beta-eta certified compiler transport.
- `Occurrence` owns public concrete/open occurrence lifting and examples.

- [ ] Move each declaration group without changing statements.
- [ ] Make `Compile.lean` import the five modules only.
- [ ] Run `lake build VisualProof.Diagram.Concrete.Elaboration.Compile`.

### Task 2: Split structural rules

**Files:**

- Replace: `VisualProof/Rule/Structural.lean`
- Create modules under `VisualProof/Rule/Structural/` for spawn core, spawn
  transport, open spawn, wire operations, modal operations, iteration/erasure,
  and semantic laws.

**Interfaces:**

- Spawn modules own compiler and open-root transport.
- Wire owns sever/join provenance and applications.
- Modal owns double-cut and vacuous operations.
- Iteration owns iteration, deiteration, and erasure.
- Semantics owns the final logical laws.

- [ ] Move each declaration group without changing statements.
- [ ] Make `Structural.lean` import the focused modules only.
- [ ] Run `lake build VisualProof.Rule.Structural`.

### Task 3: Split splice syntax, layout, and executable correspondence

**Files:**

- Replace: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Create focused modules beneath
  `VisualProof/Diagram/Concrete/Subgraph/Splice/`.

**Interfaces:**

- `Trace` owns compiler traces and views.
- `Input/Quotient` owns `Input`, admissibility, quotienting, and coalescing.
- `Input/Layout/*` owns layout construction and compiler correspondence.
- `Input/CompilerSource` owns executable splice source/open equivalence.
- `Reassembly`, `Removal`, and `Examples` own their independent surfaces.

- [ ] Move syntax/layout/executable declaration groups.
- [ ] Typecheck the last executable-correspondence module.

### Task 4: Split paired semantic transport and soundness

**Files:**

- Create route/alignment, focused-environment, presentation, pattern-simulation,
  and soundness modules beneath the splice directory.

**Interfaces:**

- Presentation modules own quotient maps, occurrence maps, binder witnesses,
  context relations, and local transport.
- Pattern simulation owns intrinsic-pattern compiler simulation.
- Soundness owns focused, root, nested, and compiled-source entailment theorems.

- [ ] Move paired semantic declaration groups without changing theorem
  statements.
- [ ] Resume and finish the active root theorem in `Soundness.lean`.
- [ ] Make `Splice.lean` import the final focused modules only.

### Task 5: Enforce the ceiling

**Files:**

- Create: `scripts/check-source-size.mjs`
- Modify: `scripts/check-formalization.mjs`

**Interfaces:**

- `check-source-size.mjs` exits nonzero and prints every violating path and line
  count.
- `check-formalization.mjs` invokes it before `lake build`.

- [ ] Implement recursive repository-text scanning with a 3,000-line maximum,
      including ignored in-repository workflow artifacts.
- [ ] Run `node scripts/check-source-size.mjs`.
- [ ] Confirm the three umbrella files contain imports only.

### Task 6: Full validation and receipt

- [ ] Run `lake build`.
- [ ] Run the placeholder/axiom audit.
- [ ] Run the exact proof-step correspondence audit.
- [ ] Run `npm test`.
- [ ] Run `npm run typecheck`.
- [ ] Append foundation-record conformance evidence and update the active goal
  receipt.
