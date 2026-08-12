# Symbolic Concrete Elaboration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make concrete elaboration compositional by storing concrete wire and binder identities in the sole compiled tree and deriving positional `Region` indices only at erasure, then prove bound-relation spawning through one structural graft.

**Architecture:** `CompiledRegion` is an origin-owned symbolic tree. Node items contain concrete wire owners and atom binders, while cut and bubble items contain symbolic child regions. A checked erasure environment converts those identities to the positional wire and relation indices required by `VisualProof.Diagram.Region`; splice compilation therefore maps ordinary identities and performs one host-focus graft, without transporting compiled results across list equalities.

**Tech Stack:** Lean 4, Lake, VisualProof concrete diagrams and intrinsic diagram syntax.

## Global Constraints

- Keep one compiler authority and one canonical focus.
- Do not add target search, route state, generic callback simulation, compiled-result casts, `HEq`, compatibility wrappers, or parallel compiler APIs.
- Every Lean dependency must be complete before an owning theorem enters RED; only that owning theorem may temporarily use `sorry`.
- Every checkpoint must pass strict warning-as-error compilation, its focused Lake build, forbidden-authority scans, and `git diff --check` before commit.

---

### Task 1: Symbolic compiler result and erasure environment

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/Compile/Tree.lean`
- Modify: `VisualProof/Concrete/Elaboration/Context.lean`

**Interfaces:**
- Produces: origin-owned `CompiledRegion`, `CompiledItem`, and `CompiledItems`; `WireContext.position`; `BinderContext.relationAt`; symbolic erasure to `Region`.

- [ ] Replace context-indexed item payloads with ordinary concrete identities:

```lean
mutual
  inductive CompiledRegion (d : Diagram) where
    | mk (origin : Fin d.regionCount) (items : CompiledItems d)

  inductive CompiledItem (d : Diagram) where
    | atom (origin : Fin d.nodeCount) (binder : Fin d.regionCount)
        (arity : Nat) (ports : Fin arity -> Fin d.wireCount)
    | identity (origin : Fin d.nodeCount) (arity : Nat)
        (ports : Fin arity -> Fin d.wireCount)
    | cut (origin : Fin d.regionCount) (body : CompiledRegion d)
    | bubble (origin : Fin d.regionCount) (arity : Nat)
        (body : CompiledRegion d)

  inductive CompiledItems (d : Diagram) where
    | nil
    | cons (head : CompiledItem d) (tail : CompiledItems d)
end
```

- [ ] Define proof-driven position projections with exact specifications:

```lean
def WireContext.position (exact : context.Exact region)
    (wire : Fin d.wireCount) (visible : d.Encloses (d.wires wire).scope region) :
    Fin context.length

theorem WireContext.position_get ... :
  context.get (context.position exact wire visible) = wire

def BinderContext.relationAt (covers : binders.Covers region)
    (binder parent : Fin d.regionCount) (arity : Nat)
    (bubble : d.regions binder = .bubble parent arity)
    (encloses : d.Encloses binder region) : RelVar rels arity

theorem BinderContext.relationAt_lookup ... :
  binders binder = some ⟨arity, binders.relationAt covers binder parent arity bubble encloses⟩
```

- [ ] Define one recursive erasure consuming a source-validity proof and exact wire/binder environments; do not store positional indices in the tree.
- [ ] Run strict checks for `Context.lean` and `Tree.lean`, build `VisualProof.Concrete.Elaboration.Compile.Tree`, scan for forbidden authorities, and commit.

### Task 2: Total symbolic compiler

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/Compile/Kernel.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compile/Region.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compile/Elaborate.lean`

**Interfaces:**
- Consumes: Task 1 symbolic tree.
- Produces: one total well-founded compiler `compileRegion`; canonical checked root compilation and erasure.

- [ ] Replace positional `compileNode?` with a symbolic node constructor that finds the unique concrete wire owning each required endpoint and stores that wire.
- [ ] Retain one descendant-ranked recursive `compileRegion (d) (hwf) (origin)`; its item-list worker is private and structural.
- [ ] Prove node shape, port ownership, item origins, and region-origin laws adjacent to the compiler.
- [ ] Define `CheckedOpen.compilation` directly from the total compiler and `CheckedOpen.elaborate` solely by symbolic erasure under `openRootWires_exact` and empty binder coverage.
- [ ] Run strict checks for all three modules, focused builds through `Compile.Elaborate`, scan, and commit.

### Task 3: Migrate semantic consumers to the sole symbolic result

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/Compile/Certified.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compile/Occurrence.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compiled.lean`
- Modify: `VisualProof/Concrete/Encode.lean`

**Interfaces:**
- Consumes: Task 2 total symbolic compiler.
- Produces: certified isomorphism, canonical source focus, and encoding correctness without a second compiler presentation.

- [ ] Rewrite certified equivariance as structural equality/isomorphism of symbolic trees followed by one erasure-environment equivalence.
- [ ] Make `CompiledRegion.focus?` search the single origin-owned tree and keep `CompiledSite` as derived namespace functions only.
- [ ] Define `CompiledSite.context`, `body`, and `rebuild` from the symbolic zipper plus the same erasure environment used by checked elaboration.
- [ ] Migrate encoding proofs to the symbolic compiler’s origin and port-owner laws; remove positional compiler motives.
- [ ] Strict-check all four modules, build `VisualProof.Concrete.Encode`, run the full existing elaboration closure, scan, and commit.

### Task 4: Remove displaced positional compiler surface

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/Compile/Kernel.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compile/Region.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compile/Certified.lean`
- Modify: `VisualProof/Concrete/Elaboration/Compiled.lean`

**Interfaces:**
- Produces: no context-indexed `CompiledItem`, exact-signature call family, positional map-success theorem, or positional focus reconciliation.

- [ ] Delete every now-unused `CompilerCall`, context-indexed map/equivariance helper, block compiler callback, and result-transport theorem.
- [ ] Confirm repository-wide absence of `CompilerCall`, `compileItems?_map_success`, compiled-result casts, `HEq`, route/focus compatibility layers, and obsolete constructor APIs.
- [ ] Run the complete elaboration and encoding builds, authority audits, diff check, and commit.

### Task 5: Symbolic splice transformation

**Files:**
- Modify: `VisualProof/Concrete/Elaboration/SpliceLayout.lean`
- Create: `VisualProof/Concrete/Elaboration/SpliceCompilation.lean`
- Modify: `VisualProof/Concrete/Elaboration.lean`

**Interfaces:**
- Consumes: source symbolic frame/pattern trees and `PlugLayout` allocation maps.
- Produces: one source-derived target symbolic root and its exact endpoint graft.

- [ ] Define direct identity maps for frame/material regions, nodes, wires, and binders from `PlugLayout`; no configurable map record.
- [ ] Prove one structural material-subtree map and one retained-frame-away map over symbolic trees.
- [ ] Prove the owning endpoint theorem in RED, with the target block order `frame nodes ++ pattern nodes ++ frame children ++ pattern children`.
- [ ] Replace RED with the kernel-checked endpoint proof, then graft upward through the sole source zipper once.
- [ ] Strict-check, focused-build, forbidden-scan, diff-check, and commit.

### Task 6: Canonical context replacement

**Files:**
- Create: `VisualProof/Concrete/Elaboration/SpliceReplacement.lean`
- Modify: `VisualProof/Concrete/Elaboration.lean`

**Interfaces:**
- Consumes: Task 5 target symbolic root and source compiled context.
- Produces: `CompiledSite.splice` with no caller-provided compiler data.

- [ ] Derive admissibility, canonical layout, target graph equality, and target well-formedness from raw splice success and receipt packing.
- [ ] Identify the constructed symbolic root with the receipt target’s sole compiler by structural compiler determinism.
- [ ] Build the endpoint four-block braid to `Region.spliceAt` using existing `ItemSeqIso` append laws.
- [ ] Define `CompiledSite.splice` returning `Diagram.ContextReplacement` and prove exact source/target endpoints.
- [ ] Strict-check, focused-build, scan, diff-check, and commit.

### Task 7: Bound-relation spawn refinement and final validation

**Files:**
- Modify: `VisualProof/Refinement/Step/Erasure.lean`
- Modify: `VisualProof/Refinement/Step.lean`

**Interfaces:**
- Consumes: `CompiledSite.splice`.
- Produces: kernel-checked `Erasure.boundRelationSpawn` and aggregate execution refinement.

- [ ] Enter `Erasure.boundRelationSpawn` as the sole RED theorem after every dependency is complete.
- [ ] Prove it from `CompiledSite.splice`, the spawn polarity guard, and the rule-level local introduction constructor.
- [ ] Replace the aggregate theorem’s corresponding branch with the completed family proof.
- [ ] Run strict checks on the full theorem closure, `lake build`, computability and authority audits, forbidden scans, and `git diff --check`.
- [ ] Review the final complexity ledger: one compiler, one focus, one splice traversal, no stored positional mirrors; commit all completed work and verify a clean repository.
