# Relational Wire Primitives Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add the nine remaining primitive HOL rule families to the intrinsic Lean calculus as relations, prove each relation sound, and provide the complete exact executor interface for all seventeen semantic operations.

**Architecture:** A shared, intrinsically typed uniform-wire transformation relates a source region to the uniquely constructed target obtained by changing one bound relation wire and every one of its applied ends. The nine public local relations package operation-specific evidence over that transformation and are lifted with `Rule.Contextual`, so polarity and target validity remain governed by the existing calculus. Each public family receives source-indexed forward/backward indices, total runners, exactness in both directions, compiled runners, and target-isomorphism closure; paired operations share one family while retaining distinct executor constructors. Argument permutation is one parametric operation whose inverse permutation supplies the converse execution.

**Authoritative design:** `docs/superpowers/specs/2026-07-29-primitive-wire-quantifier-rules-design.md` and the current intrinsic `Region`/`OpenDiagram` representation. Identity-leaf is the relation-wire primitive from that inventory; the separate identity-apparatus calculus remains governed by `docs/superpowers/specs/2026-08-12-derived-scope-identity-rules-design.md`.

**Tech Stack:** Lean 4, Lake, Mathlib-free project kernel, theorem-driven RED/GREEN development.

---

## Completion contract

The nine new public rule families are:

1. cut shape: cut-wrap / cut-absorb;
2. parallel shape: parallel-split / parallel-fuse;
3. endpoint set: ends-delete / ends-spawn;
4. arity: arity-shift / arity-unshift;
5. argument permutation: argument-permute;
6. diagonal argument: argument-duplicate / argument-contract;
7. argument projection: argument-drop / argument-extend;
8. formal application: apply-formal / abstract-formal;
9. identity leaf: identity-leaf / identity-abstract.

The seventeen semantic operations are the named constructors above. Every family, including argument permutation, must satisfy the same executor contract:

- source-indexed `ForwardIndex` and `BackwardIndex`;
- total `runForward` and `runBackward`;
- `forward_exact` and `backward_exact`;
- compiled forward and backward runners;
- target-isomorphism closure in both directions.

Every owning soundness or exactness theorem is developed RED/GREEN: all definitions in its dependency closure compile first, the production theorem alone may temporarily contain `sorry`, then that theorem is closed with a kernel-checked proof before proceeding. No fixture theorem is added merely to demonstrate elaboration.

## Task 1: Establish the shared uniform transformation

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Transform.lean`
- Create: `VisualProof/Rule/WirePrimitive.lean`

1. State an intrinsically typed transformation of one locally bound relation wire, including its source arity, target wire bundle, and a recursive item/region traversal that requires every occurrence of the selected wire to be an application and transforms every such application.
2. Make the transformation evidence determine the target region; do not store an arbitrary target beside a proposition that merely claims it is related.
3. Prove structural lemmas for untouched wires, recursive cuts, item sequences, and interpretation under a supplied pointwise body law.
4. Compile the new modules with `lake env lean` and run the relevant `sorry` audit.
5. Commit the closed shared kernel.

## Task 2: Formalize the three content-shape families

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Content.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive/Content.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive/Content.lean`

1. Define relational local evidence and contextual public rules for cut-wrap/absorb, parallel-split/fuse, and ends-delete/spawn.
2. For cut shape, prove the complement witness laws in both directions.
3. For parallel shape, prove the intersection witness and diagonal introduction laws in both directions.
4. For endpoint deletion/spawning, prove the one available witness direction and discharge the contextual gate through polarity.
5. Define the six executor constructors and runners.
6. Prove exactness forward and backward, compiled-runner correctness, and target-isomorphism closure for all three families.
7. Compile each owning module, audit it for `sorry`, and commit the closed cluster.

## Task 3: Formalize arity and argument permutation

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Arity.lean`
- Create: `VisualProof/Rule/WirePrimitive/Permutation.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive/Arity.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive/Permutation.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive/Arity.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive/Permutation.lean`

1. Define arity-shift/unshift with one fresh locally scoped argument wire per site and prove the existential-extension and inhabited-domain witness laws.
2. Define a typed argument permutation and its inverse law; reject non-bijections in the index type rather than at runner time.
3. Prove both public contextual relations sound.
4. Define the two arity executors and the one parametric permutation executor, plus the complete family-level forward/backward interfaces.
5. Prove exactness, compiled-runner correctness, and target-isomorphism closure.
6. Compile, audit for `sorry`, and commit the closed cluster.

## Task 4: Formalize duplicate/contract and drop/extend

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Argument.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive/Argument.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive/Argument.lean`

1. Define argument-duplicate/contract using a typed selected position and prove diagonal substitution in both directions.
2. Define argument-drop/extend with per-site attachments, retaining the ungated equivalence precisely for uniform visible attachment and otherwise applying the established directional gate.
3. Prove both public contextual relations sound without assuming uniformity in the gated case.
4. Define the four semantic executor constructors and the complete forward/backward interfaces.
5. Prove exactness, compiled-runner correctness, and target-isomorphism closure.
6. Compile, audit for `sorry`, and commit the closed cluster.

## Task 5: Formalize formal-application and identity-leaf

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Leaf.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive/Leaf.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive/Leaf.lean`

1. Define apply-formal/abstract-formal, with the selected formal required by its type to be a relation over the remaining arguments.
2. Define identity-leaf/identity-abstract for a relation application whose arguments share one signature and meet the identity-node arity requirement of the current intrinsic representation.
3. Prove the full-function-model application witness and equality-relation witness, then lift both through contextual polarity.
4. Define the four semantic executor constructors and the complete forward/backward interfaces.
5. Prove exactness, compiled-runner correctness, and target-isomorphism closure.
6. Compile, audit for `sorry`, and commit the closed cluster.

## Task 6: Integrate the nine families into the calculus

**Files:**

- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Create: `VisualProof/Rule/Soundness/WirePrimitive.lean`
- Create: `VisualProof/Rule/Executable/WirePrimitive.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/Rule/Executable.lean`

1. Export every rule, soundness theorem, and executor family from the three umbrellas.
2. Add exactly nine constructors to `Rule.Step` and extend `Step.iso` for each.
3. Extend aggregate step soundness with all nine cases.
4. Expose the seventeen named semantic operations and all family executor theorems through the executable umbrella.
5. Add theorem-level inventory checks only where they assert semantic coverage; do not add source-string or constructor-count tests.
6. Compile the aggregate modules and commit the integration.

## Task 7: Validate the completed calculus

1. Run `lake build` from a clean incremental state and repair all in-repository failures.
2. Run `rg -n '\bsorry\b|admit|axiom' VisualProof/Rule VisualProof/Rule.lean` and classify every match; the new dependency closure must contain no proof placeholder or new axiom.
3. Immediately after `lake build`, run
   `rg -n '\bsorry\b' VisualProof --glob '*.lean'`; every match must be an
   explicitly owned unfinished production theorem.
4. Verify the public inventory mechanically from Lean declarations: nine new `Step` families and seventeen named semantic executor constructors.
5. Review the diff for obsolete authority, adapters, unrelated cleanup, and unintended changes.
6. Use the verification-before-completion and finishing-a-development-branch workflows, then commit any final task-owned corrections and confirm `git status --short` is empty.
