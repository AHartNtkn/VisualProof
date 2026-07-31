# Primitive Wire-Quantifier Lean Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the Lean formalization for the merged primitive
wire-quantifier proof language, including the unfinished Phase 3 proof/replay
stack, and mechanically prove that the primitive compiler makes the
monolithic strongest-form relation sever/join rules redundant.

**Architecture:** Lean keeps the monolithic relation-content sever/join only
as a semantic specification. The durable kernel is the exact 34-constructor
TypeScript `ProofStep` language. Small checked concrete primitive receipts
feed one generic uniform-site witness theorem; an authoring-layer compiler
emits checked primitive programs and a redundancy theorem relates their
normalized result to the monolithic specification. The completed Phase 3
stack then proves one-step, replay, theorem, citation, and ordered-theory
soundness and checks TypeScript/Lean tag parity mechanically.

**Tech stack:** Lean 4/Lake, TypeScript, Node.js, Vitest, and the repository's
existing `formal:size`, typecheck, unit-test, and Playwright gates.

## Authority, scope, and supersession

This plan is the continuing execution authority for:

- the Lean strategy and later 2026-07-30 amendments in
  `docs/superpowers/specs/2026-07-29-primitive-wire-quantifier-rules-design.md`;
- the unfinished work in Tasks 7–11 of
  `docs/superpowers/plans/2026-07-27-zero-signature-hol-phase-3-lean-semantics.md`;
- the merged TypeScript kernel produced by
  `docs/superpowers/plans/2026-07-30-primitive-wire-quantifier-rules-ts.md`.

The completed Phase 3 Tasks 1–6 remain the semantic foundation and are not
replanned. This plan supersedes the stale parts of Tasks 7–11:

- the durable language now has **34**, not 15, tags;
- backward erasure is legal in a negative region, following the common
  flipped-polarity law;
- generic wire sever/join replaces the iota-only public primitive;
- `IdentityRetarget` is removed and substitution is derived from plain
  iteration, scoped sever, and eager one-point normalization;
- the monolithic relation rule is a specification theorem, never a durable
  `ProofStep`;
- `refLeaf`/`refAbstract` are formalized because the merged kernel keeps
  definitions folded as macros; their soundness reduces to definition lookup
  and fold/unfold transparency;
- uniform, scope-visible `argDrop`/`argExtend` is an equivalence in the merged
  kernel, while per-site attachments retain the join/sever polarity gates.

Where the original primitive design and the completed TypeScript plan differ,
the merged durable TypeScript API controls cross-language correspondence. The
design still controls the semantic obligations: uniform all-end action,
pointwise witnesses, compiler redundancy, insertion/ref conservativity, and
the derived per-site extension theorem.

## Exact durable step inventory

`VisualProof.StepTag.all` and the checked `ProofStep` sum must use this exact
order, matching `src/kernel/proof/step.ts`:

1. `refSpawn`
2. `atomSpawn`
3. `identityInsert`
4. `wireJoin`
5. `erasure`
6. `wireSever`
7. `iteration`
8. `deiteration`
9. `doubleCutIntro`
10. `doubleCutElim`
11. `theorem`
12. `vacuousIntro`
13. `vacuousElim`
14. `unfold`
15. `fold`
16. `cutWrap`
17. `cutAbsorb`
18. `parallelSplit`
19. `parallelFuse`
20. `endsDelete`
21. `endsSpawn`
22. `arityShift`
23. `arityUnshift`
24. `argPermute`
25. `argDuplicate`
26. `argContract`
27. `argDrop`
28. `argExtend`
29. `applyFormal`
30. `abstractFormal`
31. `identityLeaf`
32. `identityAbstract`
33. `refLeaf`
34. `refAbstract`

## Global constraints

- Every wire-content or wire-argument primitive transforms all applied-head
  endpoints of its acted-on wire uniformly. Merge alone may consume
  non-head endpoints. No per-end primitive is introduced.
- Every directional receipt stores orientation and checker-derived cut
  polarity. Join-family rules require negative forward / positive backward;
  sever-family rules require positive forward / negative backward.
  Equivalences are ungated.
- Public soundness is truth in every full `Model`. Generic lemmas may quantify
  over `PreModel` when the required semantic witnesses are explicit. Fullness
  is used exactly where a relation value must be synthesized; audits must
  report that boundary rather than preserve the old “only monolithic
  sever/join use fullness” claim.
- Fresh ids, selected regions, endpoint partitions, ordered formals, ambient
  parameters, definition identities, and boundary transports are all
  checker-owned receipts. A public soundness theorem accepts no semantic
  premise manufactured by its caller.
- Normalized concrete results are compared by checked concrete isomorphism
  with exact ordered boundary transport. Source-name equality is never used
  as a substitute for fresh-name equivalence.
- The monolithic relation rule may be imported only by the compiler
  correctness/redundancy layer and its fixtures. It must not appear in
  `StepTag`, `ProofStep`, replay JSON correspondence, or application dispatch.
- Delete displaced paths and declarations. Do not retain iota aliases,
  identity-retarget adapters, monolithic proof-step variants, or parallel tag
  authorities.
- Keep every repository-owned Lean source below the existing size limit.
  Split concrete construction, semantics, compiler, and fixtures before a
  module approaches the limit.
- At every task: add a RED fixture first, run its focused Lean target, make it
  GREEN, then run `lake build` and `npm run formal:size` before committing.

---

### Task 1: Correct the Phase 3 structural baseline and freeze 34 tags

**Files:**

- Modify: `VisualProof/Rule/Tag.lean`
- Modify: `VisualProof/Rule/Structural.lean`
- Modify: `VisualProof/Rule/StructuralFixtures.lean`
- Create: `VisualProof/Rule/StructuralAudit.lean`
- Modify: `VisualProof.lean`
- Test: `tests/architecture/lean-semantics.test.ts`

**Interfaces:**

- `StepTag.all.length = 34` and `StepTag.all.Nodup`.
- `StructuralErasureReceipt.sound` accepts forward-positive and
  backward-negative erasure.
- Structural insertion remains forward-negative / backward-positive.

- [x] **Step 1: Add RED inventory, Phase 3 audit, and polarity fixtures.**
  Change the Lean length theorem and architecture expectation to 34. In
  `StructuralAudit.lean`, pin the completed Task 7 authority: explicit direct
  nodes plus selected subtrees, explicit anchor-scoped internal wires, one
  boundary class per touching wire, generalized insertion outside the copied
  content, ordinary iteration/deiteration, double-cut, and vacuous-wire
  receipts. Add a backward-negative erasure fixture and a backward-positive
  refusal fixture. Preserve the existing insertion matrix.
- [x] **Step 2: Run RED.**

  ```bash
  lake build VisualProof.Rule.Tag VisualProof.Rule.StructuralFixtures
  npx vitest run tests/architecture/lean-semantics.test.ts
  ```

- [x] **Step 3: Replace the tag inventory.** Add the 19 merged primitive tags
  in the exact order above. Keep one `StepTag.all`; do not add a second list
  for tooling.
- [x] **Step 4: Replace forward-only erasure.** Remove
  `backwardErasureForbidden`; check the selected site's parity against
  orientation, and prove the backward-negative case with the independently
  named negative-splice lemma required by the primitive design.
- [x] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  npx vitest run tests/architecture/lean-semantics.test.ts
  git add -- VisualProof.lean VisualProof/Rule/Tag.lean \
    VisualProof/Rule/Structural.lean \
    VisualProof/Rule/StructuralFixtures.lean \
    VisualProof/Rule/StructuralAudit.lean \
    tests/architecture/lean-semantics.test.ts
  git commit -m "refactor: align Lean structural rules with 34 proof steps"
  ```

---

### Task 2: Complete and isolate the monolithic specification rule

**Files:**

- Modify: `VisualProof/Diagram/Concrete/WireQuantifierRelationSeverSemantics.lean`
- Create: `VisualProof/Diagram/Concrete/WireQuantifierRelationSeverRemovalSemantics.lean`
- Create: `VisualProof/Diagram/Concrete/WireQuantifierRelationSeverInsertionSemantics.lean`
- Create: `VisualProof/Rule/MonolithicWireQuantifier.lean`
- Create: `VisualProof/Rule/MonolithicWireQuantifierFixtures.lean`
- Modify: `VisualProof/Rule/WireQuantifier.lean`
- Modify: `VisualProof/Rule/WireQuantifierFixtures.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `MonolithicRelationSeverInput`, `MonolithicRelationJoinInput`.
- `applyMonolithicRelationSever`, `applyMonolithicRelationJoin`.
- `relation_sever_sound`, `relation_join_sound`, both over full `Model`.
- `VisualProof/Rule/WireQuantifier.lean` temporarily owns only the still-live
  iota partition/merge API; relation-content variants no longer occur there.

- [x] **Step 1: Add RED relation-sever semantics.** Cover multiple disjoint
  exact copies at mixed parities, nullary content, ordered repeated formals,
  coherent ambient parameters, mismatched occurrences, overlap, parameter
  visibility, and fresh relation scope.
- [x] **Step 2: Complete concrete relation-sever soundness.** Reuse the landed
  occurrence extraction, singleton-removal, factorization, negative-splice,
  and relation-join receipt machinery. Construct the reified relation witness
  exactly once through `Model.reify`.
- [x] **Step 3: Isolate the specification API.** Move relation sever/join
  inputs, applied receipts, checkers, exports, theorems, and fixtures from the
  mixed facade to `MonolithicWireQuantifier`. Leave only the current iota
  partition/merge in `WireQuantifier` until Task 3 replaces it.
- [x] **Step 4: Audit specification-only reachability.**

  ```bash
  ! rg -n "MonolithicRelation|ContentOccurrence" \
    VisualProof/Rule/Tag.lean VisualProof/Rule/WireQuantifier.lean
  ```

- [x] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/WireQuantifierRelationSeverSemantics.lean \
    VisualProof/Diagram/Concrete/WireQuantifierRelationSeverRemovalSemantics.lean \
    VisualProof/Diagram/Concrete/WireQuantifierRelationSeverInsertionSemantics.lean \
    VisualProof/Rule/MonolithicWireQuantifier.lean \
    VisualProof/Rule/MonolithicWireQuantifierFixtures.lean \
    VisualProof/Rule/WireQuantifier.lean \
    VisualProof/Rule/WireQuantifierFixtures.lean
  git commit -m "feat: complete monolithic relation sever soundness"
  ```

---

### Task 3: Rebuild sever/join as generic signature-indexed partition/merge

**Files:**

- Create: `VisualProof/Diagram/Concrete/WirePartition.lean`
- Create: `VisualProof/Diagram/Concrete/WirePartitionSemantics.lean`
- Modify: `VisualProof/Diagram/Concrete/WireQuantifierBatchRemoval.lean`
- Modify: `VisualProof/Diagram/Concrete/WireQuantifierNaturality.lean`
- Modify: `VisualProof/Diagram/Concrete/WireQuantifierFrameNaturality.lean`
- Create: `VisualProof/Rule/WirePrimitive/Partition.lean`
- Create: `VisualProof/Rule/WirePrimitive/PartitionFixtures.lean`
- Create: `VisualProof/Rule/WirePrimitive.lean`
- Delete: `VisualProof/Diagram/Concrete/WireQuantifierIota.lean`
- Delete: `VisualProof/Diagram/Concrete/WireQuantifierIotaSemantics.lean`
- Delete: `VisualProof/Rule/WireQuantifier.lean`
- Delete: `VisualProof/Rule/WireQuantifierFixtures.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

```lean
structure WireSeverInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  wire : source.val.WireId
  keep : List (CEndpoint source.val.nodeCount)
  scope : source.val.RegionId

structure WireJoinInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  left : source.val.WireId
  right : source.val.WireId
```

- `applyWireSever`, `applyWireJoin`.
- `wire_sever_sound`, `wire_join_sound` over `PreModel`.
- `identity_substitution_derived_sound` completed in Task 4.

- [x] **Step 1: Add RED generic fixtures.** Cover `.iota`, `rel []`, nested
  relation signatures, moved-endpoint scope enclosure, chosen sever scope
  polarity, equal-signature join, incomparable scopes, and merge of a
  non-head endpoint. Require content primitives to reject the same non-head
  fixture later.
- [x] **Step 2: Rebuild the concrete owner.** Partition one wire's exact
  endpoint set into retained and moved endpoints. The fresh scope must be
  inside the old scope and enclose every moved endpoint. Merge comparable,
  equal-signature wires at the outer scope. Gate sever on the fresh scope and
  join on the inner scope.
- [x] **Step 3: Prove generic soundness.** Use the one-point quantifier laws
  for the selected `Sig`; no `Model.reify` or relation-content splice is
  permitted.
- [x] **Step 4: Remove iota authority.** Migrate all consumers and fixtures to
  the generic API, delete both iota modules, and remove `iota_sever_sound` /
  `iota_join_sound`. Delete the old mixed rule facade and make
  `Rule/WirePrimitive.lean` the sole primitive facade; the monolithic
  specification remains separately named.
- [x] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  ! rg -n "WireQuantifierIota|iota_sever_sound|iota_join_sound|Rule.WireQuantifier" \
    VisualProof VisualProof.lean
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/WirePartition.lean \
    VisualProof/Diagram/Concrete/WirePartitionSemantics.lean \
    VisualProof/Diagram/Concrete/WireQuantifierIota.lean \
    VisualProof/Diagram/Concrete/WireQuantifierIotaSemantics.lean \
    VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Partition.lean \
    VisualProof/Rule/WirePrimitive/PartitionFixtures.lean \
    VisualProof/Rule/WireQuantifier.lean \
    VisualProof/Rule/WireQuantifierFixtures.lean
  git commit -m "refactor: generalize Lean wire partition and merge"
  ```

---

### Task 4: Replace identity retargeting with derived substitution

**Files:**

- Modify: `VisualProof/Diagram/Concrete/IdentityNormalizationCore.lean`
- Modify: `VisualProof/Diagram/Concrete/IdentityNormalization.lean`
- Modify: `VisualProof/Diagram/Concrete/IdentityNormalizationTransport.lean`
- Modify: `VisualProof/Diagram/Concrete/IdentityNormalizationCollapseWellFormed.lean`
- Modify: `VisualProof/Diagram/Concrete/IdentityNormalizationCollapseSemantics.lean`
- Modify: `VisualProof/Diagram/Concrete/IdentityNormalizationSemantics.lean`
- Modify: `VisualProof/Rule/Identity.lean`
- Modify: `VisualProof/Rule/IdentityFixtures.lean`
- Modify: `VisualProof/Rule/Structural.lean`
- Modify: `VisualProof/Rule/StructuralFixtures.lean`
- Delete: `VisualProof/Rule/IdentityRetargetSemantics.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `normalizeOneIdentity` collapses when zero or one incident wire is scoped
  outside the identity's region; two or more outer wires decline.
- Ordinary iteration/deiteration payloads contain no retarget field.
- `identity_substitution_derived_sound` composes iteration, generic scoped
  sever, and normalization in both orientations.

- [x] **Step 1: Add RED one-point fixtures.** Cover all-co-scoped collapse,
  exactly-one-outer collapse with the outer wire as survivor, two-outer
  refusal, arbitrary signature, and both cut parities.
- [x] **Step 2: Add RED derived-substitution fixtures.** Starting from
  `id(a,b)` dominating `P(a)`, check plain iteration into the inner region,
  sever the copied identity port and `P` endpoint onto a fresh wire scoped at
  that region, and require eager normalization to land on `P(b)`. Cover
  forward and backward orientations.
- [x] **Step 3: Extend normalization.** Generalize the collapse proof from
  all-co-scoped to all-but-at-most-one-co-scoped and prove the one-point
  equivalence without changing degeneracy drop or same-region fusion.
- [x] **Step 4: Delete retarget authority.** Remove every
  `IdentityRetarget*` structure, checker, semantic theorem, structural copy
  payload, fixture, export, and import. Plain copy rules preserve attachment
  identities exactly.
- [x] **Step 5: Prove the derived theorem.** Compose the public ordinary
  iteration receipt, Task 3's generic scoped sever receipt, and
  `normalizeIdentities_sound`; prove exact normalized landing and ordered
  transport in both orientations.
- [x] **Step 6: Prove the displaced model is absent.**

  ```bash
  test ! -e VisualProof/Rule/IdentityRetargetSemantics.lean
  ! rg -n "IdentityRetarget|retargets|identity_retarget_sound" \
    VisualProof VisualProof.lean
  ```

- [x] **Step 7: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/IdentityNormalizationCore.lean \
    VisualProof/Diagram/Concrete/IdentityNormalizationCollapseWellFormed.lean \
    VisualProof/Diagram/Concrete/IdentityNormalizationCollapseSemantics.lean \
    VisualProof/Diagram/Concrete/IdentityNormalizationSemantics.lean \
    VisualProof/Rule/Identity.lean VisualProof/Rule/IdentityFixtures.lean \
    VisualProof/Rule/IdentityRetargetSemantics.lean \
    VisualProof/Rule/Structural.lean \
    VisualProof/Rule/StructuralFixtures.lean
  git commit -m "refactor: derive Lean identity substitution from scoped sever"
  ```

---

### Task 5: Prove the generic uniform-site witness theorem

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Site.lean`
- Create: `VisualProof/Rule/WirePrimitive/Witness.lean`
- Create: `VisualProof/Rule/WirePrimitive/WitnessFixtures.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `AppliedSite`: an atom-head endpoint, site region, ordered argument tuple,
  and its checked intrinsic frame factorization.
- `UniformSiteRewrite`: one signature, one binder scope, exhaustive
  source/target site lists, a position-preserving site correspondence, and
  checked normalized result equality.
- `HasEliminatingWitness`, `HasIntroducingWitness`.
- `uniform_join_sound`, `uniform_sever_sound`,
  `uniform_equivalence_sound`.

All construction fields are private and are populated only by primitive
checkers.

- [x] **Step 1: Add RED abstract examples.** Instantiate the statement with a
  nullary site under positive and negative contexts, mixed-parity sites, and a
  two-site shared witness. Add a negative example showing that separate
  per-site witnesses do not satisfy the API.
- [x] **Step 2: Define one site/frame authority.** An applied site records its
  atom-head endpoint, region, ordered arguments, and checked factorization.
  The all-sites collection proves it exhausts the acted-on wire.
- [x] **Step 3: Prove pointwise replacement.** Show one semantic witness makes
  every source/target site pair pointwise equal and that equality composes
  through all checked contexts. Mixed site polarity must disappear from the
  final obligation; only binder-scope polarity selects entailment direction.
- [x] **Step 4: Prove the three public forms.** A supplied eliminating witness
  gives join-family soundness, an introducing witness gives sever-family
  soundness, and both give an ungated equivalence. Keep this theorem generic
  over `PreModel`; later full-model instantiations construct the witnesses.
- [x] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Rule/WirePrimitive/Site.lean \
    VisualProof/Rule/WirePrimitive/Witness.lean \
    VisualProof/Rule/WirePrimitive/WitnessFixtures.lean
  git commit -m "feat: prove the uniform wire-site witness theorem"
  ```

---

### Task 6: Formalize content-shape primitive pairs

**Files:**

- Create: `VisualProof/Diagram/Concrete/WirePrimitive/Content.lean`
- Create: `VisualProof/Diagram/Concrete/WirePrimitive/ContentSemantics.lean`
- Create: `VisualProof/Rule/WirePrimitive/Content.lean`
- Create: `VisualProof/Rule/WirePrimitive/ContentFixtures.lean`
- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `applyCutWrap`, `applyCutAbsorb`.
- `applyParallelSplit`, `applyParallelFuse`.
- `applyEndsDelete`, `applyEndsSpawn`.
- Checked receipts exposing `.source`, `.target`, `.tag`, and `.sound`.
- Public theorems:
  `cut_wrap_sound`, `cut_absorb_sound`,
  `parallel_split_sound`, `parallel_fuse_sound`,
  `ends_delete_sound`, and `ends_spawn_sound`.

- [ ] **Step 1: Add RED checker fixtures.** Cover all-end transformation,
  empty endpoint sets, mixed site regions, exact single-atom cut absorption,
  pairwise co-located parallel matching, endpoint-free spawn, ordered
  argument signatures, site visibility, polarity matrix, and non-head
  refusal.
- [ ] **Step 2: Implement concrete receipts.** Mirror the merged
  `src/kernel/rules/wire-content.ts` result shape and freshness discipline.
  Every checker proves it selected all applied heads and no others.
- [ ] **Step 3: Instantiate the witness theorem.** Use:
  `W := True` for ends deletion; negation for cut wrap/absorb; conjunction
  and diagonal copying for parallel split/fuse. Construct relation-valued
  witnesses in full `Model`; reuse `PreModel.inhabited` only where choosing
  an unused value is sufficient.
- [ ] **Step 4: Prove exact inverse fixtures.** Wrap/absorb and split/fuse
  round trips must produce checked isomorphic normalized diagrams with
  transported ordered boundaries.
- [ ] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/Content.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/ContentSemantics.lean \
    VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Content.lean \
    VisualProof/Rule/WirePrimitive/ContentFixtures.lean
  git commit -m "feat: prove wire content primitive soundness"
  ```

---

### Task 7: Formalize argument-plumbing equivalences

**Files:**

- Create: `VisualProof/Diagram/Concrete/WirePrimitive/Arguments.lean`
- Create: `VisualProof/Diagram/Concrete/WirePrimitive/ArgumentsSemantics.lean`
- Create: `VisualProof/Rule/WirePrimitive/Arguments.lean`
- Create: `VisualProof/Rule/WirePrimitive/ArgumentsFixtures.lean`
- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `applyArityShift`, `applyArityUnshift`.
- `applyArgPermute`.
- `applyArgDuplicate`, `applyArgContract`.
- `applyArgDrop`, `applyArgExtend`.
- Corresponding `_sound` theorems and checked input/receipt types over full
  `Model`, obtained from the generic `PreModel` witness theorem.

- [ ] **Step 1: Add RED plumbing fixtures.** Cover nested signatures,
  per-site fresh arity-shift wires scoped at each endpoint region,
  arity-unshift exhaustion, invalid permutations, duplicate/contract
  adjacency, drop/extend positions, all-end attachment coverage, signature
  equality, and visibility.
- [ ] **Step 2: Implement structural equivalences.** Prove arity
  shift/unshift with existential/cylindrification witnesses in the full
  relation domains; use `PreModel.inhabited` for the reverse direction's
  required choice. Prove permutation and duplicate/contract by typed tuple
  rearrangement and full-model reification of the transformed relation.
- [ ] **Step 3: Implement merged drop/extend gates.** Detect one uniform
  attachment wire visible at the acted wire's scope. That case is an ungated
  equivalence. Otherwise enforce join-family polarity for drop and
  sever-family polarity for extend.
- [ ] **Step 4: Prove the gated witnesses.** Uniform attachment uses a single
  scope-visible parameter in both directions. Per-site drop has only the
  eliminating witness; per-site extend has only the introducing witness.
- [ ] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/Arguments.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/ArgumentsSemantics.lean \
    VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Arguments.lean \
    VisualProof/Rule/WirePrimitive/ArgumentsFixtures.lean
  git commit -m "feat: prove wire argument primitive soundness"
  ```

---

### Task 8: Formalize formal, identity, and folded-reference leaves

**Files:**

- Create: `VisualProof/Diagram/Concrete/WirePrimitive/Leaves.lean`
- Create: `VisualProof/Diagram/Concrete/WirePrimitive/LeavesSemantics.lean`
- Create: `VisualProof/Rule/WirePrimitive/Leaves.lean`
- Create: `VisualProof/Rule/WirePrimitive/LeavesFixtures.lean`
- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `applyApplyFormal`, `applyAbstractFormal`.
- `applyIdentityLeaf`, `applyIdentityAbstract`.
- `applyRefLeaf`, `applyRefAbstract`.
- Corresponding `_sound` theorems over full `Model`.

- [ ] **Step 1: Add RED leaf fixtures.** Cover formal-position signature
  equality, distinct per-site formal heads, identity equal signature/arity,
  one shared definition for ref abstraction, definition signature lookup,
  chosen scope enclosure, all endpoints, both orientations, and all refusal
  cases in the merged TypeScript checkers.
- [ ] **Step 2: Implement checked concrete leaves.** Match
  `src/kernel/rules/wire-args.ts`: join-family leaf rules consume every
  applied end; sever-family abstract rules consume the exact selected
  node set and create one fresh uniformly applied wire.
- [ ] **Step 3: Prove semantic witnesses.** Use full relation domains for
  application, equality at arbitrary `Sig`, and the predicate denoted by a
  stored definition. Ref proofs must call typed definition lookup and show
  equivalence to unfold/compile/fold without actually expanding the macro.
- [ ] **Step 4: Audit fullness.** Add theorem signatures/`#check` fixtures
  demonstrating that generic partition/merge remains `PreModel`-parametric
  while relation-synthesizing primitive instances quantify over `Model`.
- [ ] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/Leaves.lean \
    VisualProof/Diagram/Concrete/WirePrimitive/LeavesSemantics.lean \
    VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Leaves.lean \
    VisualProof/Rule/WirePrimitive/LeavesFixtures.lean
  git commit -m "feat: prove wire leaf primitive soundness"
  ```

---

### Task 9: Formalize the content compiler and monolithic redundancy

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Program.lean`
- Create: `VisualProof/Rule/WirePrimitive/Compiler.lean`
- Create: `VisualProof/Rule/WirePrimitive/CompilerTermination.lean`
- Create: `VisualProof/Rule/WirePrimitive/CompilerSoundness.lean`
- Create: `VisualProof/Rule/WirePrimitive/CompilerFixtures.lean`
- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `CompiledPrimitiveStep`: the checked primitive subset emitted by the
  structural compiler.
- `PrimitiveProgram`: ordered checked steps plus composed allocation and
  boundary-transport receipts.
- `runPrimitiveProgram`.
- `compileRelationJoin`, `compileRelationSever`.
- `runPrimitiveProgram_sound`.
- `compiled_join_redundant`, `compiled_sever_redundant`.

- [ ] **Step 1: Add RED compiler fixtures.** Port the TypeScript round-trip
  corpus, including empty content, one cut, parallel root items, shared
  root-scoped internal wires, repeated/dropped/permuted formals, uniform and
  per-site parameters, formal application, identities, folded refs, nullary
  content, and the worked `∃y.(P(x,y) ∧ ¬Q(y))` example.
- [ ] **Step 2: Define the residual and measure.** The residual stores the
  live wire, remaining open content, formal count, and ambient mapping.
  Lexicographically measure nodes + internal wires + regions, then remaining
  argument plumbing. Prove every case strictly decreases; do not use partial
  recursion or a fuel value callers can choose.
- [ ] **Step 3: Implement join compilation.** Case in this order:
  root-scoped internal wire → `arityShift`; multiple root items →
  `parallelSplit`; one cut → `cutWrap`; empty → `endsDelete` then
  `vacuousElim`; one leaf → plumbing then merge, `applyFormal`,
  `identityLeaf`, or `refLeaf`.
- [ ] **Step 4: Implement sever compilation.** Validate exact disjoint
  occurrences and shared formal/ambient structure, construct the virtual
  monolithic sever target, compile the corresponding join there, reverse the
  checked program and orientation, and transport ids back through the
  occurrence removal receipt.
- [ ] **Step 5: Prove program soundness.** Compose each primitive receipt's
  theorem and exact ordered boundary transport. The compiler is
  authoring-layer logic; primitive checkers remain unaware of residuals and
  monolithic inputs.
- [ ] **Step 6: Prove redundancy.** For join and sever, show the compiled
  program's final normalized diagram is checked-isomorphic to the
  monolithic result with exact boundary transport. Derive monolithic
  soundness again as a corollary and prove primitive-set completeness for
  every checked monolithic input.
- [ ] **Step 7: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Program.lean \
    VisualProof/Rule/WirePrimitive/Compiler.lean \
    VisualProof/Rule/WirePrimitive/CompilerTermination.lean \
    VisualProof/Rule/WirePrimitive/CompilerSoundness.lean \
    VisualProof/Rule/WirePrimitive/CompilerFixtures.lean
  git commit -m "feat: prove primitive compiler redundancy"
  ```

---

### Task 10: Prove insertion, ref, and per-site extension derivability

**Files:**

- Create: `VisualProof/Rule/WirePrimitive/Derived.lean`
- Create: `VisualProof/Rule/WirePrimitive/DerivedFixtures.lean`
- Modify: `VisualProof/Rule/WirePrimitive.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `insertion_primitive_program`.
- `insertion_redundant`.
- `ref_spawn_unfold_conservative`.
- `per_site_extend_program`.
- `per_site_extend_derived`.

- [ ] **Step 1: Add RED derivation fixtures.** Include arbitrary open content
  in a negative region, nullary content, a folded reference body, uniform
  extension, two-site differing extension attachments, and both replay
  orientations.
- [ ] **Step 2: Derive insertion.** Compose vacuous introduction of a
  `rel []` wire, negative-gated atom spawn, and compiled relation join
  grounding to the inserted content. Prove the result equals structural
  insertion modulo normalization and fresh naming.
- [ ] **Step 3: Derive ref conservativity.** Show ref spawn followed by unfold
  is the insertion program for its stored definition body. Definitions remain
  macros and acquire no spawn-anywhere semantic authority.
- [ ] **Step 4: Derive per-site extension.** Show a per-site `argExtend`
  equals uniform inert extension plus the local sever/join plumbing at the new
  position. The proof must preserve the merged kernel's direct checked
  per-site rule while demonstrating that the gesture layer need expose only
  uniform extension plus ordinary local joins.
- [ ] **Step 5: Pin the independent negative-splice theorem.** The insertion
  corollary may use it, but must not replace it; backward erasure soundness
  continues to cite the direct negative-splice proof.
- [ ] **Step 6: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean VisualProof/Rule/WirePrimitive.lean \
    VisualProof/Rule/WirePrimitive/Derived.lean \
    VisualProof/Rule/WirePrimitive/DerivedFixtures.lean
  git commit -m "feat: prove primitive derivability corollaries"
  ```

---

### Task 11: Complete definitions, citation, and the exact 34-step checker

**Files:**

- Create: `VisualProof/Rule/Definition.lean`
- Create: `VisualProof/Rule/Theorem.lean`
- Create: `VisualProof/Rule/Step.lean`
- Create: `VisualProof/Rule/Soundness.lean`
- Create: `VisualProof/Rule/StepFixtures.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `applyUnfold`, `applyFold`, `unfold_sound`, `fold_sound`.
- `applyTheorem`, `theorem_application_sound`.
- A 34-constructor dependent `ProofStep`.
- `applyStep`, `applyStep_sound`.
- Step receipts expose normalized result, allocation/provenance, total wire
  transport, root interface transport, and ordered boundary transport.

- [ ] **Step 1: Add one RED fixture per tag.** Each fixture constructs a
  checker-accepted payload, applies it in its legal orientation, and checks
  its `StepTag`. Add compile-failing exhaustiveness theorems so a missing or
  duplicate constructor cannot pass.
- [ ] **Step 2: Prove ref spawn and fold/unfold.** Use
  `Definitions.lookup_iff_body` and splice denotation. Fold/unfold are
  equivalences; ref spawn uses structural insertion gates.
- [ ] **Step 3: Prove theorem application.** A prior checked theorem can be
  cited at an exact pinned occurrence, LHS→RHS in positive context and
  RHS→LHS in negative context, flipped by replay orientation. Preserve
  ordered aliased boundaries.
- [ ] **Step 4: Define the exact checked sum.** Each constructor contains the
  owning module's checked receipt or enough raw input for `applyStep` to
  construct that receipt. There is no relation-content constructor and no
  identity-retarget field.
- [ ] **Step 5: Define receipts and transport.** Match the merged TypeScript
  distinction among provenance, every-scope transport, and root interface
  transport. Normalization transport composes after the primitive result;
  repeated ordered boundary aliases remain repeated.
- [ ] **Step 6: Prove `applyStep_sound`.** Use exactly 34 exhaustive cases,
  delegating each case to its owning theorem. No default case and no premise
  that already assumes the desired directed entailment.
- [ ] **Step 7: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean VisualProof/Rule/Definition.lean \
    VisualProof/Rule/Theorem.lean VisualProof/Rule/Step.lean \
    VisualProof/Rule/Soundness.lean VisualProof/Rule/StepFixtures.lean
  git commit -m "feat: prove all 34 Lean proof steps sound"
  ```

---

### Task 12: Complete replay, theorem, and ordered-theory soundness

**Files:**

- Create: `VisualProof/Proof/Replay.lean`
- Create: `VisualProof/Proof/Theorem.lean`
- Create: `VisualProof/Proof/Theory.lean`
- Create: `VisualProof/Proof/Fixtures.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- `Proof`, `replay`, `replay_sound`, `backward_replay_sound`.
- `Theorem`, `checkTheorem`, `checkedTheorem_sound`.
- `Theory`, `verifyTheory`, `verifiedTheory_sound`.

- [ ] **Step 1: Add RED end-to-end fixtures.** Cover a multi-step primitive
  compiler program, a two-sided theorem whose halves meet only up to checked
  isomorphism, repeated boundary aliases transported through normalization,
  citation in both polarities, and a later theorem citing only an earlier
  theorem.
- [ ] **Step 2: Prove replay.** Compose `applyStep_sound` along the list while
  composing allocation reservations and total transports. Forward replay
  starts at LHS; backward replay starts at RHS with each gate flipped.
- [ ] **Step 3: Prove two-sided theorem checking.** Independently replay both
  sides, transport the registered ordered boundaries after every step, and
  require the meeting diagrams to be checked-isomorphic. Prove entailment
  between the exact registered endpoints, not substituted meeting objects.
- [ ] **Step 4: Prove ordered theory verification.** Interpret the complete
  ordered definition prefix first. Verify theorems chronologically so a
  theorem payload can cite only its already-verified prefix. Prove every
  accepted theorem valid in every full `Model`.
- [ ] **Step 5: Run GREEN and commit.**

  ```bash
  lake build
  npm run formal:size
  git add -- VisualProof.lean VisualProof/Proof/Replay.lean \
    VisualProof/Proof/Theorem.lean VisualProof/Proof/Theory.lean \
    VisualProof/Proof/Fixtures.lean
  git commit -m "feat: prove Lean replay and theory soundness"
  ```

---

### Task 13: Restore truthful correspondence and proof-authority tooling

**Files:**

- Create: `VisualProof/Correspondence/StepTags.lean`
- Create: `VisualProof/Correspondence/StepTagsMain.lean`
- Create: `VisualProof/Audit.lean`
- Create: `scripts/check-lean-step-tags.mjs`
- Create: `scripts/check-formalization.mjs`
- Modify: `lakefile.toml`
- Modify: `package.json`
- Modify: `tests/architecture/lean-semantics.test.ts`
- Modify: `VisualProof.lean`

**Interfaces:**

- Executable `visualproof_step_tags`.
- `npm run formal:tags`.
- `npm run formal:check`.

- [ ] **Step 1: Add RED tooling assertions.** Require both package scripts,
  both scripts, exactly one Lean tag executable, exact 34-line output, and no
  displaced fixture-matching executable.
- [ ] **Step 2: Serialize the Lean authority.** Define
  `StepTag.serializedName`, prove injectivity, and print `StepTag.all`; do not
  hand-maintain another Lean tag list.
- [ ] **Step 3: Compare TypeScript mechanically.** Parse only the
  `rule: '…'` discriminants of the exported TypeScript `ProofStep` union, run
  `lake env visualproof_step_tags`, reject duplicates, require exact ordered
  equality and count 34, and report the first order mismatch plus missing and
  extra tags.
- [ ] **Step 4: Add authority audits.** `VisualProof/Audit.lean` imports and
  prints axioms for normalization, derived identity substitution, generic
  partition/merge, all primitive families, relation sever/join redundancy,
  insertion redundancy, `applyStep_sound`, replay, checked theorem, and
  verified theory soundness.
- [ ] **Step 5: Add source-structure audits.**
  `scripts/check-formalization.mjs` must reject repository-owned Lean source
  containing `sorry`, `admit`, project axioms, Lambda-era declarations,
  `IdentityRetarget`, iota-only primitive owners, or Phase 4 reference
  semantics. It must also prove:

  - monolithic relation APIs occur only in the specification/compiler layer;
  - no TypeScript `ProofStep` contains a monolithic or retarget payload;
  - the public primitive content/argument checkers require all applied heads,
    except generic merge;
  - the documented full-`Model` boundary matches theorem signatures.

- [ ] **Step 6: Restore supported commands.**

  ```json
  "formal:tags": "node scripts/check-lean-step-tags.mjs",
  "formal:check": "node scripts/check-formalization.mjs"
  ```

  `formal:check` runs `formal:size`, `lake build`, `formal:tags`, TypeScript
  typecheck, and the Lean architecture test. Add only
  `visualproof_step_tags` to `lakefile.toml`.
- [ ] **Step 7: Run GREEN and commit.**

  ```bash
  npm run formal:tags
  npm run formal:check
  npx vitest run tests/architecture/lean-semantics.test.ts
  git diff --check
  git add -- VisualProof.lean VisualProof/Audit.lean \
    VisualProof/Correspondence/StepTags.lean \
    VisualProof/Correspondence/StepTagsMain.lean \
    scripts/check-lean-step-tags.mjs \
    scripts/check-formalization.mjs lakefile.toml package.json \
    tests/architecture/lean-semantics.test.ts
  git commit -m "build: enforce Lean parity for 34 proof steps"
  ```

---

### Task 14: Clean-build audit and close Phase 3

**Files:**

- Modify only the exact owner of a failure exposed by the gates.
- Update completion checkboxes in this plan as tasks land.
- Append conformance to the implementation session's foundation record.

- [ ] **Step 1: Prove displaced authorities are absent.**

  ```bash
  test ! -d VisualProof/Lambda
  test ! -e VisualProof/Rule/IdentityRetargetSemantics.lean
  test ! -e VisualProof/Diagram/Concrete/WireQuantifierIota.lean
  ! rg -n \
    "LambdaModel|IdentityRetarget|iota_sever_sound|iota_join_sound|openTermSpawn|congruenceJoin|headStrip|inconsistentCut|comprehensionInstantiate|comprehensionAbstract" \
    VisualProof VisualProof.lean
  ```

- [ ] **Step 2: Prove monolithic containment and Phase 4 absence.**

  ```bash
  test ! -e VisualProof/HOL
  ! rg -n "denotation-preservation|translateHOL|ReferenceHOL|Henkin" \
    VisualProof
  ```

  Run the formal source audit for monolithic containment rather than relying
  on a raw zero-match grep, because the compiler/redundancy modules
  intentionally retain the specification rule.
- [ ] **Step 3: Run a clean formal build.**

  ```bash
  lake clean
  lake build
  npm run formal:check
  ```

- [ ] **Step 4: Run complete repository gates.**

  ```bash
  npm test
  npm run typecheck
  npm run formal:size
  npm run e2e
  git diff --check
  git status --short
  ```

  Only unrelated pre-existing untracked `archive/` and `scratchpad/` paths
  may remain.
- [ ] **Step 5: Record conformance.** Append the completed owners, deleted
  structures, all 34 tags, full-model boundary, compiler redundancy theorems,
  clean build, unit/type/E2E results, and Phase 4 absence to the implementation
  foundation record without rewriting its pre-action sections.
- [ ] **Step 6: Commit any gate-owned correction.** Stage only task-owned
  files. If no correction exists, do not make an empty commit.

## Acceptance matrix

| Requirement | Direct evidence |
|---|---|
| Exact merged proof language | `StepTag.all_length = 34`, exhaustive `ProofStep`, `npm run formal:tags` |
| No identity-retarget authority | deleted module/declarations plus derived-substitution fixtures |
| Generic signature-indexed partition/merge | `.iota`, `rel`, nested-rel fixtures and `wire_*_sound` |
| Backward erasure follows flipped polarity | Task 1 matrix and independent negative-splice theorem |
| Complete strongest-form specification | `relation_sever_sound`, existing `relation_join_sound` |
| Uniform all-site primitive semantics | `UniformSiteRewrite` exhaustion + witness theorem |
| Original nine pairs plus folded-ref pair sound | Tasks 3 and 6–8 theorem families |
| Vacuous family retained | 34-step fixtures and compiler empty-content case |
| Fullness boundary truthful | theorem signatures plus Task 8/13 audits |
| Compiler terminates structurally | well-founded residual measure |
| Monolithic rule redundant | `compiled_join_redundant`, `compiled_sever_redundant` |
| Insertion/ref remain conservative | `insertion_redundant`, `ref_spawn_unfold_conservative` |
| Per-site extend is derived | `per_site_extend_derived` |
| Definitions/citation sound | fold/unfold and theorem-application theorems |
| All 34 steps sound | exhaustive `applyStep_sound` |
| Forward/backward replay sound | `replay_sound`, `backward_replay_sound` |
| Exact theorem endpoints | `checkedTheorem_sound` with ordered boundary transport |
| Ordered theory sound | `verifiedTheory_sound` |
| No displaced/Phase 4 model | Task 13 source audit and Task 14 clean-build gates |
