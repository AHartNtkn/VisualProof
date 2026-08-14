# Higher-Order Rule Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the recursive higher-order calculus by enforcing the two-incidence wire invariant, migrating the remaining structural rules and comprehension, and adding the three full identity-rule families with direct executable directions and semantic soundness.

**Architecture:** `Region`, `Item`, and `ItemSeq` remain the sole syntax. `Item.atom` is the higher-order application node: its head is a relation-signature wire and its ordered ports are its typed arguments. Wire scope remains the DCA of actual incidences; validity additionally requires every wire to have at least two incidences. Every runner constructs its target directly from an exact source-indexed operation description, with no search, normalization, rehoming, target witness, or second diagram representation.

**Tech Stack:** Lean 4.30.0, Lake, recursive indexed inductives, theorem-driven RED/GREEN.

## Global Constraints

- Preserve the recursive `Region` / `Item` / `ItemSeq` representation and `Item.atom` application constructor.
- A locally introduced wire has at least two item-port incidences and DCA equal to its owner region.
- An external wire has at least two combined boundary and body incidences.
- Unary identity nodes are explicit pins. Erasure and deiteration retain their accepted residue semantics; they may create pins directly but never run a normalization pass.
- Add three distinct `Rule.Step` families: vacuity, presentation invariance, and identification. Each is ungated and bidirectional.
- Comprehension selects one local `.rel arguments` wire and replaces its `Item.atom` head occurrences by one typed open pattern.
- Runners are ordinary computable functions. Their indices identify exact source-side instances and never contain a target diagram or rule witness.
- Proofs may be noncomputable. No `sorry` remains at a completed checkpoint.
- Do not add target search, occurrence discovery, global wire tables, stored scope, compatibility APIs, `HEq` reconciliation, or raised heartbeat/recursion limits.
- If an identity operation requires a global normalization/rehoming pass or another diagram authority, stop that task and report the semantic boundary.

---

### Task 1: Enforce the two-incidence validity invariant

**Files:**
- Modify: `VisualProof/Diagram/Scope.lean`
- Modify: `VisualProof/Diagram/Boundary.lean`
- Modify: `VisualProof/Diagram/Scope/Context.lean`
- Modify: `VisualProof/Diagram/UnaryIdentity.lean`
- Modify: `VisualProof/Diagram/Occurrence.lean`
- Modify: `VisualProof/Diagram/NestedOccurrence.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify: `VisualProof/Rule/Relation.lean`
- Modify: `VisualProof/Rule/Erasure.lean`
- Modify: `VisualProof/Rule/Iteration.lean`
- Modify: their executable and soundness consumers as required by the selected constructors.

**Interfaces:**
- Produces one strengthened `Region.Canonical` and one external-wire validity field on `OpenDiagram`.
- Produces direct completion-pin constructors and context-lifting theorems used by every later rule.

- [ ] Strengthen the local clause of `Region.Canonical`: for every local wire, its actual `incidencePaths` have length at least two and DCA `[]`. Add a derived nonempty projection so DCA proofs do not duplicate arithmetic.
- [ ] Add `OpenDiagram.externalTwoEnded`, requiring `2 ≤ boundaryWire.countIndex wire.val + (body.incidencePaths wire.val).length` for every external wire. Update `withBody` to require the target body’s external proof explicitly.
- [ ] Generalize the existing context replacement lemma from nonempty/DCA preservation to the strengthened local condition. It must combine unchanged outside paths with the replacement hole’s count and DCA facts; it must not traverse the whole host separately.
- [ ] Refactor `ItemSeq.pinWires` only as necessary to emit two distinct unary pins for a selected wire with zero existing incidences, one pin for a singleton or non-rooted incidence set, and none for an already valid rooted set.
- [ ] Reprove erasure and iteration/deiteration target validity. Preserve their accepted explicit residue behavior; do not introduce a post-operation repair pass.
- [ ] Update every direct `OpenDiagram`/`withBody` constructor in the active typed closure to provide external validity and prove isomorphisms preserve the property needed by their own endpoints.
- [ ] Strict-check every changed module, build Erasure and Iteration executable/soundness targets, scan for `sorry`, `HEq`, stored scope, and raised limits, then commit.

**Architecture gate:** no validity theorem may define scope from ownership, count a binder declaration as a port incidence, or repair an already-constructed target globally.

### Task 2: Migrate typed port partitions and wire severance

**Files:**
- Modify: `VisualProof/Diagram/PortPartition.lean`
- Modify: `VisualProof/Rule/WireSever.lean`
- Modify: `VisualProof/Rule/Executable/WireSever.lean`
- Modify: `VisualProof/Rule/Soundness/WireSever.lean`

**Interfaces:**
- `Region.Port`, `Item.Port`, and `ItemSeq.Port` are indexed by typed `Var` values.
- Atom ports include both the relation head and every argument application port.
- A partition maps each exact source port to a typed target wire in the fiber of one `WireRenaming` collapse.

- [ ] Replace all Nat/`RelCtx` port types with `List Sig`, `Var`, and `WireRenaming`; remove the bubble branch and add the atom-head port.
- [ ] Port `partitionOutput`, rename-collapse, and existence theorems with the same mutual structural recursion.
- [ ] Express local sever/join and open-boundary sever/join over typed wires. Each constructed endpoint must establish canonical DCA and two-incidence validity directly, using explicit pins when the rule’s chosen scope requires them.
- [ ] Port both source-indexed runner directions, exact iff coverage, target-isomorphism closure, and semantic soundness.
- [ ] Strict-check and focused-build the four modules, then commit.

**Architecture gate:** a port partition is local operation data, not a global wire representation. No search or target diagram may enter its API.

### Task 3: Migrate double cut

**Files:**
- Modify: `VisualProof/Rule/DoubleCut.lean`
- Modify: `VisualProof/Rule/Executable/DoubleCut.lean`
- Modify: `VisualProof/Rule/Soundness/DoubleCut.lean`

**Interfaces:**
- Produces direct double-cut introduction/elimination over a selected `Region wires`.
- Pass-through inherited wires receive explicit identity pins at the old selected region exactly when moving all of their incidences would change their DCA or violate the two-incidence floor.

- [ ] Define the typed double-cut wrapper and its pass-through pin block. Prove wrapper canonicality and inherited incidence/DCA preservation from the source body.
- [ ] Define the contextual symmetric relation, isomorphism closure, and direct forward/backward indices and runners.
- [ ] Prove exact coverage in both directions.
- [ ] Prove soundness using unary-identity truth and classical double negation, retaining the recursive/contextual proof shape.
- [ ] Strict-check, focused-build, scan, and commit.

**Architecture gate:** double-cut pin deposition is part of the local constructor. A later scope-normalization traversal is forbidden.

### Task 4: Add the three identity-rule families

**Files:**
- Replace: `VisualProof/Rule/Vacuity.lean`
- Create: `VisualProof/Rule/Presentation.lean`
- Create: `VisualProof/Rule/Identification.lean`
- Replace: `VisualProof/Rule/Executable/Vacuity.lean`
- Create: `VisualProof/Rule/Executable/Presentation.lean`
- Create: `VisualProof/Rule/Executable/Identification.lean`
- Replace: `VisualProof/Rule/Soundness/Vacuity.lean`
- Create: `VisualProof/Rule/Soundness/Presentation.lean`
- Create: `VisualProof/Rule/Soundness/Identification.lean`
- Modify: `VisualProof/Rule/Step.lean`

**Interfaces:**
- Vacuity describes computable identity/fresh-wire assemblies whose connected components touch at most one surviving wire, whose fresh wires are bare or absorbable at the equality home, and which preserve every touched wire’s DCA and two-end floor.
- Presentation replaces one-region, one-signature identity configurations that generate the same finite equivalence relation on the same wires, preserving at least one regional port per member and two incidences per wire.
- Identification collapses or exposes one or more wires at an equality node, retaining that node, with absorbed wire DCA exactly the node region and a nonempty set of non-identity incidences transferred for every absorbed wire. A wire whose only incidences are duplicate ports on that identity node belongs to vacuity instead; redundant same-wire ports whose removal leaves the wire valid belong to presentation invariance.

- [ ] Define the weakest recursive operation data that computes each endpoint. Use structural item/region focuses and typed port partitions; do not store an endpoint `Region` or rule proof in an index.
- [ ] Keep the three families disjoint by effect at the duplicate-port boundary: presentation contracts redundant ports while retaining the wire; vacuity removes a two-port-only identity loop; identification requires actual away incidences to transfer and never handles the zero-transfer case.
- [ ] Define each local/global relation from the same operation data consumed by its runner so exact coverage is structural rather than reconstructed by search.
- [ ] Implement two direct runner directions for each family and prove exact iff coverage plus both target-isomorphism closure laws.
- [ ] Prove semantic equivalence: inhabitedness for vacuity, equality-relation invariance for presentation, and the one-point principle for identification.
- [ ] Add distinct `Step.vacuity`, `Step.presentation`, and `Step.identification` constructors and update `Step.iso`.
- [ ] Strict-check each family independently, scan for target/search/normalization/raised limits, and commit each independently.

**Architecture gate:** if the strongest vacuity assembly cannot be computed from one recursive operation description without a second diagram/navigation authority, stop before weakening the rule or introducing a compatibility representation.

### Task 5: Replace comprehension with typed relation-wire instantiation

**Files:**
- Replace: `VisualProof/Rule/Comprehension/Relation.lean`
- Replace: `VisualProof/Rule/Soundness/Comprehension.lean`

**Interfaces:**
- Selects one local context position with signature `.rel arguments`.
- Replaces every application atom headed by that wire with a supplied `OpenDiagram arguments`, attached to the atom’s typed argument tuple, and removes the selected local wire.

- [ ] Define the local-context split and typed removal renaming for the selected relation wire.
- [ ] Port the mutual `RegionResult`/`ItemsResult`/`ItemResult` instantiation evidence. Atom-head selection is explicit; identities may not mention the selected wire; cuts recurse; other atoms rename structurally.
- [ ] Prove output canonicality and two-incidence validity from the evidence, then define the contextual comprehension relation.
- [ ] Port semantic soundness by the same mutual induction, interpreting the selected relation wire as the open pattern denotation.
- [ ] Strict-check, focused-build, scan for relation-binder syntax and raised limits, then commit.

**Architecture gate:** comprehension operates on `Item.atom`; do not add a substitution compiler or a second application syntax.

### Task 6: Integrate and validate the complete rule calculus

**Files:**
- Modify: `VisualProof/Rule/Executable.lean`
- Modify: `VisualProof/Rule/Soundness.lean`
- Modify: `VisualProof/ComputabilityAudit.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `VisualProof.lean`
- Remove stale unreachable relation/bubble and replacement/isomorphism authorities established by import analysis.

- [ ] Update aggregate imports and dispatch for all current `Step` constructors and three identity families.
- [ ] Compile every runner with Lean’s code generator; correct any validation declaration shape instead of weakening the audit.
- [ ] Remove obsolete relation-context, bubble, and unreachable replacement/context-path authorities rather than preserving adapters or aliases.
- [ ] Run strict owner checks, `lake build`, all authority audits, admission/displaced-model/raised-limit scans, and `git diff --check`.
- [ ] Review the final complexity ledger: one recursive syntax, one DCA scope, one validity authority, direct runners, and no search/normalization/parallel authority. Commit the integrated closure.
