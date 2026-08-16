# Declarative Vacuous Assembly Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define the original whole-assembly vacuity relation declaratively and prove its inclusion in the transitive closure of the full Lean rule system.

**Architecture:** A compact recursive `IdentityOnlyExtension` witness identifies exactly the retained syntax and added identity apparatus. Dependent projections from that single witness define added wires, added identities, incidences, existing contacts, connectedness, and the historical two-case absorption relation; no executable edit, computed endpoint, inverse, graph copy, or primitive-step witness enters the relation. The closure theorem lives in a separate module so the relation remains independent of `Step`.

The proof reads the complete absorption run backwards. It does not materialize
individual carrier states as diagrams: doing so would duplicate recursive syntax
and validity. Reusable proof support is owned separately at its natural boundary:
finite rule-chain transport, exact recursive item focus, finite folds over existing
extension evidence, and realization of an equality visible at a descendant region.
Only assembly-component normalization remains in the completeness module.

**Tech Stack:** Lean 4.30, the existing recursive `Region`/`Item`/`ItemSeq` syntax, `Contextual`, and `Relation.TransGen`.

## Global Constraints

- Preserve the historical class exactly: empty assemblies and reducible cyclic assemblies remain admitted.
- Contacts are the historical syntactic anchors: an existing wire or an existing identity node, not an inferred global equality class.
- The absorption run is existential proof data; no computable checker or runner is required.
- Every definition in the completeness theorem dependency closure must be complete before RED.
- The sole permitted `sorry` is the owning completeness theorem proof.

---

### Task 1: Declarative whole-assembly relation

**Files:**
- Create: `VisualProof/Rule/Vacuity/Assembly.lean`
- Create: `VisualProof/Rule/Vacuity/AssemblyCompleteness.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `VisualProof.Rule.Relation`, recursive diagram syntax and scope ownership, `VisualProof.Rule.Step` only in the completeness module.
- Produces: `IdentityOnlyExtension`, `VacuousExtension`, `WholeAssemblyVacuity`, and `WholeAssemblyVacuity.complete`.

- [ ] **Step 1: Add the recursive identity-only extension relation**

Define a typed order-preserving wire extension and mutual region/item-sequence relations. Atoms and cuts are retained; retained identity ports survive and may gain fresh-wire ports; only identity items may be newly introduced.

- [ ] **Step 2: Add proof-derived assembly occurrences**

Define dependent occurrences of fresh wires, added identity nodes, their actual incidences, and retained contacts by recursion over the extension witness. Each occurrence resolves into the existing target syntax; do not copy node, wire, scope, or port tables.

- [ ] **Step 3: State the historical acceptance condition**

Define connectedness from actual added-wire/added-identity incidence, require at most one retained contact per connected component, and define the two absorption cases over live fresh wires. Define absorbability as existence of a finite absorption chain ending with no live fresh wire.

- [ ] **Step 4: Lift the local relation through recursive contexts**

Define `VacuousExtension`, its symmetric local form, and `WholeAssemblyVacuity := Contextual ...`. Endpoint well-formedness remains owned by `OpenDiagram` and `Contextual`.

- [ ] **Step 5: Establish theorem-driven RED**

In `AssemblyCompleteness.lean`, state:

```lean
theorem WholeAssemblyVacuity.complete
    (step : WholeAssemblyVacuity source target) :
    Relation.TransGen Step source target := by
  sorry
```

Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Vacuity/Assembly.lean
lake env lean VisualProof/Rule/Vacuity/AssemblyCompleteness.lean
```

Expected: the relation module has no diagnostics; the completeness module reports only the owning theorem's `sorry` when checked with warning-as-error.

- [ ] **Step 6: Integrate and validate**

Import the completeness module from `VisualProof.lean`. Run the focused build, admission scan, authority audit, and diff check:

```bash
lake build VisualProof.Rule.Vacuity.AssemblyCompleteness
rg -n 'sorry|admit|axiom' VisualProof/Rule/Vacuity/Assembly.lean VisualProof/Rule/Vacuity/AssemblyCompleteness.lean
scripts/audit-lean-authority.sh rules
git diff --check
```

Expected: focused build succeeds; the scan finds exactly the owning completeness theorem's `sorry`; the rules audit and diff check pass.

- [ ] **Step 7: Commit the validated theorem boundary**

```bash
git add VisualProof/Rule/Vacuity/Assembly.lean VisualProof/Rule/Vacuity/AssemblyCompleteness.lean VisualProof.lean docs/superpowers/plans/2026-08-16-declarative-vacuous-assembly.md
git commit -m "State declarative vacuous assembly completeness"
```

---

### Task 2: Prove completeness

**Files:**
- Create or modify narrow diagram/rule theorem-owner modules as required for
  recursive identity focus, closure transport, and visible equality realization.
- Modify: `VisualProof/Rule/Vacuity/AssemblyCompleteness.lean`

- [ ] **Step 1: Add isomorphism-aware finite `Step` closure lemmas**

Prove concatenation and endpoint-isomorphism transport for
`Relation.TransGen Step`, derived only from `Step.iso`.

- [ ] **Step 2: Add exact recursive identity focus**

Turn an existing `Region.IdentityOccurrence` into its owning region context and
local item split, with the isomorphisms required to present the selected identity
to `Stub`, `Presentation`, and zero-fresh `Iteration`. Do not introduce item IDs,
paths stored independently of syntax, or a second navigation representation.

- [ ] **Step 3: Add finite folds over extension evidence**

Derive complete finite enumerations of fresh wires, added identities, and actual
fresh incidences from `IdentityOnlyExtension`. These lists enumerate existing
dependent cursors and never become assembly data or executable search state.

- [ ] **Step 4: Realize visible equality regionally**

Prove once that an equality available at an ancestor can be exposed at a
descendant by a finite `Step` chain using `Iteration` and `Presentation`, with a
cleanup chain. Reuse exact focus and context transport.

- [ ] **Step 5: Normalize one accepted component**

Read the accepted absorption trace backwards. Construct bare roots with
`Point`/`Stub`, contacted roots with `Stub`, reflexive incidences with `Pin`, and
same-region physical configurations with `Presentation`; use the regional
equality lemma for transferred descendant incidences.

- [ ] **Step 6: Prove the local and contextual completeness theorems**

Handle the zero-fresh base (including nullary nodes and retained-wire identity
configurations), concatenate component chains, lift through the original
`Occurrence`, and close the exact public theorem without changing its statement.

- [ ] **Step 7: Validate and commit**

Run strict checks for every touched owner, the focused completeness build,
admission and authority scans, `git diff --check`, and the aggregate build. Commit
the complete proof once all task-owned validation is green.
