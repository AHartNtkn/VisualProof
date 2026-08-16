# Declarative Vacuous Assembly Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** State the original whole-assembly vacuity relation declaratively and state its inclusion in the transitive closure of the full Lean rule system.

**Architecture:** A compact recursive `IdentityOnlyExtension` witness identifies exactly the retained syntax and added identity apparatus. Dependent projections from that single witness define added wires, added identities, incidences, existing contacts, connectedness, and the historical two-case absorption relation; no executable edit, computed endpoint, inverse, graph copy, or primitive-step witness enters the relation. The closure theorem lives in a separate module so the relation remains independent of `Step`.

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
