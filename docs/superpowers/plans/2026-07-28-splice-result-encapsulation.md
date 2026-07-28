# Splice Result Encapsulation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `splice` the only constructor of a concrete splice result and expose only its eagerly normalized checked target and total signature-preserving source-wire transport.

**Architecture:** `splice` validates the generated candidate, normalizes that checked candidate immediately, and invokes a private `ConcreteSpliceResult` constructor. Proofs that inspect generated candidate structure must accept a successful `splice attachment = .ok result` equation and derive raw well-formedness from that receipt; normalized boundary and denotation endpoints remain public.

**Tech Stack:** Lean 4, Lake, project `VisualProof` modules, compile-time API probes.

## Global Constraints

- Do not edit `Rule.Identity` or retarget files.
- Do not leave a public constructor, raw result field/accessor, or ungated compiler-completeness path.
- Preserve `ConcreteSpliceResult.checked`, `wireImage`, `wireImage_signature`, `boundaryTarget`, `boundaryTarget_signature`, and `boundaryTarget_eq_of_alias` as normalized interfaces.
- Preserve public `denote_splice` and `exact_occurrence_denotation`, gated by explicit successful splice receipts.
- Add no `sorry`, new axiom, or `unsafe` declaration.
- Keep every modified Lean source file within the repository size limit.

---

### Task 1: Establish Encapsulation Probes

**Files:**
- Create: `/tmp/vpa-splice-result-api-before.lean`
- Test: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`

**Interfaces:**
- Consumes: current public `ConcreteSpliceResult.mk` and `ConcreteSpliceResult.wellFormed`.
- Produces: red evidence that both forbidden declarations are currently externally visible.

- [x] **Step 1: Write the pre-change API probe**

```lean
import VisualProof.Diagram.Concrete.Subgraph.Splice

#check VisualProof.ConcreteSpliceResult.mk
#check VisualProof.ConcreteSpliceResult.wellFormed
```

- [x] **Step 2: Run the probe and record the exposed declarations**

Run: `lake env lean /tmp/vpa-splice-result-api-before.lean`

Expected: PASS, demonstrating that the constructor and raw projection are currently public.

### Task 2: Rebuild the Result and Acceptance Pipeline

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean:866-1000`
- Test: `/tmp/vpa-splice-result-api-after.lean`

**Interfaces:**
- Consumes: `ConcreteDiagram.checkWellFormed`, `ConcreteDiagram.checkWellFormed_preserves_input`, and `ConcreteDiagram.normalizeIdentities`.
- Produces: opaque `ConcreteSpliceResult` fields `checked`, `wireImage`, and `wireImage_signature`; `splice`; receipt-gated raw well-formedness recovery for internal proof modules.

- [x] **Step 1: Replace the raw-proof wrapper with the normalized representation**

```lean
structure ConcreteSpliceResult (attachment : ConcreteSpliceAttachment site fragment) where
  private mk ::
  checked : CheckedDiagram definitions
  wireImage : attachment.diagram.WireId → checked.val.WireId
  wireImage_signature :
    ∀ wire, (checked.val.wires (wireImage wire)).sig =
      (attachment.diagram.wires wire).sig
```

- [x] **Step 2: Make `splice` check and normalize before private construction**

```lean
match accepted : ConcreteDiagram.checkWellFormed definitions attachment.diagram with
| .error error => exact .error error
| .ok checked =>
    have same := ConcreteDiagram.checkWellFormed_preserves_input accepted
    let generated : CheckedDiagram definitions := ⟨attachment.diagram, by simpa [same] using checked.property⟩
    let normalized := ConcreteDiagram.normalizeIdentities generated
    exact .ok ⟨normalized.target, normalized.wireImage, normalized.wire_signature⟩
```

- [x] **Step 3: Re-express boundary transport using only stored normalized fields**

Keep `boundaryTarget`, `boundaryTarget_signature`, and `boundaryTarget_eq_of_alias`; delete the deferred `generatedChecked` and `normalization` accessors.

- [x] **Step 4: Build the splice module**

Run: `lake env lean VisualProof/Diagram/Concrete/Subgraph/Splice.lean`

Expected: PASS.

- [x] **Step 5: Write and run the negative API probe**

```lean
import VisualProof.Diagram.Concrete.Subgraph.Splice

#check VisualProof.ConcreteSpliceResult.mk
#check VisualProof.ConcreteSpliceResult.wellFormed
```

Run: `lake env lean /tmp/vpa-splice-result-api-after.lean`

Expected: FAIL with unknown/private declaration diagnostics for both forbidden API paths.

### Task 3: Gate Raw Factorization and Denotation Proofs

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Factorization.lean:2122-2748`
- Modify: `VisualProof/Diagram/Concrete/Subgraph/FactorizationNaturality.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph/FactorizationSemantics.lean`

**Interfaces:**
- Consumes: `(accepted : splice attachment = .ok result)`.
- Produces: private candidate/factor compilers, a `SpliceCompilation` with private constructor and compiler receipt, public receipt-gated `spliceCompilation_complete`, all naturality helpers that use candidate well-formedness, `denote_splice`, and `exact_occurrence_denotation`.

- [x] **Step 1: Add the splice-success receipt to each raw proof consumer**

Use the exact binder:

```lean
(spliceAccepted : splice attachment = .ok result)
```

Replace every `result.wellFormed` use with well-formedness derived from `spliceAccepted`.

- [x] **Step 2: Privatize raw compilers and gate compilation witness construction**

```lean
structure SpliceCompilation (attachment : ConcreteSpliceAttachment removed fragment) where
  private mk ::
  factor : SpliceFactor attachment
  private factor_compiles :
    compileSpliceFactor? attachment = some factor

theorem spliceCompilation_complete
    (result : ConcreteSpliceResult attachment)
    (spliceAccepted : splice attachment = .ok result) :
    Nonempty (SpliceCompilation attachment) := by
  obtain ⟨factor, factorCompiled⟩ :=
    compileSpliceFactor?_complete result spliceAccepted
  exact ⟨SpliceCompilation.mk factor factorCompiled⟩
```

Change the existing declaration modifiers to `private def
compileCandidateFrame?`, `private theorem compileCandidateFrame?_sound`,
`private def compileCandidateAttachmentPositions?`, `private def
compileSpliceFactor?`, and `private theorem compileSpliceFactor?_complete`.
Add `spliceAccepted` to compiler completeness, bind
`wellFormed := splice_success_wellFormed spliceAccepted`, and replace every
former `result.wellFormed` argument in its existing proof with `wellFormed`.

- [x] **Step 3: Thread the receipt through naturality call chains**

Every theorem with a `ConcreteSpliceResult` argument that invokes well-formedness-sensitive compilation receives `spliceAccepted` and passes it to downstream helpers; purely normalized result consumers remain unchanged.

- [x] **Step 4: Gate normalized public denotation endpoints**

```lean
(result : ConcreteSpliceResult attachment)
(spliceAccepted : splice attachment = .ok result)
```

Insert these adjacent binders in both `denote_splice` and
`exact_occurrence_denotation`, then use `splice_success_checked` to rewrite
`result.checked` to the normalized checked candidate before applying identity
normalization soundness.

The conclusions continue to mention `result.checked`, normalized denotation, and proof-only factorization witnesses; no raw checked candidate appears in either public conclusion.

- [x] **Step 5: Build each proof layer in dependency order**

Run:

```bash
lake env lean VisualProof/Diagram/Concrete/Subgraph/Factorization.lean
lake env lean VisualProof/Diagram/Concrete/Subgraph/FactorizationNaturality.lean
lake env lean VisualProof/Diagram/Concrete/Subgraph/FactorizationSemantics.lean
```

Expected: every command passes.

### Task 4: Migrate Examples and Validate the Public Boundary

**Files:**
- Modify: `VisualProof/Diagram/Concrete/Subgraph/SpliceExamples.lean:286-304`
- Test: `VisualProof.lean`

**Interfaces:**
- Consumes: `splice attachment`.
- Produces: example result and receipt obtained only by matching successful `splice`; complete public build and negative API evidence.

- [x] **Step 1: Replace direct example construction with a successful splice witness**

```lean
theorem splice_succeeds : ∃ result, splice attachment = .ok result := by
  native_decide

noncomputable def spliced : ConcreteSpliceResult attachment :=
  Classical.choose splice_succeeds

theorem spliced_accepted : splice attachment = .ok spliced :=
  Classical.choose_spec splice_succeeds
```

- [x] **Step 2: Build the example and public import**

Run:

```bash
lake env lean VisualProof/Diagram/Concrete/Subgraph/SpliceExamples.lean
lake env lean VisualProof.lean
```

Expected: both commands pass.

- [x] **Step 3: Scan for displaced API paths and proof escapes**

Run:

```bash
rg -n 'result\.wellFormed|ConcreteSpliceResult\.wellFormed|ConcreteSpliceResult\.mk|⟨splicedWellFormed⟩' VisualProof
rg -n '\bsorry\b|\baxiom\b|\bunsafe\b' VisualProof/Diagram/Concrete/Subgraph/{Splice,Factorization,FactorizationNaturality,FactorizationSemantics,SpliceExamples}.lean
```

Expected: no displaced result API use, no direct example construction, and no new proof escape.

- [x] **Step 4: Check file sizes and task-owned diff**

Run:

```bash
wc -l VisualProof/Diagram/Concrete/Subgraph/{Splice,Factorization,FactorizationNaturality,FactorizationSemantics,SpliceExamples}.lean
git diff --check
git status --short
```

Expected: size policy satisfied, no whitespace errors, and only task-owned files are modified.

- [x] **Step 5: Append conformance evidence and commit**

Append `<conformance>` to `/tmp/vpa-splice-result-encapsulation-foundation-20260728-01.md`, stage only task-owned files, and commit with:

```bash
git commit -m "refactor: encapsulate concrete splice results"
```
