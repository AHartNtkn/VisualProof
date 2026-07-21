# In-place Head-strip Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make TypeScript and Lean `headStrip` replace a local binary rigid-head equation with corresponding nontrivial argument equations, discharge trivial/nullary matches, and refuse multi-endpoint or nonlocal equation wires.

**Architecture:** TypeScript constructs the final record maps directly from surviving nodes and wires. Lean defines a checked two-node/one-wire selection, uses `FrameDomains` and `removeRaw` as the dense survivor authority, and appends only the compact argument equations to that frame; provenance, interface transport, and semantic simulation are rebuilt around the survivor maps.

**Tech Stack:** TypeScript 5.5, Vitest 2, Lean 4.30, VisualProof concrete-diagram survivor domains and semantic simulation framework.

## Global Constraints

- The selected output wire has exactly the two selected term-output endpoints; otherwise refuse and require severing first.
- The selected output wire is scoped exactly at the selected nodes' region; an
  ancestor-owned value is not deleted by a local reduction.
- The two source term nodes and their shared output wire are absent from every successful result.
- Trivial and nullary matches discharge completely.
- TypeScript and Lean expose one matching semantic rule; no augmenting compatibility path remains.
- Preserve unrelated user changes under `docs/goals/`.

---

### Task 1: TypeScript replacement behavior

**Files:**
- Modify: `tests/kernel/rules/headstrip.test.ts`
- Modify: `src/kernel/rules/headstrip.ts`

**Interfaces:**
- Consumes: `applyHeadStrip(d, a, b, correspondence, reservation?) : Diagram`, `mkDiagram`, and existing stable node/wire IDs.
- Produces: the same public function signature with destructive binary-equation semantics.

- [ ] **Step 1: Replace augmenting expectations with final-graph expectations**

Update the principal nontrivial test to assert:

```ts
expect(out.nodes[n1]).toBeUndefined()
expect(out.nodes[n2]).toBeUndefined()
expect(out.wires[weq]).toBeUndefined()
expect(out.wires[wa]!.endpoints).toEqual([])
```

Retain the assertions for exactly two generated closure nodes, their support
wires, and their one fresh binary output wire. Rename the all-trivial test and
assert both input nodes and the old equation wire are absent. Add a nullary
case for `\\x. x —o— \\x. x` with no remaining nodes or wires from the match.

- [ ] **Step 2: Add the binary-wire refusal regression**

Construct three rigid-head term nodes on one output wire and assert:

```ts
expect(() => applyHeadStrip(d, first, second)).toThrowError(/extra endpoints.*sever/i)
expect(d.nodes[first]).toBeDefined()
expect(d.wires[equation]!.endpoints).toHaveLength(3)
```

The unchanged input assertions establish refusal without mutation.

- [ ] **Step 3: Run the focused test and observe RED**

Run:

```bash
npx vitest run tests/kernel/rules/headstrip.test.ts
```

Expected: failures report that the source nodes/wire still exist, the trivial
case is still a no-op, and the three-endpoint equation is accepted.

- [ ] **Step 4: Implement the binary gate and direct survivor construction**

After resolving the common output wire, inspect `d.wires[oa]!.endpoints` and
raise:

```ts
throw new RuleError(
  `head strip requires a binary equation wire; '${oa}' has extra endpoints, sever it first`,
)
```

when its length is not two. Build `nodes` without keys `a` and `b`. Build
`wires` without `oa`, filtering endpoints whose `node` is `a` or `b` from all
survivors. Keep the existing argument-pair generation and attach logic, but
attach only to the survivor wire records. Update the rule comment to state the
full equivalence and replacement behavior.

- [ ] **Step 5: Run focused tests and type checking for GREEN**

Run:

```bash
npx vitest run tests/kernel/rules/headstrip.test.ts
npm run typecheck
```

Expected: the focused file passes and TypeScript reports no errors.

### Task 2: Interaction and durable-document migration

**Files:**
- Modify: `tests/app/moves.test.ts`
- Modify: `docs/superpowers/specs/2026-07-12-head-strip-interaction-design.md`
- Modify: `docs/superpowers/plans/2026-07-12-head-strip-interaction.md`

**Interfaces:**
- Consumes: `proofConnectionStep`, whose dry run already delegates legality to `applyStep`/`applyHeadStrip`.
- Produces: sever-first multi-output interaction behavior without a second UI gate.

- [ ] **Step 1: Replace the accepted three-output gesture test**

Rename the test to `refuses head-strip on a three-output equality wire until it is severed` and assert:

```ts
expect(() => proofConnectionStep(
  d, outputEnd(wire, a), outputEnd(wire, c), 'forward', 64,
)).toThrow(/binary equation wire.*extra endpoints.*sever/i)
```

Leave the geometry-only target-leg highlighting test intact: exact endpoint hit
testing remains useful even though the kernel refuses this proof rule.

- [ ] **Step 2: Run the interaction test**

Run:

```bash
npx vitest run tests/app/moves.test.ts
```

Expected: PASS once Task 1's kernel gate is active.

- [ ] **Step 3: Remove displaced durable statements**

Change the older interaction spec and implementation plan so they state that
same-wire endpoint selection identifies a candidate pair, but `headStrip`
requires the wire to be binary and destructively replaces it. Delete statements
that the original remains or that an exact pair on a three-output wire is
accepted.

### Task 3: Lean executable replacement

**Files:**
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Equational.lean`

**Interfaces:**
- Consumes: `Diagram.CheckedSelection`, `FrameDomains`, `ConcreteDiagram.removeRaw`, `SurvivorDomain.index?`, `WireProvenance.rootFiltered`, and `InterfaceTransport.survivors`.
- Produces: `HeadStripPayload.selection`, `HeadStripPayload.domains`, a survivor-based `headStripRaw`, and matching receipt transport.

- [ ] **Step 1: Add the proof-bearing binary equation gate**

Extend `HeadStripPayload` after `secondOutput` with:

```lean
  outputBinary : (input.val.wires outputWire).endpoints.length = 2
```

Define a checked selection whose request is:

```lean
{
  anchor := payload.region
  childRoots := []
  directNodes := [first, second]
  explicitWires := [payload.outputWire]
}
```

Prove validity from `distinct`, `firstNode`, `secondNode`, the two output
occurrences, endpoint `Nodup`, and `outputBinary`. Define
`HeadStripPayload.domains : FrameDomains input.val payload.selection := {}`.

- [ ] **Step 2: Add a compile-time replacement specification and observe RED**

Before changing `headStripRaw`, add the expected count statement:

```lean
@[simp] theorem headStripRaw_nodeCount
    (payload : HeadStripPayload input first second) :
    (headStripRaw input payload).nodeCount =
      payload.domains.nodes.count +
        (payload.argumentIndices.length + payload.argumentIndices.length) := by
  rfl
```

Run:

```bash
lake build VisualProof.Rule.Equational
```

Expected: FAIL because the incumbent raw diagram starts from
`input.val.nodeCount`, not the survivor frame's node count.

- [ ] **Step 3: Rebase all fresh indices and endpoint attachments on the frame**

Change `firstAddedNode`, `secondAddedNode`, and free-endpoint types to use
`payload.domains.nodes.count`. Map original support wires with
`payload.domains.wires.index?`; binary-gate facts prove every support wire is a
survivor. Replace `headStripLiftEndpoint` and old-wire append logic with frame
endpoints already reindexed by `removeRaw`.

- [ ] **Step 4: Define the final raw diagram directly from survivors**

Let:

```lean
let frame := input.val.removeRaw payload.selection payload.domains
```

Set counts to `frame.nodeCount + 2 * argumentIndices.length` and
`frame.wireCount + argumentIndices.length`; use `Fin.addCases frame.nodes` and
`Fin.addCases frame.wires` for old survivors plus new compact closure nodes and
binary equation wires. There is no raw definition that contains all input nodes
or all input wires.

- [ ] **Step 5: Rebuild provenance, interface transport, and receipt checking**

Define the source-to-frame wire map from `payload.domains.wires.index?`, then
lift it with `Fin.castAdd payload.argumentIndices.length` into the final raw
wire carrier. `headStripWireProvenance` uses that injective partial map;
`headStripInterfaceTransport` maps surviving root wires through it and returns
`none` for the removed output wire. Keep `applyHeadStrip` and its realization
theorems public with their existing signatures.

- [ ] **Step 6: Compile the executable module for GREEN**

Run:

```bash
lake build VisualProof.Rule.Equational
```

Expected: PASS, including the new count theorem and the binary payload gate.

### Task 4: Lean full-equivalence semantic proof

**Files:**
- Modify: `VisualProof/Rule/Equational.lean`
- Rebuild: `VisualProof/Rule/Soundness/Equational/HeadStripSemantic.lean`
- Rebuild: `VisualProof/Rule/Soundness/Equational/HeadStripSimulation.lean`
- Verify imports: `VisualProof/Rule/Soundness/Equational/FusionSemantic.lean`

**Interfaces:**
- Consumes: `HeadStripPayload.argumentEvaluationsEqual`, survivor maps from Task 3, `LambdaModel.eval`, and beta-eta congruence constructors.
- Produces: forward and backward concrete semantic simulation for the replacement raw diagram and the unchanged public `applyHeadStrip_sound` integration.

- [ ] **Step 1: Replace the proposition-level augmenting theorem**

Delete `headStrip_addition_equiv`. Add a theorem whose shape is:

```lean
theorem headStrip_replacement_equiv
    (original arguments : Prop)
    (decompose : original → arguments)
    (recompose : arguments → original) :
    original ↔ arguments := ⟨decompose, recompose⟩
```

Add the term-level recomposition lemma showing that aligned bound-head spines
with equal corresponding prefix-closed argument evaluations have equal whole
term evaluations in the canonical model.

- [ ] **Step 2: Run formal soundness and observe RED**

Run:

```bash
lake build VisualProof.Rule.Soundness.Equational.HeadStripSimulation
```

Expected: FAIL at append-specific lemmas such as `headStripRaw_oldNode`,
`Fin.castAdd` old-wire identities, and backward simulation that previously
discarded the added argument conjuncts while retaining the originals.

- [ ] **Step 3: Rebuild structural semantic lemmas around survivor origins**

Replace old-node/old-wire append lemmas with exact statements over
`payload.domains.nodes.origin`, `payload.domains.wires.origin`, and their
`index?` maps. Exact-scope wires and local occurrences consist of reindexed
survivors plus the fresh argument equations only in `payload.region`.

- [ ] **Step 4: Rebuild forward and backward focused-region transport**

Forward transport derives fresh argument-wire values with
`argumentEvaluationsEqual` and omits the selected source equation items.
Backward transport reads every target argument equation, applies the new
recomposition lemma, and supplies the two removed source term equations on one
shared value. Other node and child-region denotations transport through survivor
origin maps in both directions.

- [ ] **Step 5: Restore receipt-level soundness**

Re-establish boundary, root-context, and successful-receipt theorems using the
new provenance/interface map. Confirm `VisualProof/Rule/Soundness.lean` needs no
new constructor or orientation branch because `headStrip` remains equivalent.

- [ ] **Step 6: Compile all Lean code for GREEN**

Run:

```bash
lake build
```

Expected: all Lean targets build with no append-only head-strip theorem or
simulation path remaining.

### Task 5: Cross-language conformance and final validation

**Files:**
- Modify: `/tmp/visualproof-headstrip-foundation.zGFCzZ/foundation.md`

**Interfaces:**
- Consumes: the complete TypeScript/Lean changes from Tasks 1-4.
- Produces: authoritative validation evidence and the foundation conformance receipt.

- [ ] **Step 1: Audit displaced behavior**

Run:

```bash
rg -n "originals stay|original equation remains|originals untouched|nothing added, nothing removed|headStrip_addition_equiv|three-output.*head-strip|multi-output.*headStrip" src tests VisualProof docs/superpowers
```

Expected: no active statement encoding the displaced semantics. Historical
descriptions are corrected where they remain durable instructions.

- [ ] **Step 2: Run all authoritative validation**

Run:

```bash
npx vitest run tests/kernel/rules/headstrip.test.ts tests/app/moves.test.ts
npm test
npm run typecheck
npm run formal:tags
lake build
rg -n "sorry|admit|decreasing_by sorry|^axiom " VisualProof
git diff --check
```

Expected: all commands exit zero; the placeholder audit prints no matches.

- [ ] **Step 3: Review scope and append conformance**

Inspect `git status --short` and `git diff --stat`; confirm `docs/goals/` remains
untouched. Append `<conformance>` to the foundation record listing the final
owners, deleted augmenting structures, migrated interaction/doc surfaces, exact
commands, and evidence that the previous model is absent.
