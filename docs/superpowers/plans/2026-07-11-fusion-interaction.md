# Fusion Interaction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the existing fusion proof step user-authorable by wire double-click and selected-wire `F` in the main proof assistant.

**Architecture:** Extend only `ProofMoveController`, the existing gesture-to-step authority. Both gestures construct the same `{ rule: 'fusion', wire }` value and pass it through the controller's existing commit path, leaving kernel semantics and every adjacent interaction system unchanged.

**Tech Stack:** TypeScript, Vitest, existing proof kernel and application interaction layer.

## Global Constraints

- Add no context-menu action.
- Change no hover, selection, refusal, history, timeline, motion, or physics behavior.
- Preserve term-node double-click conversion and every existing keyboard binding.
- Run focused non-physics tests and type checking only; physics tests are excluded because physics is untouched.
- Land the interaction on `main` before integrating it into the game branch.

---

### Task 1: Route the two fusion gestures through the existing proof-move controller

**Files:**
- Modify: `src/app/interact/moves.ts:222-280`
- Modify: `tests/app/moves.test.ts`

**Interfaces:**
- Consumes: `ProofMoveController.doubleClick(sample: PointerSample): boolean`, `ProofMoveController.keyDown(sample: KeySample): boolean`, and the existing `ProofMoveControllerOptions.apply(step: ProofStep): void` commit sink.
- Produces: wire double-click and plain `F` with exactly one selected wire each submit `{ readonly rule: 'fusion'; readonly wire: WireId }` through `ProofMoveController.#commit`.

- [ ] **Step 1: Add failing controller tests for double-click and `F`**

Add imports for `ProofMoveController`, `ProofStep`, `Engine`, `Theme`, and `Hit`, then add a small controller fixture whose `apply` callback records submitted steps. Build an eligible fusion diagram exactly as follows:

```ts
function fusionFixture() {
  const b = new DiagramBuilder()
  const producer = b.termNode(b.root, p('\\x. x'))
  const consumer = b.termNode(b.root, p('q y'))
  const wire = b.wire(b.root, [
    { node: producer, port: { kind: 'output' } },
    { node: consumer, port: { kind: 'freeVar', name: 'q' } },
  ])
  return { diagram: b.build(), wire }
}
```

Instantiate `ProofMoveController` with a host stub containing `ownerDocument`, inert engine/theme values cast to their declared types, and mutable `selection`/`applied` arrays. Assert:

```ts
expect(controller.doubleClick(pointer({ kind: 'wire', id: wire }))).toBe(true)
expect(applied).toEqual([{ rule: 'fusion', wire }])

selection = [{ kind: 'wire', id: wire }]
expect(controller.keyDown(key('f'))).toBe(true)
expect(applied).toEqual([{ rule: 'fusion', wire }])
```

In the same tests, run the captured step through `applyStep(diagram, step, ctx())` and assert that the producer and fusion wire are absent afterward. This proves the dispatch reaches the existing kernel semantics without duplicating them.

- [ ] **Step 2: Add failing scope-boundary tests**

Pin the non-feature behavior with these assertions:

```ts
selection = [{ kind: 'wire', id: wire }, { kind: 'node', id: producer }]
expect(controller.keyDown(key('f'))).toBe(false)
expect(applied).toEqual([])

selection = [{ kind: 'node', id: producer }]
expect(controller.keyDown(key('f'))).toBe(false)
expect(applied).toEqual([])
```

Retain the existing orientation-vocabulary test and add no expectation for a
fusion action descriptor; this pins the absence of a context-menu entry.

- [ ] **Step 3: Run the focused test to verify the new cases fail**

Run: `npx vitest run tests/app/moves.test.ts`

Expected: FAIL because wire double-click returns `false` and `F` is not consumed.

- [ ] **Step 4: Implement the minimal double-click dispatch**

At the start of `ProofMoveController.doubleClick`, after updating the pointer
and checking `active()`, add only:

```ts
if (sample.hit?.kind === 'wire') {
  this.#commit({ rule: 'fusion', wire: sample.hit.id })
  return true
}
```

Leave the existing term-node conversion branch unchanged below it.

- [ ] **Step 5: Implement the minimal selected-wire `F` dispatch**

In `ProofMoveController.keyDown`, after Escape/citation-cycle handling and
before the existing Delete/Backspace/W key filter, add:

```ts
if ((sample.key === 'f' || sample.key === 'F')
  && !sample.ctrlKey && !sample.altKey && !sample.metaKey) {
  const selection = this.#options.selection()
  if (selection.length !== 1 || selection[0]?.kind !== 'wire') return false
  this.#commit({ rule: 'fusion', wire: selection[0].id })
  return true
}
```

Do not edit `#openMenu`, `#appendAction`, overlays, the viewport, shell,
history, feedback, motion, or physics.

- [ ] **Step 6: Run the focused tests and type checker**

Run: `npx vitest run tests/app/moves.test.ts tests/app/proof-front.test.ts tests/architecture/interaction-ownership.test.ts`

Expected: all selected tests pass.

Run: `npm run typecheck`

Expected: exit code 0.

- [ ] **Step 7: Audit the final diff for scope compliance**

Run: `git diff --check`

Expected: exit code 0.

Run: `git diff --name-only`

Expected implementation/test paths only: `src/app/interact/moves.ts` and
`tests/app/moves.test.ts`, in addition to this approved design and plan.

Run: `git diff -- src/app/interact/moves.ts | rg "openMenu|appendAction|overlay|refuse|history|physics"`

Expected: no output.

- [ ] **Step 8: Commit the main-assistant feature**

```bash
git add docs/superpowers/specs/2026-07-11-fusion-interaction-design.md \
  docs/superpowers/plans/2026-07-11-fusion-interaction.md \
  src/app/interact/moves.ts tests/app/moves.test.ts
git commit -m "feat: author fusion from its wire"
```
