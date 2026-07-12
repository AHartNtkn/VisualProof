# Shared Relation Workspace Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to execute this plan task-by-task.

**Goal:** Give proof-mode comprehension abstraction, substitution, and selected-pattern copying the approved shared interactions, with exact live matching, editable ordered ports, atomic cancellation, and durable gesture-level proof history.

**Architecture:** Replace the substitution-specific `ComprehensionEditor`/fixed-arity draft with one `RelationWorkspace` configured by `SubstituteTransaction` or `AbstractTransaction`. Retain the kernel comprehension rules and exact subgraph matcher as semantic authorities. Introduce a pure `CopyPlanner` shared by Edit, Proof, and the workspace, and make `ProofAction`—not `ProofStep`—the persisted and visible history unit.

**Tech Stack:** TypeScript, Vitest, Canvas/DOM interaction controllers, Playwright, existing diagram kernel and renderer.

**Global Constraints:** Work on a feature branch from `main`; preserve unrelated changes. Use `apply_patch` for source edits. Write each failing test before its implementation. Do not add a graphical-insertion or copy-pattern kernel rule. Do not preserve the displaced flat theorem/history format through aliases or compatibility parsing. Do not run `test:physics` unless a physics implementation file changes; Ctrl routing tests belong in ordinary interaction tests.

---

## Task 1: Make `ProofAction` the kernel proof-record unit

**Files:**

- Create: `src/kernel/proof/action.ts`
- Modify: `src/kernel/proof/theorem.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `src/kernel/proof/index.ts`
- Test: `tests/kernel/proof/action.test.ts`
- Test: `tests/kernel/proof/compose.test.ts`
- Test: `tests/kernel/proof/theorem.test.ts`

### 1.1 Write failing action replay tests

Add tests proving:

- a one-step action replays exactly like its step;
- a multi-step action produces one before/after unit while replaying every trusted step in order;
- failures identify both action index and constituent step index;
- placement hints accept only indices of nodes introduced by the whole action;
- theorem boundary survival is checked after every constituent step, not merely after every action.

Use presentation-neutral placement indices so proof composition never needs to remap generated node IDs:

```ts
export type PlacementHint = {
  readonly introducedNode: number
  readonly x: number
  readonly y: number
}

export type ProofAction = {
  readonly label: string
  readonly steps: readonly ProofStep[]
  readonly placements: readonly PlacementHint[]
}
```

Run:

```bash
npx vitest run --config vitest.config.ts tests/kernel/proof/action.test.ts tests/kernel/proof/theorem.test.ts
```

Expected: fail because `ProofAction`, `applyAction`, and `replayActions` do not exist and `Theorem` still stores flat steps.

### 1.2 Implement the action authority

In `action.ts`, add:

```ts
export function singleStepAction(label: string, step: ProofStep, placements: readonly PlacementHint[] = []): ProofAction

export function applyAction(
  diagram: Diagram,
  action: ProofAction,
  ctx: ProofContext,
  orientation?: 'forward' | 'backward',
  afterStep?: (diagram: Diagram, stepIndex: number) => void,
): Diagram

export function replayActions(
  diagram: Diagram,
  actions: readonly ProofAction[],
  ctx: ProofContext,
  afterStep?: (diagram: Diagram, actionIndex: number, stepIndex: number) => void,
  orientation?: 'forward' | 'backward',
): Diagram
```

`applyAction` must:

1. reject an empty label or empty step list;
2. replay steps only through `applyStep`;
3. compute introduced node IDs as `after.nodes - before.nodes`, sorted by ID;
4. reject non-finite coordinates, duplicate `introducedNode` entries, or out-of-range indices;
5. never let placement metadata influence the resulting diagram.

Change `Theorem` to `actions` and optional `backActions`. Update `checkTheorem` to use `replayActions` and preserve the existing per-step boundary-survival guarantee.

### 1.3 Preserve groups during proof composition

Replace `composeProofs(..., tail: ProofStep[])` with:

```ts
export function composeActions(
  meetTarget: Diagram,
  meetSource: Diagram,
  tail: readonly ProofAction[],
  ctx: ProofContext,
): ProofAction[]
```

Map and replay every constituent step sequentially, recomputing the isomorphism after each. Emit one mapped action for each input action with the same label and placement hints. Add tests where a two-step action mints IDs and a later action refers to them.

Run:

```bash
npx vitest run --config vitest.config.ts tests/kernel/proof/action.test.ts tests/kernel/proof/compose.test.ts tests/kernel/proof/theorem.test.ts
```

Expected: pass.

### 1.4 Commit

```bash
git add src/kernel/proof/action.ts src/kernel/proof/theorem.ts src/kernel/proof/compose.ts src/kernel/proof/index.ts tests/kernel/proof/action.test.ts tests/kernel/proof/compose.test.ts tests/kernel/proof/theorem.test.ts
git commit -m "refactor: make proof actions authoritative"
```

## Task 2: Migrate proof JSON, stores, sessions, replay, and derivation builders

**Files:**

- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/store.ts`
- Modify: `src/app/session.ts`
- Modify: `src/app/replay.ts`
- Modify: `src/app/index.ts`
- Modify: `src/theories/macros.ts`
- Modify: all theorem builders under `src/theories/*.ts` that construct `Theorem`
- Modify: `scripts/emit-theories.ts` if its types require it
- Regenerate for validation only: git-ignored `examples/*.json`
- Test: `tests/kernel/proof/json.test.ts`
- Test: `tests/kernel/proof/store.test.ts`
- Test: `tests/app/session.test.ts`
- Test: `tests/app/replay.test.ts`

### 2.1 Write failing persistence and timeline tests

Test that:

- theorem JSON writes `actions`/`backActions`, including labels, steps, and placements;
- JSON containing `steps` or `backSteps` is rejected as an unknown obsolete field;
- a multi-step action consumes exactly one timeline cursor position and one undo/redo;
- replay counts and scrubs actions, while exposing the constituent steps of the active action for animation;
- declaration and fixed-front assembly preserve groups exactly;
- saved libraries round-trip groups.

Run:

```bash
npx vitest run --config vitest.config.ts tests/kernel/proof/json.test.ts tests/kernel/proof/store.test.ts tests/app/session.test.ts tests/app/replay.test.ts
```

Expected: fail against the flat `steps` and `transitions` models.

### 2.2 Replace flat persistence and timeline state

Use this single timeline model:

```ts
export type ProofTimeline = {
  readonly states: readonly Diagram[]
  readonly actions: readonly ProofAction[]
  readonly cursor: number
}
```

Replace `timelineActiveSteps` with `timelineActiveActions`. Change `applyTrack`, `applyForward`, and `applyBackward` to accept `ProofAction` and obtain the next state through `applyAction`. Preserve fixed-boundary checks after every constituent step by passing the action callback, not only checking the final diagram.

JSON action parsing must call `stepFromJson` for each nested step and enforce exact keys. Do not accept flat arrays. Update replay to advance by action; its detail model may expose `action.steps` for within-action animation without creating extra user scrub stops.

### 2.3 Migrate all producers, fixtures, and generated artifacts

Change the shared theory emitter/builder primitive so existing calls such as:

```ts
e.push('iterate base', step)
```

append `singleStepAction(label, step)`. Migrate direct theorem literals and test fixtures explicitly. Regenerate authoritative generated theory files:

```bash
npm run emit:theories
```

Do not hand-edit generated JSON and do not stage the git-ignored `examples/` output.

### 2.4 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/kernel/proof/json.test.ts tests/kernel/proof/store.test.ts tests/app/session.test.ts tests/app/replay.test.ts
npm run typecheck
git add src tests scripts
git commit -m "refactor: persist gesture-level proof actions"
```

Expected: tests and typecheck pass; `rg -n "backSteps|timelineActiveSteps|transitions: readonly ProofStep|readonly steps: readonly ProofStep" src tests` returns no displaced model definitions.

## Task 3: Replace the fixed comprehension draft with a shared editable relation draft

**Files:**

- Create: `src/app/relation-workspace-draft.ts`
- Create: `tests/app/relation-workspace-draft.test.ts`
- Delete after migration in Task 5: `src/app/comprehension-draft.ts`
- Delete after migration in Task 5: `tests/app/comprehension-draft.test.ts`

### 3.1 Write failing port-model tests

Cover:

- substitution starts with a locked ordered forced block matching target arity;
- abstraction starts with no ports;
- dropping a draft wire at a strip index creates an optional port at that spatial position;
- optional ports reorder; forced ports neither move nor delete;
- deleting an optional port also removes its pending host binding;
- an optional substitution parameter must be bound or removed before finalization;
- abstraction boundary order and arity are derived from the submitted strip;
- all draft mutations are one snapshot each and undo/redo restores port order and bindings.

Define the neutral model:

```ts
export type RelationPort = {
  readonly id: string
  readonly wire: WireId
  readonly kind: 'forced' | 'optional'
  readonly hostWire?: WireId
}

export type RelationWorkspaceDraft = {
  readonly host: Diagram
  readonly mode: 'substitute' | 'abstract'
  readonly history: readonly RelationWorkspaceSnapshot[]
  readonly cursor: number
}
```

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/relation-workspace-draft.test.ts
```

Expected: fail because the neutral model does not exist.

### 3.2 Implement canonical draft and port operations

Provide pure operations:

```ts
beginSubstitutionDraft(host, bubble): RelationWorkspaceDraft
beginAbstractionDraft(host): RelationWorkspaceDraft
currentRelationDraft(draft): RelationWorkspaceSnapshot
insertOptionalPort(draft, wire, optionalIndex, hostWire?): RelationWorkspaceDraft
moveOptionalPort(draft, portId, optionalIndex): RelationWorkspaceDraft
deleteOptionalPort(draft, portId): RelationWorkspaceDraft
bindOptionalPort(draft, portId, hostWire): RelationWorkspaceDraft
materializeRelationDraft(draft): { relation: DiagramWithBoundary; attachments: WireId[] }
```

Retain and rename the existing useful connection, spawning, fission, wrapping, external-reference presentation, and snapshot-history functions. Validation is mode-specific but belongs in this one model. It must not call `applyComprehensionInstantiate` as a universal draft validator, because abstraction drafts have no target bubble; validate diagram integrity and port invariants here, and let each transaction run its kernel rule at finalization.

### 3.3 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/app/relation-workspace-draft.test.ts
git add src/app/relation-workspace-draft.ts tests/app/relation-workspace-draft.test.ts
git commit -m "feat: add shared editable relation draft"
```

## Task 4: Implement exact abstraction candidates and maximal-set selection

**Files:**

- Create: `src/app/abstraction-matches.ts`
- Test: `tests/app/abstraction-matches.test.ts`
- Reuse: `src/kernel/diagram/subgraph/match.ts`
- Reuse: `src/kernel/diagram/subgraph/occurrence.ts`

### 4.1 Write failing matcher tests

Create fixtures covering:

- exact matches inside the wrap and exclusion of identical shapes outside it;
- diagonal boundary arguments preserving repeated-wire order;
- overlap by node, internal wire, or selected region;
- deterministic maximal-set enumeration ordered by descending size then canonical key sequence;
- Tab forward and Shift+Tab backward cycling;
- click exclusion, restoration, and stale-exclusion removal after draft changes;
- exhaustive zero matches versus matcher fuel exhaustion;
- a nonempty unmatched draft disabling finalize;
- an empty nullary draft producing exactly one marker state, never infinite matches.

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/abstraction-matches.test.ts
```

Expected: fail because abstraction candidate orchestration does not exist.

### 4.2 Implement candidate extraction

Define:

```ts
export type AbstractionCandidate = {
  readonly key: string
  readonly occurrence: AbstractionOccurrence
  readonly footprint: {
    readonly nodes: ReadonlySet<NodeId>
    readonly wires: ReadonlySet<WireId>
    readonly regions: ReadonlySet<RegionId>
  }
}

export type AbstractionMatchResult =
  | { readonly status: 'complete'; readonly candidates: readonly AbstractionCandidate[] }
  | { readonly status: 'exhausted'; readonly candidates: readonly AbstractionCandidate[] }
```

Call `findOccurrences` in exact, boundary-pinned mode, convert each through `occurrenceToSelection`, and filter every selected item to the provisional wrap contents. Derive the canonical key from sorted selected IDs plus ordered argument wire IDs. Externally bound atoms whose binder is outside the pattern remain a precise refusal because the kernel abstraction rule rejects open binder stubs.

### 4.3 Implement deterministic maximal independent sets

Use backtracking over candidates sorted by key. Retain a set only when it is maximal under the current exclusions. Sort finished sets by the approved ordering and deduplicate by their key sequence. Expose:

```ts
maximalOccurrenceSets(candidates, excluded): readonly (readonly AbstractionCandidate[])[]
cycleOccurrenceSet(state, delta: 1 | -1): OccurrenceSetState
toggleOccurrenceExclusion(state, key): OccurrenceSetState
```

The solver must be fuel-bounded separately from diagram matching and return an explicit exhausted state rather than a partial set presented as complete.

### 4.4 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/app/abstraction-matches.test.ts tests/kernel/rules/comprehension-diagonal.test.ts
git add src/app/abstraction-matches.ts tests/app/abstraction-matches.test.ts
git commit -m "feat: derive abstraction occurrence sets"
```

## Task 5: Replace `ComprehensionEditor` with the single `RelationWorkspace`

**Files:**

- Create: `src/app/relation-workspace.ts`
- Modify: `src/app/style.css`
- Modify: `src/app/index.ts`
- Delete: `src/app/comprehension-editor.ts`
- Delete: `src/app/comprehension-draft.ts`
- Replace: `tests/app/comprehension-editor.test.ts` with `tests/app/relation-workspace.test.ts`
- Delete: `tests/app/comprehension-draft.test.ts` after its substantive cases are migrated

### 5.1 Write failing shared-window tests

Test one DOM class and one draft authority in both modes:

- both modes use `RelationWorkspace` and the same spawn, connect, fission, selection, undo/redo, move, and resize handlers;
- title/finalize copy changes by transaction configuration, not by a second editor;
- the port strip renders forced and optional ports distinctly;
- wire-to-strip drop inserts, port drag reorders, and Delete removes only optional ports;
- invalid draft edits preserve the previous valid snapshot;
- cancel clears pointer claims, highlights, gestures, and mounted DOM.

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/relation-workspace.test.ts
```

Expected: fail because only `ComprehensionEditor` exists.

### 5.2 Implement the shared window

Use one host contract:

```ts
export type RelationWorkspaceTransaction = {
  readonly mode: 'substitute' | 'abstract'
  readonly title: string
  readonly finalizeLabel: string
  readonly sourceDiagram: () => Diagram
  readonly sourceBoundary: () => readonly WireId[]
  previewShapes(): readonly Shape[]
  status(snapshot: RelationWorkspaceSnapshot): WorkspaceStatus
  finalize(snapshot: RelationWorkspaceSnapshot, placements: readonly PlacementHint[]): void
  cancel(): void
}
```

`RelationWorkspace` owns all window mechanics; transactions own only host semantics. Move existing construction controllers behind it. Add a real port-strip hit target rather than inferring boundary edits from canvas frame slots.

### 5.3 Migrate substitution without behavior loss

Add `SubstituteTransaction` in the same file or a narrow `src/app/relation-transactions.ts` if needed. It must:

- snapshot the source bubble and source fingerprint at open;
- initialize forced ports from bubble arity;
- materialize optional parameter ports as `attachments`;
- run a scratch `comprehensionInstantiate` for status and the real kernel step at finalization;
- emit one labeled `ProofAction`;
- preserve the workspace on kernel refusal.

Migrate every substantive old draft/editor test before deleting the files. Do not add re-exports with old names.

### 5.4 Validate displaced-authority removal and commit

```bash
npx vitest run --config vitest.config.ts tests/app/relation-workspace-draft.test.ts tests/app/relation-workspace.test.ts tests/kernel/rules/comprehension-instantiate.test.ts
rg -n "ComprehensionEditor|ComprehensionDraft|beginComprehensionDraft" src tests
```

Expected: tests pass; search has no matches.

```bash
git add src/app tests/app
git commit -m "feat: replace comprehension editor with relation workspace"
```

## Task 6: Add provisional proof wrapping and `AbstractTransaction`

**Files:**

- Create: `src/app/relation-transactions.ts`
- Modify: `src/app/actions.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/fixed-side-workspace.ts`
- Test: `tests/app/relation-transactions.test.ts`
- Modify: `tests/app/actions.test.ts`
- Modify: `tests/app/moves.test.ts`
- Test: `tests/app/abstraction-interaction.test.ts`

### 6.1 Write failing transaction tests

Cover ordinary track and both fixed fronts, in both orientations:

- invoking wrap opens the workspace immediately from the selected content;
- source diagram, proof cursor, and action list remain byte/fingerprint-identical while open;
- preview shapes show the provisional bubble around exactly the wrap selection;
- Escape/window close/cancel restores exact source state without an inverse step;
- mode/side switch, global undo/redo, theory replacement, return to Edit, or session reset first cancels the workspace;
- stale source fingerprint or missing live IDs blocks finalization without mutating source or draft;
- successful finalization commits exactly one `comprehensionAbstract` action.

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/relation-transactions.test.ts tests/app/abstraction-interaction.test.ts tests/app/moves.test.ts
```

Expected: fail because wrap still prompts for arity and immediately commits `vacuousIntro`.

### 6.2 Replace the proof wrap command

Replace proof-mode `vacuousWrap`'s arity prompt with `openAbstraction(sel, pointer)`. Keep Edit-mode bubble construction unchanged. Rename the proof action descriptor to describe the experienced operation, for example `abstractWrap`, rather than retaining a misleading vacuous-only label.

`AbstractTransaction` stores the untouched source, wrap selection, source fingerprint, exclusions, active set index, and empty-marker state. It derives previews and status from `abstraction-matches.ts` after every draft/port change.

### 6.3 Implement normal and empty finalization

For nonempty drafts, build the step from the active maximal set and submitted boundary order.

For an actually empty nullary draft:

- selected marker emits one zero-arity occurrence anchored in its containing region and one placement hint for the introduced atom;
- deselected marker emits zero occurrences, producing the trivial wrap;
- marker drag may change only to a region inside the wrap;
- a nonempty zero-match draft cannot use this path.

Run the real `applyComprehensionAbstract` through `applyAction`; close only on success.

### 6.4 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/app/relation-transactions.test.ts tests/app/abstraction-matches.test.ts tests/app/abstraction-interaction.test.ts tests/app/actions.test.ts tests/app/moves.test.ts
git add src/app tests/app
git commit -m "feat: author comprehension abstraction in proof mode"
```

## Task 7: Implement the pure shared `CopyPlanner`

**Files:**

- Create: `src/app/copy-planner.ts`
- Create: `tests/app/copy-planner.test.ts`
- Reuse: `src/kernel/diagram/subgraph/extract.ts`
- Reuse: `src/kernel/diagram/subgraph/splice.ts`
- Reuse: existing proof step constructors and appliers

### 7.1 Write failing planner tests

Test three destination policies:

- workspace copy structurally clones the complete selected pattern, maps IDs freshly, places at the drop point, and turns each crossing host wire into one loose root-scoped draft wire without creating a port or host binding;
- Edit copy uses the same extraction/ID map while preserving crossing attachment identities;
- Proof copy prefers a valid `iteration` plan;
- when iteration is invalid, Proof uses an ordinary construction recipe only if the entire copied pattern and every attachment can be reproduced;
- an impossible external binder, scope, polarity, or attachment yields a typed refusal and no partial diagram;
- scratch replay must fingerprint-match the intended attachment-pinned result before a target is offered;
- revalidation rejects a stale source or destination.

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/copy-planner.test.ts
```

Expected: fail because `CopyPlanner` does not exist.

### 7.2 Implement structural extraction once

Define:

```ts
export type CopyDestination =
  | { readonly kind: 'workspace'; readonly draft: Diagram; readonly region: RegionId; readonly at: Vec2 }
  | { readonly kind: 'edit'; readonly diagram: Diagram; readonly region: RegionId; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly diagram: Diagram; readonly region: RegionId; readonly orientation: ProofOrientation; readonly ctx: ProofContext }

export type CopyPlan =
  | { readonly kind: 'workspace' | 'edit'; readonly result: Diagram; readonly introduced: readonly NodeId[] }
  | { readonly kind: 'proof'; readonly action: ProofAction; readonly resultFingerprint: string }

export function planCopy(source, selection, destination): CopyPlan | CopyRefusal
export function revalidateCopy(plan, liveSource, liveDestination): CopyPlan | CopyRefusal
```

Use `extractSubgraph` as the sole structural extractor. Reject open binder stubs unless the binder is included in the selected pattern. Parameterize only the crossing-wire policy; do not fork extraction logic by surface.

### 7.3 Implement proof planning without a new kernel rule

First attempt one `iteration` step and replay it. If unavailable, compile a goal-directed recipe from the extracted pattern using a registry of existing constructors:

- atomic term/relation/bound-relation spawn;
- closed-term introduction where required by polarity;
- double-cut and vacuous-bubble wrapping;
- valid fission/fusion and wire joins where the target incidence requires them;
- any already-existing contextual construction step whose postcondition is exact structural progress toward the extracted target.

Each recipe emitter returns immutable candidate steps plus an explicit mapping from source attachment identities to destination wires. Replay the whole candidate on a scratch diagram, extract the alleged copy, and compare its boundary-pinned canonical fingerprint to the source pattern. If exact replay cannot prove the complete target, return refusal. Never expose a partial recipe.

Wrap accepted construction recipes in one `ProofAction` labeled `Copy selection`; iteration uses the same user-facing label.

### 7.4 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/app/copy-planner.test.ts tests/kernel/rules/iteration.test.ts
git add src/app/copy-planner.ts tests/app/copy-planner.test.ts
git commit -m "feat: plan contextual selected-pattern copies"
```

## Task 8: Replace iteration-only dragging with one selected-pattern copy controller

**Files:**

- Create: `src/app/interact/copy.ts`
- Modify: `src/app/interact/moves.ts`
- Modify: `src/app/interact/construct.ts`
- Modify: `src/app/relation-workspace.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/app/proof-front.ts`
- Test: `tests/app/copy-interaction.test.ts`
- Modify: `tests/app/fission-interaction.test.ts`
- Modify: `tests/app/moves.test.ts`

### 8.1 Write failing gesture-priority tests

Prove the complete overlap ordering:

1. Ctrl yields to physics and never begins copy;
2. a wire connection drag wins on a connection-capable wire segment;
3. internal subterm anatomy wins for fission and uses internal highlighting;
4. whole selected-pattern surface begins copy and uses an enclosing green group highlight;
5. all valid destinations use the same green preview regardless of iteration versus construction plan;
6. invalid destinations are not highlighted;
7. drop revalidates and commits one draft history action or one `ProofAction`;
8. cancellation/refusal leaves no partial objects or history entry.

Run:

```bash
npx vitest run --config vitest.config.ts tests/app/copy-interaction.test.ts tests/app/fission-interaction.test.ts tests/app/moves.test.ts
```

Expected: fail because `ProofMoveController` owns an iteration-only node drag.

### 8.2 Implement one controller over `CopyPlanner`

Create `CopyDragController` with adapters for source selection, destination surfaces, preview rendering, and commit. It must own the gesture once and ask `CopyPlanner` for targets; no surface may independently reimplement iteration dragging or structural copy.

Replace `IterationDrag` in `moves.ts`. Register the same controller with Edit, Proof, and `RelationWorkspace`. For host-to-workspace drops, convert canvas coordinates to workspace world coordinates and commit the returned structural result as one draft snapshot.

### 8.3 Commit actions and animation by user unit

Change shell/front apply callbacks to accept `ProofAction`. Motion may animate constituent steps sequentially, but timeline append occurs once after the action succeeds. A multi-step copy therefore has one undo and one replay stop.

### 8.4 Validate and commit

```bash
npx vitest run --config vitest.config.ts tests/app/copy-interaction.test.ts tests/app/fission-interaction.test.ts tests/app/moves.test.ts tests/app/relation-workspace.test.ts tests/app/session.test.ts
git add src/app tests/app
git commit -m "feat: share selected-pattern copy dragging"
```

## Task 9: Complete lifecycle, rendering, and browser demonstrations

**Files:**

- Modify: `src/app/shell.ts`
- Modify: `src/app/proof-front.ts`
- Modify: `src/app/fixed-side-workspace.ts`
- Modify: `src/app/style.css`
- Modify: existing Playwright helpers under `e2e/`
- Create: `e2e/relation-workspace.spec.ts`
- Create: `e2e/contextual-copy.spec.ts`

### 9.1 Add browser tests for the approved experience

Automate:

- ordinary and fixed proof fronts, forward and backward;
- wrap opening immediately with provisional bubble and exact cancel;
- the same workspace DOM class for substitute and abstract;
- selected-pattern drag from host into workspace;
- port create/reorder/delete and visible order;
- match highlighting, Tab/Shift+Tab set cycling, click exclusion/restoration;
- selected and deselected empty marker results;
- iteration and construction fallback with indistinguishable green preview;
- Ctrl drag reaching physics without copy ownership;
- one gesture, one undo, save/load, and one replay stop;
- lifecycle transitions canceling the owning transaction only.

Run each new spec red before implementation:

```bash
npx playwright test e2e/relation-workspace.spec.ts e2e/contextual-copy.spec.ts
```

Expected initially: fail at the first missing interaction, then pass after lifecycle/render integration.

### 9.2 Finish visible feedback and accessibility

Ensure the port strip has keyboard-focusable ports and descriptive labels, the empty marker exposes selected state, and status/refusal text distinguishes exhaustion, zero matches, exclusions, invalid ports, stale source, and kernel refusal. Reuse existing theme interaction colors; do not create a second copy highlight vocabulary.

### 9.3 Validate and commit

```bash
npx playwright test e2e/relation-workspace.spec.ts e2e/contextual-copy.spec.ts
git add src/app e2e
git commit -m "test: demonstrate relation authoring and contextual copy"
```

## Task 10: Remove displaced models and run decisive validation

**Files:**

- Modify/delete any remaining stale tests, examples, exports, CSS selectors, and generated files discovered below
- Append only: `/tmp/visualproof-foundation-20260712-shared-relation-workspace.md`

### 10.1 Run architectural absence checks

```bash
rg -n "ComprehensionEditor|ComprehensionDraft|beginComprehensionDraft|timelineActiveSteps|backSteps|readonly steps: readonly ProofStep|IterationDrag|graphicalInsertion|copyPattern" src tests docs/superpowers/specs/2026-07-12-shared-relation-workspace-design.md
```

Expected: no displaced implementation names in `src` or `tests`; the design spec may contain explanatory mentions only. Confirm exactly one authority for each:

```bash
rg -n "class RelationWorkspace|type RelationPort|function planCopy|class CopyDragController|type ProofAction" src
```

Expected: one defining location per responsibility, with imports elsewhere.

### 10.2 Run complete ordinary validation

```bash
npm run typecheck
npm test
npm run emit:theories
npx playwright test
git status --short
```

Expected: typecheck, ordinary Vitest suite, generation, and all Playwright tests pass. Generated files are clean after regeneration except for intended committed output. Do **not** run `npm run test:physics` unless `git diff --name-only` shows a physics implementation file changed.

If any in-repository failure appears, diagnose and repair it in this task, then rerun the failing focused command and the complete ordinary validation. Do not report it as a baseline failure.

### 10.3 Review spec coverage and implementation quality

Read the approved design and this plan line-by-line against the diff. Search for placeholders:

```bash
rg -n "TODO|FIXME|placeholder|not implemented|throw new Error\(['\"]TODO" src tests
```

Verify:

- every approved interaction has a behavioral test;
- no duplicate window, port, matching, copy, or history mechanics remain;
- kernel comprehension appliers still recheck final submissions;
- all multi-step gestures are atomic actions;
- every union/type change is reflected in JSON parsing, composition, replay, sessions, shell, fixed fronts, builders, fixtures, and generated files.

### 10.4 Append conformance evidence

Append a `<conformance>` section to `/tmp/visualproof-foundation-20260712-shared-relation-workspace.md` recording:

- implemented responsibilities and their owning files;
- deleted/replaced structures;
- migrated dependent surfaces;
- exact validation commands and results;
- searches proving the displaced models are absent.

Do not edit the foundation record's pre-action sections.

### 10.5 Final commit and branch completion

```bash
git add src tests scripts docs package.json
git commit -m "feat: complete shared relation authoring workflow"
```

Use `superpowers:verification-before-completion`, then `superpowers:finishing-a-development-branch` to merge the feature branch into `main` and remove its worktree/branch after successful integration, matching the repository's established cleanup expectation.
