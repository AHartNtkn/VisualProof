# Proof Interaction Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the production shell's parallel and two-phase proving UI with one orientation-aware direct-manipulation coordinator implementing the approved proving vocabulary.

**Architecture:** Pure helpers derive contextual steps, legal iteration targets, folded comprehensions, and citation occurrences. A disposable `ProofMoveController` owns proof-only pointer/key/menu/prompt/cycle state and emits ordinary `ProofStep` values through the existing shell session sink. The existing track and dual-front sessions remain unchanged and authoritative.

**Tech Stack:** TypeScript 5.5, Vitest 2, Playwright 1.60, immutable diagram kernel, existing `InteractiveViewport`, occurrence matcher, conversion tactics, and canvas shape overlays.

## Global Constraints

- The authoritative design is `docs/superpowers/specs/2026-07-10-proof-interaction-integration-design.md`.
- Forward and backward use one action/controller implementation; orientation is data.
- The action palette opens only after explicit still right-click and sits beside that pointer.
- Success produces no feedback message. Refusals remain verbatim and pointer-local.
- Citation arguments come only from matcher occurrences; manual wire picking is deleted.
- Named instantiation uses a folded reference comprehension, never the stored relation body.
- The approved history surface is the only history representation; Task 3 adds no memory box.
- Existing session application/declaration semantics are not rewritten.
- No physics source or physics-heavy test is touched.

## File Structure

- Create `src/app/interact/cite.ts`: pure theorem-side, occurrence filtering, candidate, and citation-step construction.
- Create `src/app/interact/moves.ts`: pure proof-step helpers plus the disposable proof-mode interaction coordinator.
- Create `tests/app/cite.test.ts`: infer-first citation semantics.
- Create `tests/app/moves.test.ts`: contextual Delete, targets, folded instantiation, and orientation parity.
- Modify `src/app/shell.ts`: one controller/sink integration; remove obsolete pending and backward paths.
- Modify `e2e/app.spec.ts`: actual-app explicit palette, direct mechanics, forward/backward parity, and absence of manual pickers.
- Modify `tests/architecture/interaction-ownership.test.ts`: displaced-path absence.
- Modify `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`: completion receipt only after green validation.

---

### Task 1: Pure proof-move semantics

**Files:**
- Create: `src/app/interact/moves.ts`
- Create: `tests/app/moves.test.ts`

**Interfaces:**

```ts
export type ProofOrientation = 'forward' | 'backward'
export type ProofDiscovery = { readonly sel: SubgraphSelection; readonly actions: readonly ActionDescriptor[] }
export function discoverProofActions(d: Diagram, hits: readonly Hit[], ctx: ProofContext, orientation: ProofOrientation): ProofDiscovery | null
export function contextualDeleteStep(d: Diagram, discovery: ProofDiscovery, fuel: number): ProofStep | null
export function iterationTargets(d: Diagram, sel: SubgraphSelection): readonly RegionId[]
export function foldedComprehension(ctx: ProofContext, name: string): DiagramWithBoundary
```

- [ ] Write failing tests proving absorb-normalized double-cut/vacuous/erase/deiterate precedence; erasure includes only same-region orphan riders; forward/backward discoveries expose the same action kinds except polarity-gated availability; targets are descendants of the selection anchor but never inside selected regions; folded comprehension contains one `ref` node and ordered boundary wires.

- [ ] Run `npm test -- tests/app/moves.test.ts` and verify RED because the module is absent.

- [ ] Implement discovery with existing `absorbHits`, `buildSelection`, and `applicableActions(d, sel, ctx, orientation === 'backward')`. Implement Delete by selecting the first available kind in `doubleCutElim`, `vacuousElim`, `erase`, `deiterate` order. For erasure only, extend `sel.wires` with `orphanedWires(d, new Set(sel.nodes))` whose scope equals `sel.region`.

```ts
const stepFor = (action: ActionDescriptor, sel: SubgraphSelection, fuel: number): ProofStep => {
  switch (action.kind) {
    case 'doubleCutElim': return { rule: 'doubleCutElim', region: sel.regions[0]! }
    case 'vacuousElim': return { rule: 'vacuousElim', region: sel.regions[0]! }
    case 'erase': return { rule: 'erasure', sel: withErasureOrphans(d, sel) }
    case 'deiterate': return { rule: 'deiteration', sel, fuel }
    default: throw new Error(`'${action.kind}' is not a contextual deletion`)
  }
}
```

- [ ] Implement `iterationTargets` by walking ancestry with `isAncestorOrEqual` and excluding every region inside a selected region. Implement `foldedComprehension` as one ref node with arity-many singleton wires forming the boundary.

- [ ] Run `npm test -- tests/app/moves.test.ts tests/app/actions.test.ts` and verify GREEN.

- [ ] Commit:

```bash
git add src/app/interact/moves.ts tests/app/moves.test.ts
git commit -m "feat: define shared proof move semantics"
```

---

### Task 2: Infer-first citation semantics

**Files:**
- Create: `src/app/interact/cite.ts`
- Create: `tests/app/cite.test.ts`

**Interfaces:**

```ts
export type CitationCandidate = {
  readonly name: string
  readonly direction: 'forward' | 'reverse'
  readonly from: DiagramWithBoundary
  readonly occurrences: readonly Occurrence[] | null
}
export function citationDirection(d: Diagram, region: RegionId, orientation: ProofOrientation): 'forward' | 'reverse'
export function citationCandidates(d: Diagram, hits: readonly Hit[], region: RegionId, ctx: ProofContext, orientation: ProofOrientation, fuel: number): { applicable: readonly CitationCandidate[]; closed: readonly CitationCandidate[] }
export function citationStep(d: Diagram, candidate: CitationCandidate, occurrenceIndex?: number, region?: RegionId): ProofStep
```

- [ ] Write failing tests with real verified theory fixtures proving: selection filters out non-containing occurrences and unrelated theorems; a unique occurrence supplies `occurrenceSelection` and `occ.attachments`; two occurrences remain in deterministic matcher order; backward orientation flips direction; a closed theorem builds an empty selection at the invocation region with no arguments.

- [ ] Run `npm test -- tests/app/cite.test.ts` and verify RED because the module is absent.

- [ ] Implement theorem-side selection (`lhs` for forward, `rhs` for reverse), closed-side detection, exact occurrence search, hit containment over occurrence node/wire/region images, candidate partition, and step construction. Propagate matcher fuel/undecided failures; do not list a theorem whose applicable occurrence set is empty.

- [ ] Run `npm test -- tests/app/cite.test.ts` and verify GREEN.

- [ ] Commit:

```bash
git add src/app/interact/cite.ts tests/app/cite.test.ts
git commit -m "feat: infer theorem citations from occurrences"
```

---

### Task 3: Disposable production proof controller

**Files:**
- Modify: `src/app/interact/moves.ts`
- Modify: `tests/app/moves.test.ts`

**Interfaces:**

```ts
export type ProofMoveControllerOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly diagram: () => Diagram
  readonly engine: () => Engine
  readonly selection: () => readonly Hit[]
  readonly setSelection: (hits: readonly Hit[]) => void
  readonly context: () => ProofContext
  readonly orientation: () => ProofOrientation
  readonly apply: (step: ProofStep) => void
  readonly refuse: (text: string, pointer: Vec2) => void
  readonly theme: () => Theme
  readonly fuel: () => number
}

export class ProofMoveController {
  claim(sample: PointerSample): PointerClaim | null
  contextMenu(sample: PointerSample): boolean
  doubleClick(sample: PointerSample): boolean
  keyDown(sample: KeySample): boolean
  overlay(): readonly Shape[]
  cancel(): void
  dispose(): void
}
```

- [ ] Add failing pure/controller-adjacent tests for Delete step dispatch, Shift purity, stationary selected-node release returning selection behavior, movement threshold entering iteration, invalid target refusal, and quick-normalization step dispatch. Use minimal fake host only where DOM is not required; browser presentation is Task 4.

- [ ] Run `npm test -- tests/app/moves.test.ts` and verify the new tests RED.

- [ ] Implement pointer claim state for selected-node drag iteration. Legal target overlays use `theme.interaction.valid`; occurrence-cycle overlays use a distinct transient candidate color. `claim` returns null outside proof mode, with Shift/Ctrl, or without an iterable selected node.

- [ ] Implement `keyDown`: Delete/Backspace emits `contextualDeleteStep`; W emits `doubleCutIntro`; Shift+W opens a pointer-local arity prompt; Tab/Enter/Escape control citation ambiguity. No handler emits success feedback.

- [ ] Implement `doubleClick`: a term node tries weak-head normalization, then head normalization, and refuses a no-op beside `sample.client`.

- [ ] Implement a controller-owned right-click palette. It lists legal parameterized/direct actions, filtered citations, and closed theorems. Unique citation applies immediately; ambiguous citation stores candidates and highlights the current occurrence. Instantiation rows use `foldedComprehension`; folding uses `inferFoldArgs`; unfolding is immediate. Custom conversion uses `applyConversion` and the controller prompt.

- [ ] Centralize cleanup so `cancel` and `dispose` remove palette/prompt and clear drag/cycle state. Refused menu actions keep the relevant menu/prompt available; successful actions close and clear selection.

- [ ] Run `npm test -- tests/app/moves.test.ts tests/app/cite.test.ts` and `npm run typecheck`; verify GREEN before shell wiring.

---

### Task 4: Replace shell proof paths and prove behavior in the actual app

**Files:**
- Modify: `src/app/shell.ts`
- Modify: `e2e/app.spec.ts`
- Modify: `tests/architecture/interaction-ownership.test.ts`

- [ ] Write failing architecture assertions that production source contains none of `type BackwardEntry`, `backwardEntries`, `commitBackward`, pending kinds `cite`, `unCite`, or click-target `iterate`, and that `src/app/shell.ts` instantiates `ProofMoveController` exactly once.

- [ ] Write failing Playwright cases proving: selection alone leaves the proof menu hidden; explicit right-click opens beside the pointer; forward and backward show the same direct vocabulary without `Un-` labels; Delete commits contextually; double-click normalizes; dragging a selected node shows legal green targets and emits iteration; citation never asks for wires; folded instantiation leaves a ref node; refusal text appears beside the attempted pointer; Escape cancels palette/cycle.

- [ ] Run the focused architecture and Playwright cases and verify RED for the obsolete shell behavior.

- [ ] In `src/app/shell.ts`, instantiate one `ProofMoveController` after `ConstructController`. Its sink calls existing `applyProofStep`; getters return `currentDiagram`, current selection/context/orientation/theme/fuel; refusal forwards the provided pointer.

- [ ] Route viewport hooks by mode:

```ts
claim: (sample) => mode === 'prove' ? proofMoves.claim(sample) : construct.claim(sample),
doubleClick: (sample) => mode === 'prove' ? proofMoves.doubleClick(sample) : construct.doubleClick(sample),
contextMenu: (sample) => {
  if (mode === 'prove') { proofMoves.contextMenu(sample); return }
  // retain existing EDIT palette behavior
},
keyDown: (sample) => proofMoves.keyDown(sample) || onKeyDown(sample),
```

Append `proofMoves.overlay()` in the frame. Call `proofMoves.cancel()` during sync/mode exit and `dispose()` during shell teardown.

- [ ] Delete `BackwardEntry`, `backwardEntries`, `commitBackward`, proof branches of `commitAction`, proof-only `Pending` variants, manual wire-click routing, and proof palette rendering from the shell. Retain only edit relation-definition/fold pending UI until its own integration stage.

- [ ] Run `npm test -- tests/app/moves.test.ts tests/app/cite.test.ts tests/app/actions.test.ts tests/architecture/interaction-ownership.test.ts`, `npm run typecheck`, and the focused new Playwright cases. Repair only root-cause failures and rerun.

- [ ] Run the complete affected app browser file: `npx playwright test e2e/app.spec.ts`. Do not run physics-heavy suites.

- [ ] Commit:

```bash
git add src/app/interact/moves.ts src/app/interact/cite.ts tests/app/moves.test.ts tests/app/cite.test.ts src/app/shell.ts e2e/app.spec.ts tests/architecture/interaction-ownership.test.ts
git commit -m "feat: integrate shared proving interactions"
```

---

### Task 5: Completion receipt and final verification

**Files:**
- Modify: `docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md`
- Modify: `/tmp/vpa-prove-interaction-integration-foundation-20260710.md` (scratch only)

- [ ] Replace Task 3's open checkbox with a factual receipt naming the deleted parallel paths and fresh validation counts. Do not mark Task 4 or later complete.

- [ ] Run fresh final validation in separate commands so Playwright's two web servers cannot race a preceding command:

```bash
git diff --check
npm test -- tests/app/moves.test.ts tests/app/cite.test.ts tests/app/actions.test.ts tests/architecture/interaction-ownership.test.ts
npm run typecheck
npx playwright test e2e/app.spec.ts
```

- [ ] Append `<conformance>` to the foundation record with owners, removed structures, migrated dependents, exact counts, and confirmation that no physics source/test was touched.

- [ ] Commit the receipt and verify clean main:

```bash
git add docs/superpowers/plans/2026-07-04-plan-20-interaction-integration.md
git commit -m "docs: close proving interaction integration"
git status --short
git log -5 --oneline
```
