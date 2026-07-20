# Folio Puzzle Recognition and Input Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace folio lore images with cached canonical puzzle previews, add culture-local level numbers, add completion keyboard activation, and implement the approved select/deselect pointer contract.

**Architecture:** The folio projection carries culture-local ordinals and immutable worker-ready preview requests derived from canonical puzzle diagrams and logical fingerprints. A game-owned preview service coordinates a module worker, IndexedDB-derived PNG storage, and a bounded object-URL LRU; the folio owns visibility scheduling and presentation. Completion keyboard input remains in the runtime controller boundary, while the game-owned brush reducer receives explicit `select` or `deselect` modes and never uses proof-erasure vocabulary.

**Tech Stack:** TypeScript, framework-free DOM, Vite module workers, OffscreenCanvas, IndexedDB, Vitest, Playwright/Chromium.

## Global Constraints

- Work only in `/home/ahart/Documents/VisualProofAssistant/.worktrees/cursebreaker-domain` on `game/cursebreaker-domain`.
- Do not commit, merge, launch Electron, or run `test:physics`.
- Preserve puzzle content, proof physics, progression, saves, folio motion, theorem dragging, and approved styling except where this plan explicitly changes presentation.
- Preview dimensions are exactly 640×400, use the Dark Slate proof palette, fit the complete canonical starting diagram, and omit the proof frame shape.
- Level numbers are one-based and reset independently for each culture.
- Preview cache keys are `cursebreaker-thumbnail:<renderer-version>:<logical-fingerprint>:640x400`.
- Decoded object URLs are bounded to 24 entries and persistent PNG entries are bounded to 256.
- Plain click selects an unselected item and preserves a selected item.
- Shift-click deselects a selected item and leaves an unselected item unchanged.
- Plain drag selects crossed items; Shift-drag deselects crossed selected items.
- Selection gestures never mutate proof content. Do not rename, alias, or route selection through proof erasure.
- Enter and Space on an unobstructed completion screen dispatch the exact same `levelSelection` action as its only button.

---

## File Structure

- Create `src/game/interface/puzzle-preview-contract.ts`: worker-safe request/result types, dimensions, renderer version, and cache-key construction.
- Create `src/game/interface/puzzle-preview-renderer.ts`: deterministic canonical diagram rasterization onto OffscreenCanvas.
- Create `src/game/interface/puzzle-preview.worker.ts`: module-worker message boundary and failure reporting.
- Create `src/game/interface/puzzle-preview-cache.ts`: IndexedDB derived-cache adapter and bounded object-URL LRU.
- Create `src/game/interface/puzzle-preview-service.ts`: request deduplication, visible-request queueing, worker lifecycle, generation rejection, and subscription cancellation.
- Modify `src/game/interface/folio-projection.ts`: culture-local level numbers and canonical preview requests.
- Modify `src/game/interface/folio-view.ts`: consume preview service, schedule visible records, render readiness/error states, and reuse ready images in enlarged inspection/theorem lift.
- Modify `src/game/interface/folio.css`: replace mount/specimen styling with fitted Dark Slate preview styling and pointer-transparent hover/focus inspection.
- Modify `src/game/interface/loupe/interact/brush.ts`: explicit select/deselect brush vocabulary and transitions.
- Modify `src/game/interface/loupe/interact/viewport.ts`: carry Shift into brush begin/move/still-click resolution.
- Modify `src/game/interface/mount.ts`: completion Enter/Space routing.
- Modify `scripts/assets/production-interface-assets.ts` and `tests/assets/production-interface-assets.test.ts`: remove obsolete mount/specimen asset authority.
- Delete the three mount PNGs and three specimen PNGs displaced by canonical previews.
- Modify focused unit, DOM, and browser fixtures/tests listed in each task.

---

### Task 1: Canonical Preview Requests and Culture-Local Numbers

**Files:**
- Create: `src/game/interface/puzzle-preview-contract.ts`
- Modify: `src/game/interface/folio-projection.ts`
- Test: `tests/game/folio-projection.test.ts`
- Test: `tests/game/puzzle-preview-contract.test.ts`

**Interfaces:**
- Produces: `PuzzlePreviewRequest`, `PuzzlePreviewWorkerResult`, `PUZZLE_PREVIEW_WIDTH`, `PUZZLE_PREVIEW_HEIGHT`, `puzzlePreviewKey(fingerprint)`.
- Produces: `FolioRecordProjection.levelNumber: number` and `FolioRecordProjection.preview: PuzzlePreviewRequest`.

- [ ] **Step 1: Write failing projection and key tests**

Add assertions proving the first and last record numbers in each culture are `1` and `18`, that numbering resets in the second culture, that numbers do not change with completion state, and that every preview request contains `diagramToJson(catalog.puzzle(id).diagram)` with a key derived from `catalog.puzzleFingerprint(id)`.

```ts
expect(archive.cultures[0]!.records.map(({ levelNumber }) => levelNumber))
  .toEqual(Array.from({ length: 18 }, (_, index) => index + 1))
expect(archive.cultures[1]!.records[0]!.levelNumber).toBe(1)
expect(archive.cultures[0]!.records[0]!.preview).toEqual({
  key: puzzlePreviewKey(catalog.puzzleFingerprint(catalog.puzzleIds[0]!)),
  fingerprint: catalog.puzzleFingerprint(catalog.puzzleIds[0]!),
  diagram: diagramToJson(catalog.puzzle(catalog.puzzleIds[0]!).diagram),
  width: 640,
  height: 400,
})
```

- [ ] **Step 2: Run the tests and observe RED**

Run: `npm test -- tests/game/folio-projection.test.ts tests/game/puzzle-preview-contract.test.ts`

Expected: FAIL because `levelNumber`, `preview`, and `puzzlePreviewKey` do not exist.

- [ ] **Step 3: Implement the request contract and projection**

Use the following public contract:

```ts
export const PUZZLE_PREVIEW_WIDTH = 640
export const PUZZLE_PREVIEW_HEIGHT = 400
export const PUZZLE_PREVIEW_RENDERER_VERSION = 'dark-slate-v1'

export type PuzzlePreviewRequest = {
  readonly key: string
  readonly fingerprint: string
  readonly diagram: unknown
  readonly width: typeof PUZZLE_PREVIEW_WIDTH
  readonly height: typeof PUZZLE_PREVIEW_HEIGHT
}

export type PuzzlePreviewWorkerResult =
  | { readonly kind: 'ready'; readonly key: string; readonly generation: number; readonly blob: Blob }
  | { readonly kind: 'error'; readonly key: string; readonly generation: number; readonly message: string }

export const puzzlePreviewKey = (fingerprint: string): string =>
  `cursebreaker-thumbnail:${PUZZLE_PREVIEW_RENDERER_VERSION}:${fingerprint}:640x400`
```

In `projectFolio`, enumerate each culture's `puzzlesInCulture` result with `.map((id, index) => ...)`, set `levelNumber: index + 1`, and serialize the immutable catalog puzzle with `diagramToJson`.

- [ ] **Step 4: Run GREEN verification**

Run: `npm test -- tests/game/folio-projection.test.ts tests/game/puzzle-preview-contract.test.ts`

Expected: both files PASS.

---

### Task 2: Deterministic Worker Rendering and Bounded Derived Cache

**Files:**
- Create: `src/game/interface/puzzle-preview-renderer.ts`
- Create: `src/game/interface/puzzle-preview.worker.ts`
- Create: `src/game/interface/puzzle-preview-cache.ts`
- Create: `src/game/interface/puzzle-preview-service.ts`
- Test: `tests/game/puzzle-preview-renderer-browser.test.ts`
- Test: `tests/game/puzzle-preview-cache.test.ts`
- Test: `tests/game/puzzle-preview-service.test.ts`
- Create: `tests/game/puzzle-preview-renderer-fixture.html`
- Create: `tests/game/puzzle-preview-renderer-fixture.ts`

**Interfaces:**
- Consumes: `PuzzlePreviewRequest` and `PuzzlePreviewWorkerResult` from Task 1.
- Produces: `renderPuzzlePreview(request): Promise<Blob>`.
- Produces: `PuzzlePreviewCache` with `get`, `put`, and `dispose`.
- Produces: `PuzzlePreviewService.subscribe(request, listener): () => void` and `dispose()`.

- [ ] **Step 1: Write failing renderer browser tests**

Build a fixture that sends a small and deliberately wide diagram through the real module worker. Decode returned PNGs into canvases and assert 640×400 dimensions, opaque `DARK.canvas` corners, non-background diagram pixels inside all four bounds, no rendered frame border, deterministic equality for repeated requests, and an error result for malformed diagram JSON.

- [ ] **Step 2: Run the renderer test and observe RED**

Run: `npm test -- tests/game/puzzle-preview-renderer-browser.test.ts`

Expected: FAIL because the worker and renderer modules do not exist.

- [ ] **Step 3: Implement deterministic rasterization**

`renderPuzzlePreview` must:

```ts
const diagram = diagramFromJson(request.diagram)
const engine = mkEngine(diagram, [])
seedProject(engine)
for (let index = 0; index < 16; index += 1) settleStep(engine, null)
const canvas = new OffscreenCanvas(request.width, request.height)
const context = canvas.getContext('2d')
if (context === null) throw new Error('puzzle preview canvas has no 2d context')
context.fillStyle = DARK.canvas
context.fillRect(0, 0, request.width, request.height)
const view = fitCamera(
  engine.frame === null ? undefined : { center: engine.frame.center, radius: engine.frame.half },
  request.width,
  request.height,
  1,
)
drawShapes(context as unknown as CanvasRenderingContext2D,
  paint(engine, DARK).filter((shape) => shape.kind !== 'frame'), view)
return canvas.convertToBlob({ type: 'image/png' })
```

The worker must echo the request key and generation and convert thrown values to a stable error message. It must never retain puzzle content as authority.

- [ ] **Step 4: Run renderer GREEN verification**

Run: `npm test -- tests/game/puzzle-preview-renderer-browser.test.ts`

Expected: PASS.

- [ ] **Step 5: Write failing cache and orchestration tests**

Use injected fake `Worker`, object-URL functions, clock, and cache storage to prove:

- a persistent hit emits `ready` without worker work;
- concurrent subscribers for one key share one worker request;
- canceling the last queued subscriber prevents worker dispatch;
- stale generations are ignored after disposal;
- worker failures emit `error` without installing a URL;
- a 25th decoded entry revokes the least-recently-used URL;
- a 257th persistent entry removes the oldest IndexedDB entry;
- renderer-version/fingerprint changes create a cache miss.

- [ ] **Step 6: Run cache/service tests and observe RED**

Run: `npm test -- tests/game/puzzle-preview-cache.test.ts tests/game/puzzle-preview-service.test.ts`

Expected: FAIL because cache and service modules do not exist.

- [ ] **Step 7: Implement the cache and service**

Use these interfaces:

```ts
export type PuzzlePreviewState =
  | { readonly kind: 'preparing' }
  | { readonly kind: 'ready'; readonly url: string }
  | { readonly kind: 'error'; readonly message: string }

export type PuzzlePreviewService = {
  subscribe(request: PuzzlePreviewRequest, listener: (state: PuzzlePreviewState) => void): () => void
  dispose(): void
}
```

The IndexedDB database is `cursebreaker-derived-previews`, version `1`, with object store `previews` keyed by `key` and values `{ key, blob, lastUsed }`. IndexedDB unavailability falls back to the bounded in-memory cache only; no localStorage or checked-in PNG path is allowed. Maintain exactly one active worker render, a FIFO of subscriber-backed requests, and a monotonically increasing generation rejected after disposal.

- [ ] **Step 8: Run cache/service GREEN verification**

Run: `npm test -- tests/game/puzzle-preview-cache.test.ts tests/game/puzzle-preview-service.test.ts`

Expected: both files PASS with object URLs revoked exactly once.

---

### Task 3: Replace Folio Image Authority and Add Enlarged Inspection

**Files:**
- Modify: `src/game/interface/folio-view.ts`
- Modify: `src/game/interface/folio.css`
- Modify: `src/game/interface/mount.ts`
- Modify: `tests/game/production-interface-dom.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`
- Modify: `tests/game/authoritative-runtime-fixture.ts`

**Interfaces:**
- Consumes: `FolioRecordProjection.levelNumber`, `.preview`, and `PuzzlePreviewService`.
- Produces: numbered record names, preview state DOM, visible-first subscriptions, and a pointer-transparent enlarged preview.

- [ ] **Step 1: Write failing DOM tests**

Inject a fake preview service through a new optional `FolioViewOptions.previewService` port. Assert:

```ts
expect(record.querySelector('.curse-folio-record-name')!.textContent).toBe('1. Completed')
expect(record.getAttribute('aria-label')).toContain('1. Completed')
expect(record.querySelector('.curse-folio-puzzle-preview-status')!.textContent)
  .toBe('Preparing preview…')
fakePreview.ready(COMPLETED, 'blob:completed')
expect(record.querySelector('.curse-folio-puzzle-preview')!.getAttribute('src'))
  .toBe('blob:completed')
```

Also assert that `Preview unavailable` appears on error, the enlarged image carries `aria-hidden="true"`, and theorem-drag inspection reuses the same ready URL.

- [ ] **Step 2: Run DOM test and observe RED**

Run: `npm test -- tests/game/production-interface-dom.test.ts`

Expected: FAIL because the record remains unnumbered and specimen/mount DOM is still authoritative.

- [ ] **Step 3: Implement folio preview consumption**

Remove `RecordMount`, `mountSequence`, `mountFor`, and `specimenByPuzzle`. Render each evidence area as:

```html
<span class="curse-folio-puzzle-preview-frame" data-preview-state="preparing">
  <img class="curse-folio-puzzle-preview" alt="" aria-hidden="true">
  <span class="curse-folio-puzzle-preview-status">Preparing preview…</span>
  <span class="curse-folio-puzzle-preview-inspection" aria-hidden="true">
    <img alt="">
  </span>
</span>
```

Use `IntersectionObserver` rooted at the scrolling sheet with a one-record root margin. Subscribe only observed records; when no observer exists (fake DOM), subscribe immediately. Cancel subscriptions and observer registrations before record replacement and disposal. Preserve ready/error state by preview key across projection updates. Name text is `${record.levelNumber}. ${record.name}` and every record's accessible label starts with that same string before status text.

- [ ] **Step 4: Replace CSS without changing folio geometry**

Keep `.record-face` row sizing and status/guard/priority/clearance layers. Replace mount backgrounds and `.specimen-image` with a Dark Slate frame, `object-fit: contain`, centered preview, nonblocking readiness copy, and an enlarged fixed/absolute inspection shown by `.artifact-record:hover` and `.artifact-record:focus-visible`. The inspection must be `pointer-events: none`, stay within the viewport with CSS clamping, and be disabled while `.is-inspection-source` theorem dragging owns the lifted record.

- [ ] **Step 5: Run DOM GREEN verification**

Run: `npm test -- tests/game/production-interface-dom.test.ts`

Expected: PASS with existing folio motion and theorem drag assertions unchanged.

- [ ] **Step 6: Write and run rendered folio tests RED then GREEN**

Extend the real Chromium fixture to expose preview readiness. Assert that the first six visible records receive 640×400 PNG URLs before offscreen records, scrolling schedules later records, switching cultures restores scroll and schedules that culture independently, names are numbered per culture, hover/focus shows a larger preview without intercepting pointer input, and a large diagram remains fully framed.

Run before integration: `npm test -- tests/game/authoritative-runtime-browser.test.ts`

Expected RED: no numbered names or real puzzle preview state.

Run after integration: `npm test -- tests/game/authoritative-runtime-browser.test.ts`

Expected GREEN: all authoritative runtime browser tests PASS.

---

### Task 4: Rebuild Game Selection Around Explicit Select/Deselect Modes

**Files:**
- Modify: `src/game/interface/loupe/interact/brush.ts`
- Modify: `src/game/interface/loupe/interact/viewport.ts`
- Create: `tests/game/brush.test.ts`
- Modify: `tests/game/game-proof-surface-fixture.ts`
- Modify: `tests/game/game-proof-surface-browser.test.ts`
- Modify: `tests/game/game-proof-surface-source.test.ts`

**Interfaces:**
- Produces: `BrushMode = 'select' | 'deselect'`.
- Changes: `BrushEvent.begin` to `{ kind: 'begin'; hit: Hit | null; mode: BrushMode }`.
- Preserves: `choosePointerPhase` Shift precedence and ordinary iteration claim ownership.

- [ ] **Step 1: Write failing game brush tests**

Move the behavior authority into a new game test importing the game-owned reducer. Cover this complete table:

```ts
expect(click([], nodeA, 'select')).toEqual([nodeA])
expect(click([nodeA], nodeA, 'select')).toEqual([nodeA])
expect(click([], nodeA, 'deselect')).toEqual([])
expect(click([nodeA], nodeA, 'deselect')).toEqual([])
expect(drag([nodeA], [nodeB, wire], 'select')).toEqual([nodeA, nodeB, wire])
expect(drag([nodeA, wire], [nodeA, nodeB, wire], 'deselect')).toEqual([])
```

Also assert still background click clears all, void-start ordinary drag selects encountered hits, and no game brush source or public type contains an `erase` property or mode.

- [ ] **Step 2: Run brush test and observe RED**

Run: `npm test -- tests/game/brush.test.ts`

Expected: FAIL because `BrushMode` and explicit begin mode do not exist and ordinary selected hits are removed.

- [ ] **Step 3: Implement the pure reducer**

Use selection-specific names:

```ts
export type BrushMode = 'select' | 'deselect'
export type BrushStroke = {
  readonly mode: BrushMode
  readonly fromVoid: boolean
  readonly touched: boolean
}

function applyBrush(selected: readonly Hit[], hit: Hit | null, mode: BrushMode): readonly Hit[] {
  if (hit === null) return selected
  const present = isHitSelected(selected, hit)
  if (mode === 'deselect') {
    return present ? selected.filter((candidate) => !sameHit(candidate, hit)) : selected
  }
  return present ? selected : [...selected, hit]
}
```

`begin` applies only the requested mode. `move` retains that mode. `end` clears selection only when the stroke began in void and touched no semantic hit.

- [ ] **Step 4: Run brush GREEN verification**

Run: `npm test -- tests/game/brush.test.ts`

Expected: PASS.

- [ ] **Step 5: Write failing real-pointer browser tests**

Expose stable client points for at least two proof hits and the proof background. In Chromium assert:

- click selected hit twice leaves it selected;
- Shift-click selected hit deselects it;
- Shift-click unselected hit leaves it unselected;
- ordinary drag adds crossed hits;
- Shift-drag removes crossed selected hits and leaves unselected hits unchanged;
- background click clears all;
- ordinary iteration drag from a selected iterable source still prepares the iteration move.

- [ ] **Step 6: Run pointer tests and observe RED**

Run: `npm test -- tests/game/game-proof-surface-browser.test.ts`

Expected: FAIL on ordinary selected-hit preservation and explicit Shift behavior.

- [ ] **Step 7: Route explicit modes through the viewport**

At pointer down compute `const brushMode: BrushMode = event.shiftKey ? 'deselect' : 'select'`, store it on `ActivePointer`, and pass it to every reducer `begin`, including the moving-start reconstruction. `#commitStillSelection` always uses `select` for an unmodified claimed still release. Shift remains selection phase and therefore cannot become an iteration/construction claim.

- [ ] **Step 8: Run pointer GREEN verification**

Run: `npm test -- tests/game/brush.test.ts tests/game/game-proof-surface-browser.test.ts tests/game/game-proof-surface-source.test.ts`

Expected: all files PASS; source test confirms the game brush has no selection field or mode named `erase`.

---

### Task 5: Completion Enter and Space Activation

**Files:**
- Modify: `src/game/interface/mount.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`

**Interfaces:**
- Consumes: existing `dispatch({ kind: 'levelSelection' })` controller route.
- Produces: unmodified Enter/Space completion keyboard equivalence.

- [ ] **Step 1: Write failing completion keyboard tests**

For separate fresh completion fixtures, press Enter and Space and assert mode becomes `archive`, the folio remains mounted, and the save write matches the button path. Also assert modified keys, repeat events, and keys while pause/settings is topmost do not dismiss completion.

- [ ] **Step 2: Run the focused browser test and observe RED**

Run: `npm test -- tests/game/authoritative-runtime-browser.test.ts -t "completion"`

Expected: FAIL because Enter and Space leave completion open.

- [ ] **Step 3: Implement runtime key routing**

After editable-target and topmost-transient handling but before puzzle-only undo handling, add:

```ts
if (this.#state.mode === 'completion'
  && this.#state.transient === null
  && !event.altKey && !event.ctrlKey && !event.metaKey && !event.shiftKey
  && (event.key === 'Enter' || event.key === ' ')) {
  event.preventDefault()
  this.dispatch({ kind: 'levelSelection' })
  return
}
```

Use the existing repeat guard; do not synthesize a click or add a second controller path.

- [ ] **Step 4: Run completion GREEN verification**

Run: `npm test -- tests/game/authoritative-runtime-browser.test.ts -t "completion"`

Expected: PASS for button, Enter, and Space paths.

---

### Task 6: Delete Displaced Assets and Validate the Complete System

**Files:**
- Modify: `scripts/assets/production-interface-assets.ts`
- Modify: `tests/assets/production-interface-assets.test.ts`
- Modify: `tests/game/production-interface-dom.test.ts`
- Delete: `assets/interface/generated/excavation-folio/mount-photo.png`
- Delete: `assets/interface/generated/excavation-folio/mount-rubbing.png`
- Delete: `assets/interface/generated/excavation-folio/mount-tracing.png`
- Delete: `assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png`
- Delete: `assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png`
- Delete: `assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png`
- Modify: `/tmp/cursebreaker-interface-recognition-input-foundation-v4-20260719.md`

**Interfaces:**
- Removes: obsolete folio image authority and asset validation entries.
- Produces: direct conformance evidence in the active foundation record.

- [ ] **Step 1: Write failing absence/consumption assertions**

Change expected production asset paths to exclude the six displaced PNGs. Assert `folio-view.ts` has no `specimenByPuzzle`, `RecordMount`, or specimen asset URL; `folio.css` has no mount PNG URL; and the runtime DOM has canonical preview frames instead of `data-mount` or `.specimen-image` consumers.

- [ ] **Step 2: Run asset tests and observe RED**

Run: `npm test -- tests/assets/production-interface-assets.test.ts tests/game/production-interface-dom.test.ts`

Expected: FAIL while production manifests and runtime consumers retain the obsolete assets.

- [ ] **Step 3: Remove consumers, manifest entries, and the six files**

Use explicit file paths only. Do not touch other deleted or modified assets in the dirty worktree. Confirm `git status --short -- <six paths>` reports exactly those deletions.

- [ ] **Step 4: Run focused validation**

Run:

```bash
npm test -- tests/game/puzzle-preview-contract.test.ts tests/game/puzzle-preview-cache.test.ts tests/game/puzzle-preview-service.test.ts tests/game/puzzle-preview-renderer-browser.test.ts tests/game/folio-projection.test.ts tests/game/production-interface-dom.test.ts tests/game/game-proof-surface-browser.test.ts tests/game/game-proof-surface-source.test.ts tests/game/authoritative-runtime-browser.test.ts tests/assets/production-interface-assets.test.ts
npm run assets:validate
npm run typecheck
npm run build:renderer
```

Expected: every command exits 0. Do not run `npm run app`, Electron, packaging, or the physics battery.

- [ ] **Step 5: Run broad non-physics regression validation**

Run: `npm test`

Expected: all configured non-physics tests PASS with zero failures.

- [ ] **Step 6: Check displaced authority and diff scope**

Run:

```bash
rg -n "specimenByPuzzle|RecordMount|mount-photo|mount-rubbing|mount-tracing|auten-reliquary|seyric-field-seal|uninscribed-votive|readonly erase|stroke\.erase" src/game scripts/assets tests/assets tests/game
git diff --check
git status --short
```

Expected: `rg` finds no displaced runtime/test authority, `git diff --check` exits 0, and status contains only the pre-existing dirty work plus this plan's scoped additions/modifications/deletions.

- [ ] **Step 7: Append foundation conformance**

Append `<conformance>` to `/tmp/cursebreaker-interface-recognition-input-foundation-v4-20260719.md` without modifying its pre-action sections. Record preview ownership, worker/cache structures, numbering, keyboard routing, select/deselect structures, deleted assets, migrated dependents, exact validation commands, and proof that obsolete image authority and selection-erasure vocabulary are absent.

---

## Self-Review

- Spec coverage: canonical previews, future large diagrams, background worker, persistent/bounded cache, enlarged inspection, culture-local numbering, completion keyboard equivalence, exact selection contract, obsolete asset deletion, and authoritative validation each have an owning task.
- Placeholder scan: no `TBD`, `TODO`, deferred error handling, or content-free implementation step remains.
- Type consistency: Tasks 1–3 consistently use `PuzzlePreviewRequest`; Tasks 2–3 consistently use `PuzzlePreviewService.subscribe`; Task 4 consistently uses `BrushMode = 'select' | 'deselect'` and explicit `begin.mode`.
- Scope check: the preview pipeline, folio consumption, selection reducer, and completion route are separately testable tasks but remain one plan because the approved interface change requires one integrated release and one obsolete-asset migration.
