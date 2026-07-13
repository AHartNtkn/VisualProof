# Central lens Task 5 report

## Outcome

Replaced the proof-assistant browser product with one Cursebreaker entry rooted at `main#cursebreaker`. The opening `two-veils` seal now mounts inside the approved central-lens composition, retains `ProofFrontViewport` as the sole proof interaction authority, and uses the Task 4 physical lever for timeline movement.

## Foundation

`/tmp/central-lens-task5-foundation-20260712T190000Z.md`

The first-principles comparison selected the existing game domain, backward viewport, lens layout, and timeline lever for reuse because their responsibilities match the desired model. It selected a complete replacement of the assistant browser entry, document roots, chrome stylesheet, and product-startup theory hooks.

## TDD evidence

The product-surface architecture test was created before production changes and run in RED. It failed at the intended assertion because `app/main.ts` still imported and mounted `mountShell`. After the entry replacement it passed.

## Implemented ownership

- `mountCursebreaker` owns the catalog, local progress/session, runtime authority, viewport lifecycle, layout, resize, animation, refusal presentation, lever integration, and disposal.
- `ProofFrontViewport` remains the sole proof-input owner and is configured only for the backward side, with an empty boundary, catalog relation context, empty theorem map, `DARK`, and fuel 256.
- `applyGameStep` evaluates during `prepare`; the returned session becomes authoritative only in the motion commit closure. Completion is recorded once before viewport reconciliation and lever refresh.
- Ctrl/Cmd+Z and Ctrl/Cmd+Shift+Z request `moveCursor`; no undo/redo buttons exist.
- Only glass `ResizeObserver` bounds reach `ProofFrontViewport.resize`; window resize only reapplies `lensLayout` to the stage.
- Generated shadow, optics, frame, lever-housing, and lever-handle assets are decorative and do not own pointer input.
- Refusals remain temporary, red, pointer-adjacent `role=alert` outputs with no misconception metadata or invalid-move policy changes.
- The returned debug seam exposes puzzle id, timeline cursor/count, completed ids, lens and glass rectangles, and viewport debug state.

## Displaced surface

The game entry no longer contains the assistant shell mount, separate canvas/chrome roots, assistant product title, assistant chrome CSS, or `preapp`/`pree2e` theory-emission hooks. `emit:theories` remains available only as an explicit development utility.

## Validation

- RED: `npx vitest run tests/architecture/game-product-surface.test.ts` — failed because `mountCursebreaker` was absent and `mountShell` remained.
- GREEN focused suite: 6 files, 27 tests passed.
- `npm run typecheck` — passed.
- `npx vite build app --logLevel error` — passed; all five central-lens PNG roles were emitted.
- Physics tests were intentionally not run because physics did not change.

## Self-review

The implementation stays within the Task 5 surface. It does not copy assistant shell state, add a second product path, alter proof/move/physics semantics, introduce controls over the lens, or bypass the Task 4 lever and existing timeline authority. The browser entry has one host and one product owner; decorative images are non-interactive and hidden from assistive technology; disposal releases every owned observer, listener, animation request, temporary refusal, lever, viewport, and DOM stage.
