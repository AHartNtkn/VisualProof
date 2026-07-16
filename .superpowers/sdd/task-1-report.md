# Task 1 Report: Excavation Folio Demo Foundation

## Status

DONE_WITH_CONCERNS

## Commit

`9e0f63a` — `feat(review): establish excavation folio demo foundation`

## Files changed

- `review/excavation-folio/index.html`
- `review/excavation-folio/main.ts`
- `review/excavation-folio/model.ts`
- `review/excavation-folio/content.ts`
- `review/excavation-folio/base.css`
- `tests/review/excavation-folio-model.test.ts`
- `tsconfig.json`

The session-local first-principles evidence is recorded at
`/tmp/visual-proof-assistant-task-1-foundation-20260716.md`.

## Design decisions

- Established `model.ts` as the only authority for the closed review state,
  actions, transitions, artifact status projection, reset/Escape behavior, and
  keyboard-only review mapping.
- Kept the state model demonstration-specific rather than treating it as a
  future application API.
- Made progression selection deterministic: arrival selects the closed Seyric
  state; intermediate progressions select the open Seyric dossier; release
  selects the open Myratic dossier; every progression change dismisses
  inspection.
- Represented inaccessible inspection as an unchanged transition so later
  physical refusal motion can be triggered without admitting an invalid
  inspected state.
- Copied the seven required artifact records into a small immutable demo-only
  content projection with one evidence mount, professional name, accession
  line, and concise provenance/material summary per artifact.
- Projected culture, progression, cover, motion, inspected artifact, and Myratic
  restriction to deterministic root `data-*` attributes.
- Kept keyboard review controls invisible. Digits 1–5 select progression, M
  toggles full/reduced, P toggles paused/full, R resets, and Escape dismisses
  inspection.
- Reused the approved desk, substrate, gasket, timeline housing, and timeline
  handle only through asset URLs. No runtime application/domain imports exist.
- Limited CSS to the Task 1 composition foundation and explicit evidence
  placeholders; final folio artwork and authored motion remain for later tasks.
- Added `review` to the root TypeScript project so the standalone demo is
  checked under the repository's strict compiler contract.

## TDD and validation

1. RED:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: failed because `review/excavation-folio/model.ts` did not exist.

2. First GREEN attempt:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: exposed an incorrect test-relative import path.

   `npm run typecheck`

   Result: exposed the same import error plus strict nullable-root and unchecked
   string-index errors in the new browser entry.

3. Model GREEN:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: 19/19 tests passed.

   `npm run typecheck`

   Result: passed.

4. Keyboard mapping RED:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: 19 tests passed and the new keyboard mapping test failed because
   `reviewActionForKey` did not exist.

5. Final pre-commit verification:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: 20/20 tests passed.

   `npm run typecheck`

   Result: passed with exit code 0.

   `git diff --check`

   Result: passed with no whitespace errors.

   Prohibited import scan:

   `rg -n "from ['\"][^'\"]*src/(app|game|kernel|view)" review/excavation-folio`

   Result: no matches.

   Deterministic state projection scan confirmed all six root state attributes
   in `main.ts`.

## Self-review

- Scope matches Task 1: state, content projection, standalone composition, base
  styling, keyboard mappings, tests, and typecheck inclusion only.
- The status matrix displays every required physical status simultaneously in
  `seyric-practiced`.
- All required names and concise provenance/material summaries are present.
- Culture changes, progression changes, cover closure, reset, and Escape cannot
  leave stale inspection state.
- Inaccessible records cannot enter inspection state.
- The lens is pointer-inert and layered behind a bounded left workspace; the
  workspace width is calculated to end before the full-height lens aperture.
- No visible shortcut strip, help overlay, runtime import, persistence, proof
  behavior, source management, final asset work, or motion implementation was
  added.
- Only the seven listed Task 1 files were committed. Existing unrelated dirty
  files remain untouched.

## Concerns

- The approved desk and mechanical image files referenced by URL were already
  present as unrelated untracked work in this worktree. Per the task boundary,
  they were consumed but not staged or committed. The demo therefore requires
  the separate approved-asset work to be committed or otherwise retained.
- Task 1 validation did not include browser screenshot or motion evidence,
  because those belong to later asset/motion/capture tasks. Human visual review
  of the completed folio is consequently not claimed here.

## Review-finding correction

### Changes

- Replaced the hard 26rem folio minimum with a shared geometry contract:
  the 100vh lens owns its center and aperture-left edge, and the folio workspace
  ends at that aperture boundary with zero minimum width and clipped overflow.
  The lens now owns the higher layer, so folio content cannot cover it.
- Replaced the inaccessible disabled-card treatment with a record face covered
  by a dedicated `record-guard` / `restricted-sleeve` structure. The guard has
  a fold and custody band, while the covered record face is removed from the
  accessibility tree and the actionable record announces its sealed sleeve.
  No inaccessible opacity or `aria-disabled` treatment remains.
- Changed the instrument from 102vh to exactly 100vh.
- Added `motionPreference` as the durable full/reduced preference. Pausing now
  preserves it, unpausing restores it, and M while paused changes the preference
  that will be restored without leaving the paused state.

### TDD and validation

1. RED:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: failed with 8 intended regressions: missing durable motion
   preference behavior, missing physical guard structure, hard/overlaid folio
   geometry, and 102vh lens sizing. 17 existing tests passed.

2. GREEN:

   `npm test -- tests/review/excavation-folio-model.test.ts`

   Result: 25/25 tests passed.

3. Integration:

   `npm run typecheck`

   Result: passed with exit code 0.

   `git diff --check`

   Result: passed with no whitespace errors.

### Fix self-review

- The workspace and aperture use one CSS geometry authority; there is no
  competing folio minimum or folio-over-lens stacking path.
- Narrow viewports sacrifice folio workspace width rather than shrinking or
  covering the lens, matching the approved composition priority.
- Inaccessible records remain present and actionable for physical refusal, but
  useful content is physically covered instead of visually dimmed or disabled.
- The Task 1 placeholder establishes obstruction DOM/CSS grammar only; no Task
  2 authored folio artwork or motion was started.
- Full and reduced preferences both survive pause/unpause, and M while paused
  deterministically selects the resumed preference.
- Changes are limited to Task 1 implementation, its focused test, and this
  required report append. Existing unrelated worktree changes remain untouched.

### Remaining concerns

- Browser screenshot validation remains intentionally deferred to the later
  capture task; Task 1 now proves the spatial and obstruction contracts through
  focused structural tests and typechecking, not final visual quality.
