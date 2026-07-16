# Task 3 report: physical folio interactions and animation choreography

## Status

Implemented and validated.

Implementation commit: `f237ff3` (`feat(review): choreograph physical folio motion`)

Foundation record: `/tmp/visual-proof-assistant-task3-foundation-20260716.md`

## Implemented scope

- Added one interruptible motion coordinator with independent cover, dossier, record, restriction, and packet channels.
- Rebuilt the folio render boundary so the cover, stacked dossier layers, tabs, inspection stage, and packet mechanics persist across state changes.
- Added hinged cover release/travel/settle phases.
- Added stacked-paper dossier release/travel/compression/settle and attached-tab lag.
- Added record corner release, lift, travel, inspection settle, controlled return, lowering, and remounting with height-dependent shadows.
- Added targeted restricted-sleeve pull/resistance/rebound/settle without software feedback.
- Added ordered Myratic tie-unfasten, guard-open, contents-release, and packet-settle mechanics.
- Added reduced-motion depth/contrast substitutions and immediate paused settling.
- Preserved Task 1 model authority and Task 2 institutional assets, including the distinct guard leaf and physical restriction sleeve.

## TDD evidence

Red:

`npx vitest run tests/review/excavation-folio-motion.test.ts`

- Exit 1.
- Failed because `review/excavation-folio/motion.ts` did not exist.

Green:

`npx vitest run tests/review/excavation-folio-motion.test.ts --reporter=verbose`

- Exit 0.
- 1 file passed, 9 tests passed.
- Proved phase cleanup, interruption ownership, reduced substitution, paused settling, inaccessible refusal sequence, ordered packet release, and reset cleanup.

## Final automated validation

`npx vitest run tests/review/excavation-folio-assets.test.ts tests/review/excavation-folio-motion.test.ts tests/review/excavation-folio-model.test.ts`

- Exit 0.
- 3 files passed, 40 tests passed.
- Model: 25 passed.
- Motion: 9 passed.
- Assets/layout: 6 passed, including 1600x1000 folio composition.

`npm run typecheck`

- Exit 0.
- `tsc --noEmit` completed without diagnostics.

`npx vite build review/excavation-folio --base ./ --outDir /tmp/excavation-folio-task3-final --emptyOutDir --logLevel error`

- Exit 0.

## Browser motion inspection

Ran a headless Chromium probe against `/tmp/excavation-folio-task3-final/index.html` at 1600x1000 and sampled computed transforms/shadows during active phases.

Observed evidence:

- Cover hinge travel: 3D rotation matrix with approximately `-20px` hinge translation.
- Dossier travel: nonzero x/y/z translation and shadow increase to `rgba(26, 19, 15, 0.38) 11.52px 16px 19.2px`.
- Record lift: scaled/translated physical lift with shadow increased to roughly `19px 29px 40px`.
- Record return: lower scale/height and shadow reduced to roughly `13px 17px 21px`, followed by hidden settled inspection state.
- Restricted sleeve: selected sleeve alone showed nonzero translation/skew during resistance and cleaned its target class after settling.
- Packet opening: guard reached a 3D rotated, approximately `-245px` translated release position through ordered phases.
- Rapid Seyric→Myratic interruption settled with culture `myratic`, no dossier phase/target, and no active motion class.
- Reduced mode exposed `reduced-depth` while the dossier transform remained `none`, preserving the state change without large travel.

Focused browser commands used Playwright directly and did not add capture infrastructure.

## Self-review

- Corrected delegated record clicks after browser inspection showed accessible inspection was not entering the stage.
- Restored the authored `guard-leaf-layer` contract after the asset/layout suite caught its accidental displacement.
- Restricted refusal choreography to the selected sleeve instead of all inaccessible records.
- Confirmed new transient state is owned only by `FolioMotion`; persistent review state remains in Task 1's model.
- Confirmed stale channel cleanup cannot delete a replacement animation's phase or class.
- Confirmed no visible software error message, disabled-card behavior, button bounce, or dissolving packet shortcut was introduced.

## Concerns

- The file-URL browser probe reports missing runtime image URLs for HTML-authored specimen/lens sources because their existing `../../assets` paths are outside the temporary build directory. Motion CSS assets were bundled, motion sampling remained valid, and the authoritative asset/layout test separately loaded and decoded every specimen. No repository capture infrastructure was changed in this task.

## Review fixes

- Added a generation-owned integration boundary for asynchronous motion completions.
- Every dispatched state change now invalidates earlier completion callbacks before projecting the newer state.
- Inspection-return completion can no longer replay its captured state after progression, reset, motion-preference, or culture changes, including when `settleAll()` aborts the animation.
- Restriction markers are cleared at the dispatch boundary and replacement attempts receive new channel ownership, so an older refusal's `finally` callback cannot remove the newest marker.

Validation after the fixes:

- `npx vitest run tests/review/excavation-folio-motion.test.ts --reporter=verbose`
  - 14/14 tests passed, including four stale inspection-return cases and repeated inaccessible attempts.
- `npx vitest run tests/review/excavation-folio-assets.test.ts tests/review/excavation-folio-motion.test.ts tests/review/excavation-folio-model.test.ts`
  - 45/45 focused folio tests passed.
- `npm run typecheck`
  - Passed without diagnostics.
- `npx vite build review/excavation-folio --base ./ --outDir /tmp/excavation-folio-task3-fix --emptyOutDir --logLevel error`
  - Passed.
- `git diff --check`
  - Passed.
