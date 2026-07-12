# Opening Final Review Fix Report

## Status

DONE

Foundation authority: `/tmp/vpa-opening-final-review-foundation-20260712-001.md`.
Its pre-action sections were not changed and no conformance section was appended.

## Root cause and implementation

- Added `src/game/unlock.ts` as the single pure owner of the conjunction between
  culture `unlocksAfter` gates and puzzle `prerequisites`.
- Migrated runtime `isUnlocked` and catalog validation to
  `meetsUnlockConditions`.
- Added catalog fixed-point simulation from empty completion. It completes each
  currently available batch and rejects any remaining puzzles with their
  cultures named in the error.
- Added the exact alternating-edge deadlock regression and a valid staged
  cross-culture graph regression.
- Removed only `resolve-repeated-veils` from artifact 6's `assesses` list.
- Replaced both partial opening-culture assertions with complete exact records,
  including the approved historical summaries.

## RED evidence

Cross-graph regression was added before production changes.

```text
npm test -- tests/game/catalog.test.ts -t "rejects a deadlock formed jointly"
exit 1
1 failed, 23 skipped
AssertionError: expected [Function] to throw an error
```

This proved the incumbent catalog accepted the exact graph in which culture A
was open, gateway A required gateway B, culture B unlocked after gateway A, and
gateway B had no puzzle prerequisite.

The artifact-6 exact expectation was changed before its content record.

```text
npm test -- tests/game/opening-content.test.ts -t "pins approved learning roles"
exit 1
1 failed, 5 skipped
```

The diff showed the sole extra received assessment was
`resolve-repeated-veils`.

## GREEN evidence

Focused verification:

```text
npm test -- tests/game/catalog.test.ts tests/game/progress.test.ts
2 files passed; 30 tests passed; exit 0

npm test -- tests/game/catalog.test.ts tests/game/progress.test.ts tests/game/opening-content.test.ts
3 files passed; 36 tests passed; exit 0
```

Decisive non-physics verification:

```text
npx vitest run tests/game tests/architecture/game-boundary.test.ts tests/kernel/rules/doublecut.test.ts tests/kernel/rules/erasure.test.ts tests/kernel/rules/iteration.test.ts tests/kernel/rules/comprehension-instantiate.test.ts
13 files passed; 111 tests passed; exit 0

npm run typecheck
tsc --noEmit; exit 0
```

Integrity and scope verification:

```text
git diff --check
exit 0; no output

if git diff --name-only | rg -n '^(src/(app|view|theory)/|tests/(app|view|theory)/)|physics|wirephys|relax'; then exit 1; fi
exit 0; no output

if rg -n "CampaignId|CampaignDefinition|campaignId|campaigns|\.campaign\b" src/game tests/game; then exit 1; fi
exit 0; no output

if rg -n "MisconceptionCue|misconceptions|\.thought\b" src/game tests/game; then exit 1; fi
exit 0; no output

if git diff --name-only 6520bf8 | rg -n '^(src/view/|tests/view/)|physics|wirephys|relax'; then exit 1; fi
exit 0; no output
```

The shared-condition ownership scan found the full conjunction only in
`src/game/unlock.ts`; runtime and catalog both call it. The dedicated physics
battery was not run.

## Files

- `src/game/unlock.ts`
- `src/game/catalog.ts`
- `src/game/progress.ts`
- `src/game/content/opening.ts`
- `tests/game/catalog.test.ts`
- `tests/game/opening-content.test.ts`

## Commit

`d2173af` — `fix(game): reject combined unlock deadlocks`

## Concerns

None.
