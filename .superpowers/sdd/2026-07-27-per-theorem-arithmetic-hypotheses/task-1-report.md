# Task 1 report: local arithmetic statement contracts

## Outcome

Replaced the blanket arithmetic statement authority with explicit, exported
per-theorem primitive and hypothesis contracts. Statement construction now
declares and draws only each theorem's ordered contract entries.

## TDD evidence

Before implementation, the independently hard-coded contract tests failed in 9
of 10 cases: their errors exposed the previous fixed three-primitive and
seven-hypothesis bundle. After reconstruction, the focused statement suite
passes all 10 tests.

## Validation

- `npx vitest run tests/theories/frege-statements.test.ts` — passed (10 tests).
- `npm run typecheck` — intentional Tasks 1–4 migration barrier. The two
  remaining import errors are `arithmetic-assoc-base.ts` importing removed
  `drawStandingHypotheses`, and `arithmetic-assoc-carrier.ts` importing removed
  `drawStandingHypotheses` plus `PrimitiveRelations`; their Task 2–4
  reconstruction restores green typechecking without compatibility exports.

## Scope

Only Task 1 source, tests, and plan documentation were changed. `archive/` and
`scratchpad/` remain unmodified and unstaged.
