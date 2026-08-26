# Task 14 report: end-to-end interaction and persistence coverage

## Outcome

Task 14 is complete. The application now has committed end-to-end evidence for
the full Lambda workflow and a normally serialized, loadable
`examples/lambda.json`.

No production behavior needed alteration: the complete Lambda proof surface was
already handled exhaustively by the pipeline, session, snapshot, serializer,
loader, replay, 2D interaction, and 3D scene paths. `scripts/emit-theories.ts`
therefore required no Lambda case.

## Files changed

- `examples/lambda.json`
  - verified backward proof from the empty sheet;
  - spawns `(\\x. x) a` as one nameless term with output/free unary caps;
  - records a checked `lambdaConversion` to normal form.
- `e2e/construction.spec.ts`
  - exercises the exact `Lambda expression` row and asserts the complete IOTA
    incidence structure produced by edit-mode spawning.
- `e2e/interaction.spec.ts`
  - exercises proof-mode Lambda spawning, painted-stroke double-click,
    undo/redo controls, declaration, normal serializer download, normal loader,
    structural action recovery, and replay.
- `e2e/view3.spec.ts`
  - loads the committed example, replays to the redex, enters 3D, and verifies
    Lambda hover and focus through real scene projection and GPU picking.
- `tests/app/pipeline.test.ts`
  - covers library rebuild, save/load, and Lambda replay.
- `tests/app/session.test.ts`
  - covers exact Lambda action history through undo/redo and declaration.
- `tests/app/proof-snapshot.test.ts`
  - covers Lambda step JSON, placements, nameless term content, and current
    structural diagram content.

## RED/GREEN evidence

- App-level assertions initially exposed an invalid test premise when a forward
  spawn targeted the positive root. After placing the forward fixture in a
  negative cut, all three Lambda assertions were immediately green against the
  existing implementation. No artificial product failure was introduced.
- First browser run: 18 tests, 16 passed and 2 failed.
  - The construction Lambda scenario passed immediately.
  - The interaction scenario reached spawn correctly; its first double-click
    coordinate was not on the painted carrier. The test now locates a candidate
    through the real 2D hit-test before exercising double-click.
  - The load/3D scenario failed with `ENOENT` for
    `examples/lambda.json`, the genuine missing Task 14 fixture.
- Focused interaction GREEN: 1 passed.
- Focused load/3D GREEN: 1 passed.
- Required browser GREEN: 18 passed.

## Serialization of the example

The example was produced from authoritative model values, not handwritten JSON:

1. build an empty `DiagramWithBoundary` with `DiagramBuilder`;
2. start a verified backward proof track;
3. apply `proofTermSpawnStep(parseTerm('(\\x. x) a'), root)` through
   `applyTrack`;
4. obtain the term node and apply `convertToNormal(...).step` through the same
   track;
5. declare and register `LambdaWorkflow`;
6. pass the context through `sessionTheory` and `theoryToJson`; and
7. pretty-print that serializer result as `examples/lambda.json`.

The stored term payload is canonical nameless syntax (`A(L(B(0)),F(0))` before
normalization and `F(0)` afterward).

## Exact validation

- `npx vitest run tests/app/pipeline.test.ts tests/app/session.test.ts tests/app/proof-snapshot.test.ts`
  - 3 files passed, 7 tests passed.
- `npx playwright test e2e/construction.spec.ts e2e/interaction.spec.ts e2e/view3.spec.ts`
  - 18 tests passed.
- `npm run typecheck`
  - passed (`tsc --noEmit`).
- `git diff --check`
  - passed with no output.

## Concerns and blockers

None. Browser startup emits the repository's existing `NO_COLOR`/`FORCE_COLOR`
warning; it does not affect application behavior or test results.
