# Task 6 fix round 1 report

Status: complete

## Review findings resolved

1. Exact identity contradiction is now one kernel-owned structural predicate.
   The disequality child must contain only the matching identity: no descendant
   region, unrelated node, or child-scoped wire is accepted. The app enumerator
   uses the same kernel finder, and the applier rechecks the exact premise before
   surgery.
2. Backward proof orientation no longer turns physical negative-region content
   into an erasure candidate. Backward orientation changes citation direction;
   structural polarity gates remain physical.
3. Definition authoring has one boundary authority: canonical graph order.
   Manual wire-pick ordering and its shell interaction were removed. Fold
   inference now compares the exact selected region, direct regions, nodes, and
   wires against the occurrence selection.
4. Edit wire joining validates every input wire signature before constructing a
   merged wire. Heterogeneous endpoint-free wires are refused without modifying
   the source diagram.
5. The copy drag controller retains planner refusals and surfaces an
   outside-descendant-cone refusal on release instead of silently converting it
   into no action. View-dependent copy preview geometry moved to
   `copy-view.ts`, keeping the controller directly testable.
6. Executable browser scenarios and selectors for fission, the relation
   workspace, conversion preferences, term entry, and `closedTermIntro` were
   removed from `e2e/app.spec.ts` and `e2e/contextual-copy.spec.ts`. Three
   coherent generic structural workspace/chrome scenarios remain. No theory
   corpus loading was introduced.

## Direct regression coverage

- `tests/kernel/rules/identity.test.ts`: node, region, and wire near misses are
  refused and the source diagram is preserved.
- `tests/app/actions.test.ts`: the near miss is not offered as an identity
  contradiction, and backward negative content is not offered erasure.
- `tests/app/define.test.ts`: canonical-only authoring and exact region/wire
  selection matching.
- `tests/app/edit.test.ts`: heterogeneous endpoint-free wire join refusal and
  source preservation.
- `tests/app/copy-interaction.test.ts`: controller-level outside-cone refusal
  feedback with no commit.

## Validation

Focused combined gate:

- `npx vitest run tests/app/actions.test.ts tests/app/connection.test.ts tests/app/copy-interaction.test.ts tests/app/copy-planner.test.ts tests/app/define.test.ts tests/app/edit.test.ts tests/app/feedback.test.ts tests/kernel/rules/identity.test.ts`
- 8 files passed, 57 tests passed.

Full app gate:

- `npx vitest run tests/app tests/interaction tests/architecture`
- 33 files passed, 96 tests passed.

Browser specification collection:

- `npx playwright test e2e/app.spec.ts e2e/contextual-copy.spec.ts --list`
- 3 tests collected from 2 files.

Retired-workflow scan:

- Case-insensitive scan of both amended E2E files for fission, relation
  workspace, conversion/preference controls, term workflows, and
  `closedTermIntro`.
- 0 hits.

Compiler and hygiene:

- Scoped TypeScript audit over every amended source, direct regression test, and
  E2E specification: 0 diagnostics.
- `git diff --check`: passed.

## External validation blocker

Running the three browser scenarios is blocked before Playwright can start the
web server: the existing `src/view/tromp.ts` still imports the removed
`../kernel/term/term` module, so the Vite build fails during module resolution.
This downstream view migration is outside Task 6 fix round 1. The full repository
TypeScript command remains nonzero for the same already-recorded downstream view,
theory, and physics/test migrations; no amended file emits a diagnostic.

The existing untracked scratchpads and
`tests/physics/cut-containment.test.ts` were not changed or staged.
