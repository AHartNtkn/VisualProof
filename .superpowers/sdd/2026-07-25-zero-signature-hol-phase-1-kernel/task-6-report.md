# Task 6 report: zero-signature app migration

Status: complete

## Outcome

The app interaction layer now owns one structural model over `atom`, `ref`, and
`identity` nodes. Construction and proof actions expose identity insertion and
exact structural identity contradiction; proof copy delegates to ordinary
iteration; edit copy delegates to extract/splice; definition matching is exact
graph matching; spawn, proof-spawn, motion, proof fronts, and shell no longer own
term entry, conversion, fission, comprehension, or relation-workspace state.

`tests/fixtures/zero-signature.ts` is the generic fixture authority for `UNARY`,
`BINARY`, `unaryDefinition`, `identityInCut`, and `tinyTheory`. Surviving generic
boot, library, persistence, session, history, replay, and companion tests use that
authority.

Pure selection, proof-front policy, and shell-label modules isolate headless app
policy from the downstream view runtime while preserving the existing public
re-exports.

## Removed ownership

All task-named application, interaction, workspace harness, E2E, and dedicated
test paths are absent:

- abstraction matching and tactics
- relation transactions, workspace, and workspace draft
- closed-term introduction, comprehension macros, and fission
- named-relation interaction
- relation-workspace browser harness
- abstraction and relation-workspace E2E specs
- dedicated tests for every removed responsibility

The relation-workspace CSS selectors and stale Vite build input were also removed.
A source scan over `src/app`, `src/interaction`, `app/style.css`, and
`e2e/vite.config.ts` found zero prohibited computation/comprehension/workspace
terms.

## Validation

RED evidence before implementation:

- `tests/app/edit.test.ts`: three failures because `addIdentity` did not exist.
- `tests/app/actions.test.ts`: collection failed because the old action layer
  still imported deleted inconsistent-cut ownership.

Focused GREEN:

- `npx vitest run tests/app/actions.test.ts tests/app/edit.test.ts`
- 2 files passed, 14 tests passed.

Authoritative Task 6 gate:

- `npx vitest run tests/app tests/interaction tests/architecture`
- 33 files passed, 90 tests passed.

Scoped compiler audit:

- `src/app`: 0 diagnostics.
- surviving `tests/app`: 0 diagnostics.
- surviving `tests/interaction`: 0 diagnostics.
- `tests/architecture`: 0 diagnostics.

Additional checks:

- `git diff --check`: passed.
- prohibited source scan: 0 hits.
- task-named removed paths still present: 0.

## Downstream TypeScript diagnostics

The full repository TypeScript run remains nonzero solely outside Task 6:
339 diagnostics total, partitioned exactly as follows:

- `src/view`: 23
- `src/theories`: 163
- `tests/view`: 33
- `tests/physics`: 86
- `tests/theories`: 34
- all other paths: 0

Exact file counts:

| File | Diagnostics |
| --- | ---: |
| `src/theories/frege.ts` | 123 |
| `src/theories/lambda.ts` | 15 |
| `src/theories/macros.ts` | 25 |
| `src/view/bend.ts` | 1 |
| `src/view/engine.ts` | 11 |
| `src/view/paint.ts` | 5 |
| `src/view/tromp.ts` | 6 |
| `tests/physics/cut-containment.test.ts` | 5 |
| `tests/physics/define-render.test.ts` | 4 |
| `tests/physics/drag-clamp.test.ts` | 7 |
| `tests/physics/hittest.test.ts` | 9 |
| `tests/physics/paint.test.ts` | 20 |
| `tests/physics/pipeline.test.ts` | 3 |
| `tests/physics/relax.test.ts` | 26 |
| `tests/physics/stub-scope.test.ts` | 9 |
| `tests/physics/wires.test.ts` | 3 |
| `tests/theories/battery.test.ts` | 11 |
| `tests/theories/frege.test.ts` | 8 |
| `tests/theories/lambda.test.ts` | 3 |
| `tests/theories/macros.test.ts` | 12 |
| `tests/view/bend.test.ts` | 1 |
| `tests/view/drag-clamp.test.ts` | 5 |
| `tests/view/engine.test.ts` | 6 |
| `tests/view/mec.test.ts` | 2 |
| `tests/view/morph.test.ts` | 1 |
| `tests/view/stub-scope.test.ts` | 13 |
| `tests/view/tromp.test.ts` | 1 |
| `tests/view/wires.test.ts` | 4 |

`tests/physics/cut-containment.test.ts` was an existing untracked user file and
was not changed or staged.

## Remaining concern

The surviving broader E2E specs still encode former term/comprehension workflows.
They were not part of the Task 6 gate or named deletion set and remain for the
later E2E/corpus migration. No Task 6 app source retains those paths.

## Fix round 1/5

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
