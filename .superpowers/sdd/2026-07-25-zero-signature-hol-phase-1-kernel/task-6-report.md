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
