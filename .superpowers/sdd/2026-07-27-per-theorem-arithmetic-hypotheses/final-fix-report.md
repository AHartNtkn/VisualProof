# Final review fix wave report

## Outcome

Completed the selected final-review replacement without changing Lean,
kernel/proof semantics, theorem behavior, generated theory data, replay,
interaction, or runtime application behavior.

Base commit: `89dc5c45de88b531556f96d2001e03dd14e71c85`.

## Exact changes

- Removed the unsupported `formal:tags` and `formal:check` package scripts.
- Deleted `scripts/check-lean-step-tags.mjs` and
  `scripts/check-formalization.mjs` after reference inspection established
  that package advertisement was their only supported caller.
- Corrected the `addRelationWire` comment so it describes the surviving
  relation-wire representation and no longer claims that a body node witnesses
  the wire.
- Removed only the unused test-local `ProvenanceBranch.origins` field and its
  constructor/clone plumbing. Selection keys, proof traces, provenance
  decisions, certificates, receipts, meeting checks, and negative regressions
  remain intact.

## RED evidence

The pre-change repository search found:

- `package.json` advertising both unsupported formal commands;
- `scripts/check-formalization.mjs` calling `formal:tags` and the deleted
  `tests/kernel/formal/correspondence.test.ts`;
- `src/app/edit.ts` claiming a body node witnesses a relational wire;
- `tests/theories/frege.test.ts` declaring, constructing, and cloning the
  otherwise unread `origins` set.

Repository-wide script-reference inspection, excluding the forbidden
`archive/` and `scratchpad/` trees, found no independent supported caller.
Remaining mentions were historical design/plan records. The architecture
vocabulary test retains a negative absence assertion for the already deleted
correspondence test; it is not a caller.

The unchanged focused baseline passed before implementation:

```text
npx vitest run --config vitest.config.ts tests/architecture tests/app/edit.test.ts tests/theories/frege.test.ts
6 files passed; 55 tests passed
```

## GREEN evidence

Supported-authority searches after implementation found no reference to either
removed command, either removed script, or the deleted correspondence test.
Historical plan/spec records and the architecture guard's negative absence
assertion remain non-executable. Searches also found no `origins` plumbing in
the Frege test and no body-node witness wording in the relation-wire comment.

Commands and results:

```text
npx vitest run --config vitest.config.ts tests/architecture tests/app/edit.test.ts tests/theories/frege.test.ts
6 files passed; 55 tests passed

npm test
107 files passed; 652 tests passed

npm run typecheck
passed (tsc --noEmit)

node --input-type=module -e <package/script absence assertion>
unsupported formal command surface is absent

git diff --check -- package.json scripts/check-lean-step-tags.mjs scripts/check-formalization.mjs src/app/edit.ts tests/theories/frege.test.ts
passed with no output
```

## Self-review

- The source diff is exactly five scoped paths: two package entries removed,
  two now-unowned scripts deleted, one comment corrected, and three unused
  test-metadata lines removed.
- No executable source behavior changed.
- No Lean or VisualProof path changed.
- No kernel, theorem, proof-step, JSON, replay, interaction, or generated
  artifact changed.
- No compatibility command, wrapper, alias, fallback, or parked executable
  path remains.
- `archive/` and `scratchpad/` were excluded from every repository search and
  were not read, touched, staged, deleted, or stashed.

## Staged paths

Only these task-owned paths are to be staged:

```text
package.json
scripts/check-formalization.mjs
scripts/check-lean-step-tags.mjs
src/app/edit.ts
tests/theories/frege.test.ts
.superpowers/sdd/2026-07-27-per-theorem-arithmetic-hypotheses/final-fix-report.md
```

## Commit

One commit is prepared with subject:
`chore: remove deferred formal validation commands`.

The commit containing this report cannot embed its own content-addressed SHA;
the authoritative SHA is the resulting `git log -1` value and the implementer
handoff.
