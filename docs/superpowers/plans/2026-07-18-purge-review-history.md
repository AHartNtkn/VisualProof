# Purge Review and Obsolete Asset History Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove review-only renders, scenes, duplicate demos, reproduction machinery, and displaced interface assets from the current game and every commit reachable from `game/cursebreaker-domain`, while retaining approved production pixels and a validated playable build.

**Architecture:** Replace the source/hash/reproduction manifest with one declarative semantic registry of the PNGs consumed by production. Delete every review/demo authority and obsolete asset from the current tree, then rewrite only the game branch ancestry with a path-based index filter. A temporary local recovery ref protects the operation until verification; the remote branch is updated only with an exact `--force-with-lease` tied to the audited pre-rewrite remote tip.

**Tech Stack:** TypeScript 5.5, Node 22, PNG IHDR inspection, Vitest, Playwright Chromium, Vite, Electron TypeScript build, Git `filter-branch`/index filtering.

## Global Constraints

- Preserve the approved desk, gasket, timeline housing/handle, substrate, folio, specimen, and three editor-loupe production PNG blobs exactly.
- Remove review renders and runnable review scenes instead of replacing them with aliases, ignored copies, or compatibility paths.
- Replace exact-byte/source-reproduction authority with semantic checks for required path, dimensions, color/alpha representation, layer geometry, and actual runtime consumption.
- Preserve unrelated commits and user work; rewrite only `game/cursebreaker-domain` and update only its matching remote branch.
- Use `git push --force-with-lease` with the exact audited old remote commit; never use an unguarded force push.
- Keep a temporary local recovery ref until the rewritten branch passes validation, then delete it and `refs/original` so the removed history is no longer reachable through cleanup refs.
- Do not run the dedicated physics battery.

---

### Task 1: Semantic production-asset authority

**Files:**
- Create: `scripts/assets/production-interface-assets.ts`
- Create: `tests/assets/production-interface-assets.test.ts`
- Modify: `scripts/assets/validate-interface-assets.ts`
- Modify: `tests/game/construction-loupe-assets.test.ts`

**Interfaces:**
- Produces: `PRODUCTION_INTERFACE_ASSETS: readonly ProductionInterfaceAsset[]`
- Produces: `validateProductionInterfaceAssets(root: string): string[]`
- Consumes: approved PNG files and their production consumer source paths.

- [ ] **Step 1: Write the failing semantic-registry test**

Create `tests/assets/production-interface-assets.test.ts` with checks that call
`validateProductionInterfaceAssets(process.cwd())`, expect no errors, expect the
registry to contain exactly the runtime asset paths, and reject all paths under
`review/`, all `.blend` paths, and the obsolete filenames
`frame.png`, `glass.png`, `shadow.png`, `lever-housing.png`, and
`lever-handle.png`.

```ts
import { describe, expect, it } from 'vitest'
import {
  PRODUCTION_INTERFACE_ASSETS,
  validateProductionInterfaceAssets,
} from '../../scripts/assets/production-interface-assets'

describe('production interface asset authority', () => {
  it('semantically validates only assets consumed by the game', () => {
    expect(validateProductionInterfaceAssets(process.cwd())).toEqual([])
    const paths = PRODUCTION_INTERFACE_ASSETS.map(({ path }) => path)
    expect(paths).not.toContainEqual(expect.stringMatching(/^review\//))
    expect(paths).not.toContainEqual(expect.stringMatching(/\.blend$/))
    expect(paths).not.toContainEqual(expect.stringMatching(
      /central-lens\/(?:frame|glass|shadow|lever-housing|lever-handle)\.png$/,
    ))
  })
})
```

- [ ] **Step 2: Run the test and verify the missing-module failure**

Run:

```bash
npx vitest run tests/assets/production-interface-assets.test.ts
```

Expected: FAIL because `scripts/assets/production-interface-assets.ts` does not
exist.

- [ ] **Step 3: Implement the semantic registry and validator**

Create a focused module with this public representation:

```ts
export type ProductionInterfaceAsset = {
  readonly path: string
  readonly width: number
  readonly height: number
  readonly colorType: 'rgb' | 'rgba'
  readonly consumer: string
  readonly token: string
}

export const PRODUCTION_INTERFACE_ASSETS = [
  {
    path: 'assets/interface/generated/desk/natural-indigo-hardwood.png',
    width: 2048, height: 2048, colorType: 'rgb',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'desk/natural-indigo-hardwood.png',
  },
  {
    path: 'assets/interface/generated/central-lens/gasket-frame.png',
    width: 4096, height: 4096, colorType: 'rgba',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'central-lens/gasket-frame.png',
  },
  { path: 'assets/interface/generated/central-lens/timeline-housing.png', width: 4096, height: 4096, colorType: 'rgba', consumer: 'src/game/interface/lens-environment.ts', token: 'central-lens/timeline-housing.png' },
  { path: 'assets/interface/generated/central-lens/timeline-handle.png', width: 4096, height: 4096, colorType: 'rgba', consumer: 'src/game/interface/lens-environment.ts', token: 'central-lens/timeline-handle.png' },
  { path: 'assets/interface/generated/substrates/static-review-substrate.png', width: 1024, height: 1024, colorType: 'rgb', consumer: 'src/game/interface/lens-environment.ts', token: 'substrates/static-review-substrate.png' },
  { path: 'assets/interface/generated/excavation-folio/folio-shell.png', width: 1100, height: 820, colorType: 'rgba', consumer: 'src/game/interface/folio.css', token: 'excavation-folio/folio-shell.png' },
  { path: 'assets/interface/generated/excavation-folio/dossier-sheet.png', width: 900, height: 720, colorType: 'rgba', consumer: 'src/game/interface/folio.css', token: 'excavation-folio/dossier-sheet.png' },
  { path: 'assets/interface/generated/excavation-folio/mount-photo.png', width: 720, height: 460, colorType: 'rgba', consumer: 'src/game/interface/folio.css', token: 'excavation-folio/mount-photo.png' },
  { path: 'assets/interface/generated/excavation-folio/clearance-slip.png', width: 500, height: 180, colorType: 'rgba', consumer: 'src/game/interface/folio.css', token: 'excavation-folio/clearance-slip.png' },
  { path: 'assets/interface/generated/excavation-folio/restricted-sleeve.png', width: 680, height: 430, colorType: 'rgba', consumer: 'src/game/interface/folio.css', token: 'excavation-folio/restricted-sleeve.png' },
  { path: 'assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png', width: 760, height: 470, colorType: 'rgba', consumer: 'src/game/interface/folio-view.ts', token: 'specimens/auten-reliquary-closure.png' },
  { path: 'assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png', width: 760, height: 470, colorType: 'rgba', consumer: 'src/game/interface/folio-view.ts', token: 'specimens/seyric-field-seal-s-27.png' },
  { path: 'assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png', width: 760, height: 470, colorType: 'rgba', consumer: 'src/game/interface/folio-view.ts', token: 'specimens/uninscribed-votive-of-myrat.png' },
  { path: 'assets/interface/generated/editor-loupe/rim-socket.png', width: 1400, height: 1400, colorType: 'rgba', consumer: 'src/game/interface/construction-loupe.ts', token: 'editor-loupe/rim-socket.png' },
  { path: 'assets/interface/generated/editor-loupe/handle-terminal.png', width: 1400, height: 1400, colorType: 'rgba', consumer: 'src/game/interface/construction-loupe.ts', token: 'editor-loupe/handle-terminal.png' },
  { path: 'assets/interface/generated/editor-loupe/optical-edge.png', width: 1400, height: 1400, colorType: 'rgba', consumer: 'src/game/interface/construction-loupe.ts', token: 'editor-loupe/optical-edge.png' },
] as const satisfies readonly ProductionInterfaceAsset[]
```

Implement a strict PNG header reader that verifies the signature, 8-bit depth,
non-interlacing, exact dimensions, and IHDR color type `2` for `rgb` or `6` for
`rgba`. For RGBA files, use `inspectPngFile` to require visible alpha. Read each
declared consumer and require its exact token. Add editor-loupe sample checks:
transparent corners/aperture on all layers, visible rim at `(650, 180)`, visible
terminal at `(1200, 1180)`, and visible optics at `(1080, 650)`.

- [ ] **Step 4: Remove Candidate A source-pixel authority from the game test**

Delete the `review/editor-loupe-study/isolated/candidate-a.png` import and the
entire “losslessly partitions approved source pixels” test from
`tests/game/construction-loupe-assets.test.ts`. Retain semantic geometry,
transparency, CSS pointer behavior, and production-consumption checks.

- [ ] **Step 5: Point the command-line validator at the new authority**

Replace `scripts/assets/validate-interface-assets.ts` with:

```ts
import { validateProductionInterfaceAssets } from './production-interface-assets'

const errors = validateProductionInterfaceAssets(process.cwd())
for (const error of errors) console.error(error)
if (errors.length > 0) process.exitCode = 1
```

- [ ] **Step 6: Run focused validation**

Run:

```bash
npx vitest run tests/assets/production-interface-assets.test.ts tests/game/construction-loupe-assets.test.ts
npm run assets:validate
```

Expected: both test files pass and the semantic validator exits 0 without
printing errors.

- [ ] **Step 7: Commit the new authority**

```bash
git add scripts/assets/production-interface-assets.ts scripts/assets/validate-interface-assets.ts tests/assets/production-interface-assets.test.ts tests/game/construction-loupe-assets.test.ts
git commit -m "assets: validate production semantics"
```

### Task 2: Delete review, scene, and reproduction authority

**Files:**
- Delete: `review/`
- Delete: `tests/review/`
- Delete: `assets/interface/source/`
- Delete: `assets/interface/manifest.json`
- Delete: `assets/interface/generated/central-lens/frame.png`
- Delete: `assets/interface/generated/central-lens/glass.png`
- Delete: `assets/interface/generated/central-lens/shadow.png`
- Delete: `assets/interface/generated/central-lens/lever-housing.png`
- Delete: `assets/interface/generated/central-lens/lever-handle.png`
- Delete: `assets/interface/generated/excavation-folio/guard-leaf.png`
- Delete: `assets/interface/generated/excavation-folio/mount-rubbing.png`
- Delete: `assets/interface/generated/excavation-folio/mount-tracing.png`
- Delete: `assets/interface/generated/excavation-folio/priority-band.png`
- Delete: `scripts/assets/audit-excavation-folio-assets.py`
- Delete: `scripts/assets/build-editor-loupe-layers.ts`
- Delete: `scripts/assets/build-editor-loupe-study.py`
- Delete: `scripts/assets/build-excavation-folio-assets.py`
- Delete: `scripts/assets/render-approved-static-assets.py`
- Delete: `scripts/assets/render-corrected-mechanical.py`
- Delete: `scripts/build-editor-loupe-comparison.py`
- Delete: `scripts/build-substrate-darkness-options.py`
- Delete: `scripts/capture-excavation-folio.mjs`
- Delete: `scripts/capture-interface-static.mjs`
- Delete: `scripts/validate-interface-static.mjs`
- Delete: `scripts/assets/blender/`
- Delete: `scripts/assets/check-blender.sh`
- Delete: `scripts/assets/install-blender.sh`
- Delete: `scripts/assets/manifest.ts`
- Delete: `scripts/assets/promote-interface.ts`
- Delete: `scripts/assets/render-interface.sh`
- Delete: `scripts/assets/verify-render-reproducibility.sh`
- Delete: `scripts/assets/validate-editor-loupe-layers.ts`
- Delete: `tests/assets/manifest.test.ts`
- Delete: `tests/assets/promote-interface.test.ts`
- Delete: `tests/assets/render-contract.test.ts`
- Modify: `package.json`

**Interfaces:**
- Consumes: Task 1 semantic validator.
- Produces: one current tree containing only game-owned production assets.

- [ ] **Step 1: Add a failing displaced-path source test**

Extend `tests/assets/production-interface-assets.test.ts` to recursively scan
tracked/current paths and assert that these authorities do not exist:

```ts
const forbidden = [
  'review',
  'tests/review',
  'assets/interface/source',
  'assets/interface/manifest.json',
  'scripts/assets/manifest.ts',
  'scripts/assets/promote-interface.ts',
  'scripts/assets/build-editor-loupe-layers.ts',
  'scripts/assets/build-editor-loupe-study.py',
  'scripts/assets/build-excavation-folio-assets.py',
  'scripts/assets/blender',
  'scripts/assets/render-interface.sh',
  'scripts/assets/verify-render-reproducibility.sh',
]
for (const path of forbidden) expect(existsSync(resolve(path)), path).toBe(false)
```

Run the test and expect failure on the first still-existing review path.

- [ ] **Step 2: Remove review trees, review tests, and review-only scripts**

Use `git rm` for the complete `review/` and `tests/review/` trees and these
review-specific files:

```text
scripts/assets/audit-excavation-folio-assets.py
scripts/assets/build-editor-loupe-layers.ts
scripts/assets/build-editor-loupe-study.py
scripts/assets/build-excavation-folio-assets.py
scripts/assets/render-approved-static-assets.py
scripts/assets/render-corrected-mechanical.py
scripts/build-editor-loupe-comparison.py
scripts/build-substrate-darkness-options.py
scripts/capture-excavation-folio.mjs
scripts/capture-interface-static.mjs
scripts/validate-interface-static.mjs
```

- [ ] **Step 3: Remove Blender/source and obsolete manifest authority**

Use `git rm` for `assets/interface/source/`, `assets/interface/manifest.json`,
the five obsolete central-lens PNGs, and the four demo-only folio PNGs listed in
the task file section.

- [ ] **Step 4: Remove obsolete renderer/promotion machinery and its tests**

Use `git rm` for:

```text
scripts/assets/blender/
scripts/assets/check-blender.sh
scripts/assets/install-blender.sh
scripts/assets/manifest.ts
scripts/assets/promote-interface.ts
scripts/assets/render-interface.sh
scripts/assets/verify-render-reproducibility.sh
scripts/assets/validate-editor-loupe-layers.ts
tests/assets/manifest.test.ts
tests/assets/promote-interface.test.ts
tests/assets/render-contract.test.ts
```

Keep `scripts/assets/canonical-png.ts`, its unit test, the new semantic
validator, and `scripts/assets/capture-central-lens.mjs` because its captures
remain ignored runtime evidence rather than committed review media.

- [ ] **Step 5: Remove the obsolete package command**

Delete `assets:build-loupe` from `package.json`. Keep `assets:validate` and
`assets:capture-lens`.

- [ ] **Step 6: Prove the current tree has no displaced path or consumer**

Run:

```bash
npx vitest run tests/assets tests/game/construction-loupe-assets.test.ts tests/game/authoritative-runtime-source.test.ts
npm run assets:validate
rg -n "review/|editor-loupe-study|central-lens/(frame|glass|shadow|lever-housing|lever-handle)\.png|excavation-folio/(guard-leaf|mount-rubbing|mount-tracing|priority-band)\.png|manifest\.json|verify-render-reproducibility" app src electron scripts tests package.json
```

Expected: tests and validation pass; `rg` returns no matches.

- [ ] **Step 7: Commit current-tree cleanup**

Stage only the enumerated deletions and migrations, inspect
`git diff --cached --stat`, then commit:

```bash
git commit -m "chore: remove review asset authority"
```

### Task 3: Validate the pre-rewrite game and preserve rewrite receipts

**Files:**
- Create outside repository: `/tmp/cursebreaker-history-cleanup-yN8Cq7/pre-rewrite-receipt.txt`
- Append outside repository: `/tmp/cursebreaker-history-cleanup-yN8Cq7/foundation.md`

**Interfaces:**
- Consumes: clean Task 2 commit.
- Produces: exact old local/remote commit IDs, approved blob IDs, target path
  list, and a temporary recovery ref.

- [ ] **Step 1: Run authoritative pre-rewrite validation**

Run the complete non-physics game and platform tests, `tests/assets`, semantic
asset validation, typecheck, desktop build, and `git diff --check`. Expect the
established typecheck baseline only if the removed review test no longer exists;
after deleting `tests/review/editor-loupe-study.test.ts`, typecheck must pass.

- [ ] **Step 2: Record immutable rewrite inputs**

Record in the scratch receipt:

```text
old_local_head=<git rev-parse game/cursebreaker-domain>
old_remote_head=249b8e40e3e054eeedf700edbeaf6e6ee6da2a33
backup_ref=refs/backup/cursebreaker-history-cleanup
```

Append the `git hash-object` blob ID for every retained production PNG in
`PRODUCTION_INTERFACE_ASSETS` and the complete filtered path list from Task 2.

- [ ] **Step 3: Create the temporary recovery ref**

Run:

```bash
git update-ref refs/backup/cursebreaker-history-cleanup HEAD
```

Verify the ref resolves to `old_local_head` before rewriting.

### Task 4: Rewrite branch ancestry and update the remote safely

**Files:**
- Rewrite: `refs/heads/game/cursebreaker-domain`
- Delete after verification: `refs/backup/cursebreaker-history-cleanup`
- Delete after verification: `refs/original/refs/heads/game/cursebreaker-domain`

**Interfaces:**
- Consumes: Task 3 receipt and recovery ref.
- Produces: rewritten local and remote game branch with no target paths in any
  reachable commit.

- [ ] **Step 1: Run the narrow index-filter rewrite**

Run this command for only `game/cursebreaker-domain`; do not pass `-- --all`,
tags, `main`, or any other branch:

```bash
FILTER_BRANCH_SQUELCH_WARNING=1 git filter-branch --force --index-filter 'git rm -r --cached --ignore-unmatch -- review tests/review assets/interface/source assets/interface/manifest.json assets/interface/generated/central-lens/frame.png assets/interface/generated/central-lens/glass.png assets/interface/generated/central-lens/shadow.png assets/interface/generated/central-lens/lever-housing.png assets/interface/generated/central-lens/lever-handle.png assets/interface/generated/excavation-folio/guard-leaf.png assets/interface/generated/excavation-folio/mount-rubbing.png assets/interface/generated/excavation-folio/mount-tracing.png assets/interface/generated/excavation-folio/priority-band.png scripts/assets/audit-excavation-folio-assets.py scripts/assets/blender scripts/assets/build-editor-loupe-layers.ts scripts/assets/build-editor-loupe-study.py scripts/assets/build-excavation-folio-assets.py scripts/assets/check-blender.sh scripts/assets/install-blender.sh scripts/assets/manifest.ts scripts/assets/promote-interface.ts scripts/assets/render-approved-static-assets.py scripts/assets/render-corrected-mechanical.py scripts/assets/render-interface.sh scripts/assets/verify-render-reproducibility.sh scripts/assets/validate-editor-loupe-layers.ts scripts/build-editor-loupe-comparison.py scripts/build-substrate-darkness-options.py scripts/capture-excavation-folio.mjs scripts/capture-interface-static.mjs scripts/validate-interface-static.mjs tests/assets/manifest.test.ts tests/assets/promote-interface.test.ts tests/assets/render-contract.test.ts' -- game/cursebreaker-domain
```

Expected: commits at and after the earliest target-bearing game commit receive
new IDs; the checked-out tree still matches the validated cleanup commit.

- [ ] **Step 2: Verify historical absence and retained blob identity**

For every filtered path, run:

```bash
git log game/cursebreaker-domain --all-match -- <path>
```

Expected: no output when scoped to the rewritten branch. Run this complete-tree
scan and expect no matches:

```bash
git rev-list game/cursebreaker-domain | while IFS= read -r commit; do
  git ls-tree -r --name-only "$commit"
done | rg '^(review/|tests/review/|assets/interface/source/|assets/interface/manifest\.json$)|central-lens/(frame|glass|shadow|lever-housing|lever-handle)\.png$|excavation-folio/(guard-leaf|mount-rubbing|mount-tracing|priority-band)\.png$|^(scripts/assets/(audit-excavation-folio-assets|build-editor-loupe-layers|build-editor-loupe-study|build-excavation-folio-assets|check-blender|install-blender|manifest|promote-interface|render-approved-static-assets|render-corrected-mechanical|render-interface|verify-render-reproducibility|validate-editor-loupe-layers)|scripts/(build-editor-loupe-comparison|build-substrate-darkness-options|capture-excavation-folio|capture-interface-static|validate-interface-static)|tests/assets/(manifest|promote-interface|render-contract))\.'
```

Compare every retained production PNG's new `git hash-object` result with the
Task 3 receipt; every blob ID must match.

- [ ] **Step 3: Re-run post-rewrite validation**

Run:

```bash
npx vitest run tests/game
npx vitest run tests/platform
npx vitest run tests/assets
npm run assets:validate
npm run typecheck
npm run build:desktop
npx vitest run tests/game/built-renderer-csp-smoke.test.ts
git diff --check
```

Expected: every remaining game, platform, and asset test passes; semantic asset
validation, typecheck, desktop build, CSP smoke, and diff integrity all pass.
The physics configuration is not invoked.

- [ ] **Step 4: Update only the matching remote branch with an exact lease**

Run:

```bash
git push --force-with-lease=refs/heads/game/cursebreaker-domain:249b8e40e3e054eeedf700edbeaf6e6ee6da2a33 origin game/cursebreaker-domain:game/cursebreaker-domain
```

Expected: the push succeeds only if the remote branch still equals the audited
old remote tip. If the lease fails, stop without broadening or fetching over the
evidence; report the changed remote tip.

- [ ] **Step 5: Remove recovery refs only after remote and local verification**

Delete `refs/backup/cursebreaker-history-cleanup` and
`refs/original/refs/heads/game/cursebreaker-domain`, expire only the rewritten
branch's reflog entries if necessary, and verify neither ref resolves. Do not
run repository-wide immediate pruning because it could destroy unrelated
unreachable user recovery objects.

- [ ] **Step 6: Append conformance and report exact results**

Append `<conformance>` to the scratch foundation record with removed paths and
bytes, rewritten local/remote tips, preserved production blob evidence,
validation commands/results, recovery-ref deletion, and proof that the old
review/obsolete history is unreachable from the rewritten game branch and its
remote-tracking ref.
