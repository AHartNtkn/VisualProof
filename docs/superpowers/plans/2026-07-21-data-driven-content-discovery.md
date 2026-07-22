# Data-Driven Content Discovery Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make manifest-owned runtime JSON automatically available to the game build so adding a complete puzzle bundle requires content changes only.

**Architecture:** Vite eagerly discovers only runtime content directories and materializes the existing `GameContentFiles` injection record. The manifest remains the sole selector and ordering authority; the pure synchronous loader and its exact failure behavior remain unchanged. The handwritten per-puzzle registry and every authoring contract that requires it are deleted.

**Tech Stack:** TypeScript 5.5, Vite 5, Vitest 2, Electron 43, strict JSON content format v3.

## Global Constraints

- `content/manifest.json` is the sole production registration and ordering authority.
- Discovered but unmanifested runtime JSON is inert.
- Runtime discovery includes manifest, puzzles, definitions, progression, catalog, and guidance only.
- Runtime discovery excludes coverage, validation, and schemas.
- Renderer and game code receive no Node, filesystem, Electron, IPC, fetch, or network authority.
- `loadGameContent(files)` remains synchronous, pure, bundler-independent, injectable, and path-strict.
- No generated registry, compatibility map, fallback catalog, or per-puzzle source entry may remain.
- Preserve all twelve uncommitted Seyric Metamath puzzle and validation bundles and their content-only metadata changes.

---

### Task 1: Replace the handwritten runtime inventory

**Files:**
- Create: `tests/game/content-files.test.ts`
- Modify: `tests/architecture/game-boundary.test.ts`
- Replace: `src/game/content/files.ts`
- Modify: `tsconfig.json`

**Interfaces:**
- Consumes: Vite `ImportMeta.glob`, current `GameContentFiles = Readonly<Record<string, unknown>>`, current manifest-relative path strings.
- Produces: unchanged `gameContentFiles: GameContentFiles` export containing automatically discovered runtime JSON.

- [ ] **Step 1: Write the failing production-inventory tests**

Create `tests/game/content-files.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { gameContentFiles } from '../../src/game/content/files'

type RuntimeManifest = {
  readonly puzzles: readonly string[]
  readonly definitions: readonly string[]
  readonly progression: string
  readonly catalog: string
  readonly guidance: string
}

describe('data-driven runtime content inventory', () => {
  it('makes every manifest-owned runtime file available automatically', () => {
    const manifest = gameContentFiles['manifest.json'] as RuntimeManifest
    const selected = [
      ...manifest.puzzles,
      ...manifest.definitions,
      manifest.progression,
      manifest.catalog,
      manifest.guidance,
    ]
    expect(selected.filter((path) => !Object.hasOwn(gameContentFiles, path))).toEqual([])
  })

  it('keeps build-only records out of the runtime inventory', () => {
    expect(Object.keys(gameContentFiles).filter((path) =>
      /^(?:coverage|validation|schemas)\//.test(path),
    )).toEqual([])
  })
})
```

Extend `tests/architecture/game-boundary.test.ts` in the existing runtime-content assertion:

```ts
expect(contentImports).toContain('import.meta.glob')
expect(contentImports).not.toMatch(/from\s+['"][^'"]*content\/(?:puzzles|definitions)\//)
expect(contentImports).not.toMatch(/['"]puzzles\/[^*'"]+\.json['"]\s*:/)
expect(contentImports).not.toContain('content/coverage')
expect(contentImports).not.toContain('content/validation')
expect(contentImports).not.toContain('content/schemas')
```

- [ ] **Step 2: Run the new tests and verify RED**

Run:

```bash
npx vitest run tests/game/content-files.test.ts tests/architecture/game-boundary.test.ts tests/game/catalog.test.ts
```

Expected: `content-files.test.ts` reports the twelve missing `seyric-metamath-*` paths, the architecture assertion reports the missing glob and individual imports, and `catalog.test.ts` fails at `puzzles/seyric-metamath-pm2-82.json`.

- [ ] **Step 3: Replace the registry with eager positive-pattern discovery**

Replace all of `src/game/content/files.ts` with:

```ts
import type { GameContentFiles } from '../content-loader'

const contentPrefix = '../../../content/'
const discovered = import.meta.glob<unknown>([
  '../../../content/manifest.json',
  '../../../content/puzzles/**/*.json',
  '../../../content/definitions/**/*.json',
  '../../../content/progression/**/*.json',
  '../../../content/catalog/**/*.json',
  '../../../content/guidance/**/*.json',
], { eager: true, import: 'default' })

const entries = Object.entries(discovered).map(([path, value]) => {
  if (!path.startsWith(contentPrefix)) throw new Error(`unexpected content module path '${path}'`)
  return [path.slice(contentPrefix.length), value] as const
})

export const gameContentFiles: GameContentFiles = Object.freeze(Object.fromEntries(entries))
```

Add `"vite/client"` beside `"node"` in `tsconfig.json`'s `compilerOptions.types` so test, source, and renderer compilation use the same Vite environment.

- [ ] **Step 4: Run focused GREEN validation**

Run:

```bash
npx vitest run tests/game/content-files.test.ts tests/architecture/game-boundary.test.ts tests/game/catalog.test.ts tests/game/layered-content.test.ts tests/game/culture-progression-coherence.test.ts
npm run typecheck
```

Expected: all tests and typecheck pass; the catalog contains all 121 manifest puzzles.

- [ ] **Step 5: Verify deletion and commit Task 1 only**

Run:

```bash
rg -n "from ['\"].*content/puzzles/|['\"]puzzles/[^*]+\.json['\"]\s*:" src/game/content/files.ts
git diff --check
```

Expected: the search has no matches and the diff check passes.

Commit only Task 1 files:

```bash
git add src/game/content/files.ts tsconfig.json tests/game/content-files.test.ts tests/architecture/game-boundary.test.ts
git commit -m "fix: derive runtime content inventory"
```

---

### Task 2: Remove stale authoring synchronization contracts

**Files:**
- Modify: `tests/game/content-validation.test.ts`
- Modify: `tests/game/culture-content-migration.test.ts`
- Modify: `docs/game-content-format.md`
- Modify: `docs/seyric-content-authoring-handoff.md`

**Interfaces:**
- Consumes: automatic `gameContentFiles`, `validateGameContent()` receipt, manifest-owned content model.
- Produces: content tests and authoring documentation that require no per-puzzle source update.

- [ ] **Step 1: Run the stale receipt test and verify RED**

Run:

```bash
npx vitest run tests/game/content-validation.test.ts -t "schema-validates every registered layer"
```

Expected: FAIL because the current test hard-codes 1,039 actions while the twelve new witnesses produce 1,448.

- [ ] **Step 2: Replace the hard-coded inventory receipt with structural invariants**

In `tests/game/content-validation.test.ts`, replace the exact `actions: 1039` object with:

```ts
const receipt = validateGameContent()
expect(receipt).toMatchObject({
  puzzles: catalog.puzzleIds.length,
  solutions: catalog.puzzleIds.length,
  recognizedStates,
})
expect(receipt.actions).toBeGreaterThanOrEqual(receipt.solutions)
```

This keeps exact puzzle/solution/catalog agreement and witness existence while allowing content-authored witness lengths to change.

- [ ] **Step 3: Remove the static registry as an authored authority**

In `tests/game/culture-content-migration.test.ts`, remove `src/game/content/files.ts` from the concatenated authored authority text. Keep the behavioral `gameContentFiles` absence assertion for removed puzzle paths.

In `docs/game-content-format.md`, replace the integration-bundle requirement for a “corresponding static runtime import” with automatic build-time availability through the approved runtime content directories. State that the manifest alone registers and orders content.

In `docs/seyric-content-authoring-handoff.md`, remove static-import synchronization from the author checklist and state that Vite derives runtime availability while manifest registration remains mandatory.

- [ ] **Step 4: Run focused GREEN validation**

Run:

```bash
npx vitest run tests/game/content-validation.test.ts tests/game/culture-content-migration.test.ts tests/game/catalog.test.ts tests/game/culture-progression-coherence.test.ts tests/game/opening-content.test.ts
npm run content:validate
npm run typecheck
git diff --check
```

Expected: all tests and commands pass; content validation reports 121 puzzles, 121 solutions, and 1,448 actions.

- [ ] **Step 5: Commit Task 2 only**

```bash
git add tests/game/content-validation.test.ts tests/game/culture-content-migration.test.ts docs/game-content-format.md docs/seyric-content-authoring-handoff.md
git commit -m "docs: make manifest the sole content registry"
```

---

### Task 3: Validate and commit the twelve content bundles

**Files:**
- Add: `content/puzzles/seyric-metamath-*.json` (12 files)
- Add: `content/validation/seyric-metamath-*.json` (12 files)
- Modify: `content/manifest.json`
- Modify: `content/catalog/cursebreaker.json`
- Modify: `content/coverage/seyric.json`
- Modify: `content/progression/core.json`

**Interfaces:**
- Consumes: automatic runtime discovery from Task 1 and existing content format v3.
- Produces: twelve runtime-loadable optional Seyric puzzles with authenticated replaying witnesses.

- [ ] **Step 1: Run authoritative content and runtime validation**

Run:

```bash
npm run content:validate
npx vitest run tests/game/content-files.test.ts tests/game/catalog.test.ts tests/game/content-validation.test.ts tests/game/culture-progression-coherence.test.ts tests/game/seyric-content-authority.test.ts tests/game/seyric-culture-owned-puzzles.test.ts
```

Expected: content validation reports 121 puzzles, 121 solutions, 1,448 actions; all focused tests pass.

- [ ] **Step 2: Run build and architecture validation**

Run:

```bash
npx vitest run tests/architecture/game-boundary.test.ts tests/architecture/game-proof-hot-path.test.ts tests/platform/package-contract.test.ts
npm run typecheck
npm run build:renderer
npm run build:desktop
npm run test:desktop-startup
```

Expected: every test, typecheck, renderer build, desktop build, and desktop startup passes.

- [ ] **Step 3: Audit exact content scope and registration**

Run:

```bash
git status --short
git diff --check
rg -n "seyric-metamath-(pm2-82|4exmid|cases2-hard-direction|cases2|4cases|anddi|orddi|ccase|majority|peirceroll|meredith|dn1)" content/manifest.json content/catalog/cursebreaker.json content/coverage/seyric.json content/progression/core.json
```

Expected: each ID occurs exactly once in each required content authority, and no uncommitted path exists outside the Task 3 content files.

- [ ] **Step 4: Commit the content bundles only**

```bash
git add content/manifest.json content/catalog/cursebreaker.json content/coverage/seyric.json content/progression/core.json content/puzzles/seyric-metamath-*.json content/validation/seyric-metamath-*.json
git commit -m "content: add optional Seyric Metamath challenges"
```

- [ ] **Step 5: Run final clean-tree verification**

Run:

```bash
npm run content:validate
npx vitest run tests/game/content-files.test.ts tests/game/catalog.test.ts tests/game/content-validation.test.ts tests/game/culture-progression-coherence.test.ts
npm run typecheck
git status --short
```

Expected: all commands pass and the worktree is clean.
