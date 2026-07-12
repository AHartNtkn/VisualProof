# Opt-In Expensive Physics Tests Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Keep routine validation comprehensive and fast by moving only expensive settling/simulation tests behind explicit physics and full-suite commands.

**Architecture:** `vitest.suites.ts` is the single authority for ordinary, physics, and combined file selection and timeout policy. Expensive tests live in `tests/physics/`; settle-dominated files move intact and mixed files are split so cheap assertions remain ordinary. Package scripts select a suite through `VPA_TEST_SUITE`, while architecture tests and `vitest list --filesOnly` prove the actual boundaries.

**Tech Stack:** TypeScript 5.5, Vitest 2.1, npm scripts.

## Global Constraints

- `npm test` runs every ordinary test and no file under `tests/physics/`.
- `npm run test:physics` runs only `tests/physics/**/*.test.ts` with the existing 1,800,000 ms timeout.
- `npm run test:all` runs ordinary and physics tests in one Vitest invocation.
- Cheap deterministic engine, geometry, and bounded interaction tests remain ordinary.
- Expensive classification is owned by the `tests/physics/` location, never a duplicate filename list.
- Existing test assertions and physics budgets are preserved; this work changes scheduling, not behavior.

---

## File Structure

- Create `vitest.suites.ts`: validate `VPA_TEST_SUITE` and produce the authoritative include/exclude/timeout policy.
- Modify `vitest.config.ts`: consume the suite policy instead of globally selecting every test with long timeouts.
- Modify `package.json`: expose ordinary, physics, and all commands.
- Create `tests/architecture/test-suites.test.ts`: unit-test all suite policies and invalid selection.
- Create `tests/physics/`: own every expensive settling/simulation test.
- Split mixed tests in `tests/app` and `tests/view` so their cheap cases remain ordinary.

---

### Task 1: Authoritative Suite Selection

**Files:**
- Create: `vitest.suites.ts`
- Modify: `vitest.config.ts`
- Modify: `package.json`
- Create: `tests/architecture/test-suites.test.ts`

**Interfaces:**
- Produces: `type TestSuite = 'ordinary' | 'physics' | 'all'`
- Produces: `testSuite(value?: string): TestSuite`
- Produces: `suiteTestConfig(suite: TestSuite): Pick<InlineConfig, 'include' | 'exclude' | 'testTimeout' | 'hookTimeout'>`

- [ ] **Step 1: Write failing policy tests**

Create `tests/architecture/test-suites.test.ts`:

```ts
import { describe, expect, it } from 'vitest'
import { suiteTestConfig, testSuite } from '../../vitest.suites'

describe('Vitest suite ownership', () => {
  it('defaults to ordinary validation', () => {
    expect(testSuite()).toBe('ordinary')
    expect(suiteTestConfig('ordinary')).toEqual({
      include: ['tests/**/*.test.ts'],
      exclude: ['tests/physics/**/*.test.ts'],
      testTimeout: 5_000,
      hookTimeout: 10_000,
    })
  })

  it('selects exactly the expensive physics directory', () => {
    expect(suiteTestConfig('physics')).toEqual({
      include: ['tests/physics/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    })
  })

  it('selects both authorities for full validation', () => {
    expect(suiteTestConfig('all')).toEqual({
      include: ['tests/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    })
  })

  it('refuses an unknown suite instead of silently changing coverage', () => {
    expect(() => testSuite('slow')).toThrow(/unknown VPA_TEST_SUITE 'slow'/)
  })
})
```

- [ ] **Step 2: Verify RED**

Run: `npx vitest run tests/architecture/test-suites.test.ts`

Expected: FAIL because `vitest.suites.ts` does not exist.

- [ ] **Step 3: Implement the single selection authority**

Create `vitest.suites.ts`:

```ts
import type { InlineConfig } from 'vitest/node'

export type TestSuite = 'ordinary' | 'physics' | 'all'

export function testSuite(value = process.env.VPA_TEST_SUITE): TestSuite {
  if (value === undefined || value === '') return 'ordinary'
  if (value === 'ordinary' || value === 'physics' || value === 'all') return value
  throw new Error(`unknown VPA_TEST_SUITE '${value}'; expected ordinary, physics, or all`)
}

export function suiteTestConfig(
  suite: TestSuite,
): Pick<InlineConfig, 'include' | 'exclude' | 'testTimeout' | 'hookTimeout'> {
  if (suite === 'ordinary') {
    return {
      include: ['tests/**/*.test.ts'],
      exclude: ['tests/physics/**/*.test.ts'],
      testTimeout: 5_000,
      hookTimeout: 10_000,
    }
  }
  if (suite === 'physics') {
    return {
      include: ['tests/physics/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    }
  }
  return {
    include: ['tests/**/*.test.ts'],
    exclude: [],
    testTimeout: 1_800_000,
    hookTimeout: 1_800_000,
  }
}
```

Replace `vitest.config.ts` with:

```ts
import { defineConfig } from 'vitest/config'
import { suiteTestConfig, testSuite } from './vitest.suites'

export default defineConfig({
  test: suiteTestConfig(testSuite()),
})
```

Add these scripts in `package.json`:

```json
"test": "vitest run",
"test:physics": "VPA_TEST_SUITE=physics vitest run",
"test:all": "VPA_TEST_SUITE=all vitest run",
"test:watch": "vitest"
```

- [ ] **Step 4: Verify GREEN and command routing**

Run: `npx vitest run tests/architecture/test-suites.test.ts`

Expected: 4 tests PASS.

Run: `npm run typecheck`

Expected: PASS.

Run: `npx vitest list --filesOnly`

Expected: command succeeds and prints no `tests/physics/` path.

Run: `VPA_TEST_SUITE=physics npx vitest list --filesOnly --passWithNoTests`

Expected at this task boundary: exits successfully with no files. Task 2 supplies the files.

- [ ] **Step 5: Commit**

```bash
git add vitest.suites.ts vitest.config.ts package.json tests/architecture/test-suites.test.ts
git commit -m "test: separate ordinary and physics suites"
```

---

### Task 2: Migrate Expensive Tests Without Losing Cheap Coverage

**Files:**
- Create: `tests/physics/relax.test.ts`
- Create: `tests/physics/wirephys.test.ts`
- Create: `tests/physics/drag-clamp.test.ts`
- Create: `tests/physics/pipeline.test.ts`
- Create: `tests/physics/paint.test.ts`
- Create: `tests/physics/wires.test.ts`
- Create: `tests/physics/hittest.test.ts`
- Create: `tests/physics/stub-scope.test.ts`
- Create: `tests/physics/define-render.test.ts`
- Create: `tests/physics/session-boundary.test.ts`
- Modify: `tests/view/paint.test.ts`
- Modify: `tests/view/wires.test.ts`
- Modify: `tests/view/stub-scope.test.ts`
- Modify: `tests/app/hittest.test.ts`
- Modify: `tests/app/define.test.ts`
- Modify: `tests/app/session.test.ts`

**Interfaces:**
- Consumes: the `tests/physics/**/*.test.ts` selection authority from Task 1.
- Produces: a location-based partition with unchanged assertions and fixture budgets.

- [ ] **Step 1: Move settle-dominated files intact**

Run:

```bash
mkdir -p tests/physics
git mv tests/view/relax.test.ts tests/physics/relax.test.ts
git mv tests/view/wirephys.test.ts tests/physics/wirephys.test.ts
git mv tests/view/drag-clamp.test.ts tests/physics/drag-clamp.test.ts
git mv tests/view/pipeline.test.ts tests/physics/pipeline.test.ts
```

These files stay one directory below `tests`, so their existing `../../src/...` imports remain correct.

- [ ] **Step 2: Split the paint suite**

Move all engine/settle/paint assertions from `tests/view/paint.test.ts` into `tests/physics/paint.test.ts`, preserving their bodies and budgets verbatim. Keep these cheap assertions ordinary:

```text
authoritative content scale > paint derives node size directly from Engine.scale
law 6 > ships the two first-class themes
theme toggle > nextTheme flips between the two first-class themes
```

Retain only the imports and fixtures required by each resulting file. Do not rewrite assertions.

- [ ] **Step 3: Split the wire suite**

Keep the two pure anchor assertions in `tests/view/wires.test.ts`:

```text
worldBindAnchor > a ref binds on its DISC_R rim
worldBindAnchor > an atom/term binds on its port anchor
```

Move every remaining describe block, beginning with `computeLegs — the traced θ-quadratic legs ARE the wire`, into `tests/physics/wires.test.ts`. Preserve all settling budgets, wild-layout sweeps, and plusComm checks verbatim.

- [ ] **Step 4: Split mixed view/app suites by exact cases**

Create the named physics files and move these tests verbatim:

```text
tests/physics/stub-scope.test.ts
  after settling, the ∃ dot sits OUTSIDE both cut circles
  ∀-shape: a 2-endpoint wire scoped between the cuts grows a dangling ∃ branch THERE

tests/physics/hittest.test.ts
  dragTarget > a point on an ∃ dot grabs its homed body
  engine hit targets > a click on a branch junction resolves to its wire
  engine hit targets > a click on an existential stub resolves to its internal wire
  engine hit targets > a click on a boundary wire resolves to that wire
  engine hit targets > clicking an endpointless boundary port resolves to that wire
  engine hit targets > both boundary positions and the connecting path hit the same identity

tests/physics/define-render.test.ts
  defineRelation — the defined relation renders its argument-order pip (entire describe block)

tests/physics/session-boundary.test.ts
  sideBoundary > an engine built for a side connects every boundary wire to a fixed frame slot
```

Shared fixture helpers may be copied only when they are small immutable test builders; production logic must not be duplicated. Preserve assertion text and numeric budgets.

- [ ] **Step 5: Prove the partition with collection checks**

Run: `npx vitest list --filesOnly`

Expected: lists `tests/view`, `tests/app`, kernel, theory, architecture, and script tests; lists no `tests/physics` file.

Run: `VPA_TEST_SUITE=physics npx vitest list --filesOnly`

Expected: lists exactly the ten files under `tests/physics/` and no file outside that directory.

Run: `VPA_TEST_SUITE=all npx vitest list --filesOnly`

Expected: the union of the previous two file sets, with no duplicates.

- [ ] **Step 6: Run migrated focused tests**

Run:

```bash
npm test -- tests/view/paint.test.ts tests/view/wires.test.ts tests/view/stub-scope.test.ts tests/app/hittest.test.ts tests/app/define.test.ts tests/app/session.test.ts
```

Expected: ordinary retained tests run; any known session-undo baseline failures remain separately identifiable, and no settle-dominated moved case executes.

Run:

```bash
npm run test:physics
```

Expected: every migrated assertion executes. Fix only migration/configuration regressions; do not weaken a physics assertion or budget.

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add tests/physics tests/view tests/app
git commit -m "test: make expensive physics validation opt-in"
```

---

### Task 3: Validate the New Contract End to End

**Files:**
- Modify only if validation exposes a migration defect.

**Interfaces:**
- Consumes: `npm test`, `npm run test:physics`, and `npm run test:all`.
- Produces: command/file-set/runtime receipts proving the new validation contract.

- [ ] **Step 1: Run ordinary validation**

Run: `npm test`

Expected: completes without executing `tests/physics/**`; elapsed time no longer contains the previous multi-minute settle suites. Pre-existing unrelated architecture/session failures may remain, but no new failure is accepted.

- [ ] **Step 2: Run physics validation**

Run: `npm run test:physics`

Expected: every physics file executes with the long timeout. All assertions pass unless a pre-existing physics failure is independently reproduced from the branch base.

- [ ] **Step 3: Run combined validation and typecheck**

Run: `npm run test:all`

Expected: ordinary and physics files are both collected in one run. Existing unrelated failures remain distinguishable; no selection gap or duplicate file execution occurs.

Run: `npm run typecheck`

Expected: PASS.

- [ ] **Step 4: Record conformance**

Append the command outputs, selected file counts, elapsed times, and any independently reproduced pre-existing failures to the foundation record at `/tmp/visualproof-foundation-20260711-opt-in-physics-tests.md` under `<conformance>`. Do not alter its pre-action sections.

- [ ] **Step 5: Close validation cleanly**

If validation exposes a migration defect, return it to Task 2, change only the implicated configuration or migrated test file, rerun Task 2 Steps 5–6, and include that file in Task 2's commit. Task 3 creates no compatibility layer, skipped assertion, reduced budget, or empty commit.
