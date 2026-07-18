# Fix Electron App Launch Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `npm run app` launch the visible Electron game through its real preload instead of serving an unusable standalone Vite renderer.

**Architecture:** Vite remains the renderer compiler inside `build:desktop`; Electron remains the only playable runtime. The package contract selects one `app` launcher, the renderer bootstrap converts startup rejection into an accessible diagnostic surface, and a real Electron smoke validates archive-to-puzzle entry through preload and IPC.

**Tech Stack:** npm scripts, Vite 5, Electron 43, TypeScript 5.5, Vitest 2, Playwright Electron.

## Global Constraints

- `npm run app` is the sole playable development launch command.
- Do not add a browser/localStorage fallback for the Electron preload API.
- Preserve Electron context isolation and disabled renderer Node integration.
- Use an isolated temporary Electron user-data directory in runtime validation.
- Do not run the proof-physics battery.

---

### Task 1: Select one authoritative desktop launcher

**Files:**
- Modify: `tests/platform/package-contract.test.ts`
- Modify: `package.json`

**Interfaces:**
- Consumes: existing `build:desktop` script and Electron package entry `dist-electron/main.js`.
- Produces: package script `app = "npm run build:desktop && electron ."` with no `desktop:dev` competitor.

- [ ] **Step 1: Write the failing package-contract assertions**

Replace the first test's script assertions with exact launcher ownership:

```ts
expect(packageDocument.scripts).toMatchObject({
  app: 'npm run build:desktop && electron .',
  'build:renderer': expect.any(String),
  'build:electron': expect.any(String),
  'build:desktop': expect.any(String),
  'package:linux:dir': expect.any(String),
  'package:linux': expect.any(String),
})
expect(packageDocument.scripts).not.toHaveProperty('desktop:dev')
expect(packageDocument.scripts.app).not.toMatch(/^vite(?:\s|$)/)
```

- [ ] **Step 2: Run the test and verify RED**

Run:

```bash
npx vitest run tests/platform/package-contract.test.ts
```

Expected: FAIL because `app` is `vite app` and `desktop:dev` still exists.

- [ ] **Step 3: Implement the sole launcher**

Set:

```json
"app": "npm run build:desktop && electron ."
```

Delete the `desktop:dev` property. Keep `build:renderer`, `build:electron`, `build:desktop`, and Linux packaging unchanged.

- [ ] **Step 4: Run focused GREEN validation**

Run:

```bash
npx vitest run tests/platform/package-contract.test.ts
npm run build:desktop
```

Expected: 3 tests pass and both renderer/Electron builds succeed.

- [ ] **Step 5: Commit**

```bash
git add package.json tests/platform/package-contract.test.ts
git commit -m "fix: launch app through Electron"
```

### Task 2: Make renderer startup failure observable

**Files:**
- Modify: `tests/game/built-renderer-csp-smoke.test.ts`
- Modify: `app/main.ts`
- Modify: `app/style.css`

**Interfaces:**
- Consumes: `mountCursebreaker(...)` and the real/fake `cursebreakerPlatform` preload boundary.
- Produces: `.curse-launch-failure[role="alert"]` after any rejected initial boot promise.

- [ ] **Step 1: Add the failing built-renderer failure test**

Parameterize the test helper so its injected platform can reject `loadSave` with `new Error('fixture load failure')`. Add:

```ts
it('renders an accessible diagnostic instead of an empty black host when startup fails', async () => {
  const { page, pageErrors } = await openBuiltRenderer('load-error')
  try {
    const alert = page.locator('.curse-launch-failure[role="alert"]')
    await expect.poll(() => alert.count()).toBe(1)
    await expect.poll(() => alert.textContent()).toContain('Cursebreaker could not start')
    await expect.poll(() => page.locator('#cursebreaker').getAttribute('data-launch-state'))
      .toBe('failed')
    expect(pageErrors).toEqual([])
  } finally {
    await page.close()
  }
})
```

- [ ] **Step 2: Run the test and verify RED**

Run:

```bash
npx vitest run tests/game/built-renderer-csp-smoke.test.ts
```

Expected: FAIL because the rejected boot remains an unhandled page error and no alert exists.

- [ ] **Step 3: Add the minimal bootstrap rejection boundary**

In `app/main.ts`, add a focused `showLaunchFailure(error: unknown)` that logs `Failed to start Cursebreaker`, resolves the existing `#cursebreaker` host, sets `data-launch-state="failed"`, clears it, and appends a `section.curse-launch-failure` with `role="alert"`, heading text `Cursebreaker could not start`, and concise close-and-retry copy. Replace `void boot()` with:

```ts
void boot().catch(showLaunchFailure)
```

Add CSS that centers the diagnostic within the existing dark host using only the named class; do not add images, lore, controls, or a preload fallback.

- [ ] **Step 4: Run focused GREEN validation**

Run:

```bash
npx vitest run tests/game/built-renderer-csp-smoke.test.ts tests/platform/package-contract.test.ts
npm run typecheck
git diff --check
```

Expected: 5 tests pass, typecheck passes, and no diff errors occur.

- [ ] **Step 5: Commit**

```bash
git add app/main.ts app/style.css tests/game/built-renderer-csp-smoke.test.ts
git commit -m "fix: expose renderer launch failures"
```

### Task 3: Prove the exact command is playable

**Files:**
- Append outside repository: `/tmp/cursebreaker-black-screen-7XBM7O/foundation.md`

**Interfaces:**
- Consumes: the built `app` script, Electron main/preload IPC, and opening archive catalog.
- Produces: realistic launch evidence for the exact user command.

- [ ] **Step 1: Run complete focused validation**

Run:

```bash
npx vitest run tests/platform tests/game/built-renderer-csp-smoke.test.ts tests/game/authoritative-runtime-browser.test.ts
npm run assets:validate
npm run typecheck
npm run build:desktop
git diff --check
```

Expected: every selected non-physics test and build check passes.

- [ ] **Step 2: Launch the exact command with isolated desktop state**

Reserve local debugging port `9333` only after proving it is unused, create an
isolated directory, then run:

```bash
launch_data_dir=$(mktemp -d /tmp/cursebreaker-app-smoke-XXXXXX)
debug_port=9333
if ss -ltn | rg -q ":${debug_port} "; then exit 1; fi
npm run app -- --user-data-dir="$launch_data_dir" --remote-debugging-port="$debug_port"
```

Connect Playwright to that port. Assert one Electron page, no page errors, `.curse-production-environment[data-mode="archive"]`, at least one `.curse-folio-record[data-status="unlocked"]`, and a nonempty `.curse-production-lens` bounding box.

- [ ] **Step 3: Enter the first unlocked puzzle**

Click the first `.curse-folio-record[data-status="unlocked"]`, then assert `.curse-production-environment[data-mode="puzzle"]`, `.game-proof-surface`, and `.curse-production-timeline-control` are visible. Capture one screenshot in the scratch directory, inspect it, request exit through the real preload, and verify the Electron process exits.

- [ ] **Step 4: Append conformance**

Append `<conformance>` to the foundation record with the root cause, displaced command removed, tests/builds, exact-command launch evidence, screenshot path, startup console result, archive-to-puzzle result, and explicit statement that physics was not run.
