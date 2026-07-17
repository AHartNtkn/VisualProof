# Single-owner dossier transition implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the duplicated outgoing culture sheet so a culture switch paints exactly one dossier while retaining the approved incoming-sheet motion.

**Architecture:** `.active-dossier` becomes the sole paper and content owner. Culture and progression changes update it synchronously, then `FolioMotion.dossier` applies the existing 260 ms rigid translation/shadow timeline; no clone, pose capture, stacking, or deferred removal remains.

**Tech Stack:** TypeScript, CSS keyframes, Vitest, Playwright, Vite.

## Global Constraints

- The active page still shows both culture-selection tabs.
- Preserve the existing dossier duration, easing, rigid translation, and shadow interpolation.
- Do not change cover, inspection, restriction, packet, reset, responsive geometry, or clipping behavior.
- Do not touch physics code or run physics tests.
- Do not retain compatibility selectors or a dormant outgoing-clone path.

---

### Task 1: Replace outgoing-sheet ownership with one active dossier

**Files:**
- Modify: `tests/review/excavation-folio-browser.test.ts`
- Modify: `review/excavation-folio/main.ts`
- Modify: `review/excavation-folio/folio.css`
- Modify: `review/excavation-folio/motion.css`

**Interfaces:**
- Consumes: `FolioMotion.dossier(target: CultureId, mode: MotionMode): Promise<void>` and the existing `.active-dossier` projection.
- Produces: one `.active-dossier` element, zero `.outgoing-dossier` elements, and unchanged `data-motion-dossier-*` descriptors.

- [ ] **Step 1: Replace the stationary-outgoing test with a failing single-owner contract**

In `tests/review/excavation-folio-browser.test.ts`, replace the test named
`moves a rigid incoming dossier over a stationary outgoing sheet` with a served
browser test that clicks Myratic and samples every active frame:

```ts
it('moves one rigid dossier with no outgoing culture paint', async () => {
  const page = await openPage({ width: 1600, height: 1000 })
  try {
    await page.keyboard.press('3')
    await waitForMotionIdle(page)
    const observations = await page
      .locator('.active-dossier [data-culture="myratic"]')
      .evaluate(async (tab) => {
        ;(tab as HTMLButtonElement).click()
        const root = document.querySelector<HTMLElement>('#excavation-folio-demo')
        const active = document.querySelector<HTMLElement>('.active-dossier')
        if (root === null || active === null) throw new Error('Dossier projection missing')
        const frames: Array<{ matrix: number[]; distance: number; sheetCount: number; outgoingCount: number }> = []
        while (root.classList.contains('is-motion-dossier')) {
          const matrix = new DOMMatrixReadOnly(getComputedStyle(active).transform)
          frames.push({
            matrix: [matrix.a, matrix.b, matrix.c, matrix.d],
            distance: Math.hypot(matrix.e, matrix.f),
            sheetCount: document.querySelectorAll('.active-dossier, .outgoing-dossier').length,
            outgoingCount: document.querySelectorAll('.outgoing-dossier').length,
          })
          await new Promise((resolve) => requestAnimationFrame(resolve))
        }
        return {
          frames,
          title: active.querySelector('[data-dossier-title]')?.textContent ?? '',
          tabs: [...active.querySelectorAll('[data-culture]')].map(
            (item) => (item as HTMLElement).dataset.culture,
          ),
        }
      })
    expect(observations.title).toMatch(/Myratic dossier/i)
    expect(observations.tabs).toEqual(['seyric', 'myratic'])
    expect(observations.frames.length).toBeGreaterThan(2)
    expect(observations.frames.every(({ sheetCount }) => sheetCount === 1)).toBe(true)
    expect(observations.frames.every(({ outgoingCount }) => outgoingCount === 0)).toBe(true)
    for (const frame of observations.frames) {
      expect(frame.matrix.slice(0, 4)).toEqual([1, 0, 0, 1])
    }
    for (let index = 1; index < observations.frames.length; index += 1) {
      expect(observations.frames[index]!.distance).toBeLessThanOrEqual(
        observations.frames[index - 1]!.distance + 0.05,
      )
    }
  } finally {
    await page.close()
  }
})
```

- [ ] **Step 2: Replace the rapid identity test with a failing supersession contract**

Replace `preserves the interrupted dossier identity and pose while its replacement enters`
with a test that switches to Myratic, waits 55 ms, switches back to Seyric, and
asserts in the same browser task that `.outgoing-dossier` count is zero,
`.active-dossier` contains the Seyric title and both culture tabs, and the root's
`data-motion-dossier-target` is `seyric`.

- [ ] **Step 3: Run the two tests and verify RED**

Run:

```bash
npm test -- --run tests/review/excavation-folio-browser.test.ts -t "one rigid dossier|supersedes an interrupted dossier"
```

Expected: both tests fail because `.outgoing-dossier` exists during each switch.

- [ ] **Step 4: Delete outgoing-sheet staging and cleanup from the projection**

In `review/excavation-folio/main.ts`:

- delete the `outgoingDossier` calculation in `dispatch`;
- replace each dossier call chained to `.finally(() => outgoingDossier?.remove())`
  with `void motion.dossier(next.culture, next.motion)`;
- delete `stageOutgoingDossier` completely.

The culture and progression cases retain only:

```ts
if (previous.culture !== next.culture) {
  void motion.dossier(next.culture, next.motion)
}
```

- [ ] **Step 5: Delete outgoing-sheet CSS ownership**

In `review/excavation-folio/folio.css`, remove `.outgoing-dossier` from shared
selectors and delete its standalone rule and Myratic filter selector. In
`review/excavation-folio/motion.css`, delete:

```css
.is-motion-dossier .outgoing-dossier {
  z-index: 2;
}
```

Retain the existing `.active-dossier` layout and `dossier-enter` keyframes unchanged.

- [ ] **Step 6: Prove the obsolete production model is absent**

Run:

```bash
rg -n "outgoing-dossier|stageOutgoingDossier|outgoingDossier" review/excavation-folio/main.ts review/excavation-folio/folio.css review/excavation-folio/motion.css
```

Expected: no matches.

- [ ] **Step 7: Run the focused browser contracts and verify GREEN**

Run the Step 3 command again. Expected: both tests pass.

- [ ] **Step 8: Commit the ownership replacement**

```bash
git add review/excavation-folio/main.ts review/excavation-folio/folio.css review/excavation-folio/motion.css tests/review/excavation-folio-browser.test.ts
git commit -m "fix(review): remove outgoing dossier paint"
```

### Task 2: Regenerate evidence and validate the complete folio

**Files:**
- Modify: `review/excavation-folio/evidence/*.png`
- Modify: `review/excavation-folio/evidence/motion-trace.json`
- Modify if the capture contract requires it: `scripts/capture-excavation-folio.mjs`

**Interfaces:**
- Consumes: the single-owner dossier transition from Task 1 and the canonical capture command.
- Produces: checked-in screenshots and timeline evidence generated from the final served implementation.

- [ ] **Step 1: Regenerate canonical evidence**

Run:

```bash
node scripts/capture-excavation-folio.mjs
```

Expected: exit 0; screenshots and `motion-trace.json` are regenerated.

- [ ] **Step 2: Inspect the immediate Myratic switch state**

Use served Chromium to pause the dossier animation at an early frame and confirm
that no Seyric notes, duplicate tabs, dark doubled ruled lines, or second dossier
sheet are visible. This is realistic visual evidence, not a snapshot-only assertion.

- [ ] **Step 3: Run complete focused validation**

```bash
npm test -- --run tests/review/excavation-folio-model.test.ts tests/review/excavation-folio-motion.test.ts tests/review/excavation-folio-browser.test.ts
npm run typecheck
npx vite build review/excavation-folio --outDir /tmp/cursebreaker-folio-single-owner-build --emptyOutDir
git diff --check
```

Expected: all focused tests pass; typecheck, build, and diff check exit 0.

- [ ] **Step 4: Request independent review**

The reviewer must check that the outgoing model is absent, both culture tabs remain
on the active page, the dark texture/protrusion bug is structurally impossible,
and unrelated folio motion is unchanged. Fix all Critical or Important findings.

- [ ] **Step 5: Commit regenerated evidence**

```bash
git add review/excavation-folio/evidence scripts/capture-excavation-folio.mjs
git commit -m "test(review): capture single-owner dossier transition"
```

- [ ] **Step 6: Append foundation conformance and serve the demo**

Append `<conformance>` to
`/tmp/cursebreaker-folio-outgoing-decoration-20260717-foundation.md`, then serve
the final committed branch at `/review/excavation-folio/` and verify HTTP 200.
