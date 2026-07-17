# Continuous Folio Motion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the excavation folio's stop-start phase scheduler with one continuous timeline per physical action, restore the full visible cover hit target, and give record graphics correct clipping owners.

**Architecture:** `FolioMotion` becomes a lifecycle coordinator that installs one channel descriptor and waits once. CSS keyframes own each complete visual trajectory. Record source geometry/status and generation-safe cleanup remain, while phase datasets/selectors/tests are deleted. Runtime validation measures real pointer targets, frame progress, rigid sheet transforms, and settled clipping.

**Tech Stack:** TypeScript, CSS keyframes, Vitest, Playwright served-browser tests, Vite evidence capture.

## Global Constraints

- Keep `data-cover-control` as the only cover interaction authority; add no control.
- Full actions use one timeline; reduced actions use one 90 ms non-spatial timeline; paused actions schedule no motion.
- Dossier sheets use translation-only rigid transforms with no scale, skew, rotation, reversal, or tab-specific motion.
- Record inspection/return must retain exact captured source geometry and physical status.
- Status tabs and bands may protrude; record-face, mount, and guard contents remain contained.
- Released Myratic guard, tie, and fastener leave no settled visible residue.
- Remove the phase model completely; do not retain compatibility datasets, selectors, tests, or trace fields.
- Do not modify the central lens, assets, puzzle behavior, feedback, or proof physics.
- Do not run physics tests.

---

### Task 1: Replace the Motion Coordinator Representation

**Files:**
- Modify: `tests/review/excavation-folio-motion.test.ts`
- Modify: `review/excavation-folio/motion.ts`

**Interfaces:**
- Consumes: existing `MotionClock.wait(milliseconds, signal)` and public `FolioMotion` methods.
- Produces: one descriptor per active channel: `is-motion-<channel>`, `data-motion-<channel>-target`, `data-motion-<channel>-kind`, and `--motion-<channel>-duration`.

- [ ] **Step 1: Rewrite coordinator tests to require one wait and no phases**

Extend the fake root with a style recorder:

```ts
class FakeStyle {
  readonly values = new Map<string, string>()
  setProperty(name: string, value: string): void { this.values.set(name, value) }
  removeProperty(name: string): string {
    const value = this.values.get(name) ?? ''
    this.values.delete(name)
    return value
  }
}
```

Replace phase assertions with descriptor assertions. The cover test must require:

```ts
const complete = motion.cover('open', 'full')
expect(clock.size).toBe(1)
expect(dataset.motionCoverTarget).toBe('open')
expect(dataset.motionCoverKind).toBe('open')
expect(style.values.get('--motion-cover-duration')).toBe('380ms')
expect(Object.keys(dataset).some((key) => key.endsWith('Phase'))).toBe(false)
await advance(clock)
await complete
expect(classList.contains('is-motion-cover')).toBe(false)
```

Add equivalent kind assertions for dossier `replace`, record `inspect`/`return`, restriction `refuse`, and packet `release`. Reduced motion must use kind `reduced`, duration `90ms`, and one wait. Paused motion must use no wait or transient descriptor. Replacement and `settleAll()` tests must still prove newest-owner cleanup.

- [ ] **Step 2: Run the coordinator tests and verify RED**

Run:

```bash
npm test -- --run tests/review/excavation-folio-motion.test.ts
```

Expected: FAIL because the incumbent coordinator creates phase datasets and schedules several waits.

- [ ] **Step 3: Implement the single-timeline coordinator**

In `motion.ts`, replace `phaseDurations`, phase arrays, and the phase loop with:

```ts
const fullDurations: Record<MotionChannel, number> = {
  cover: 380,
  dossier: 260,
  record: 340,
  restriction: 320,
  packet: 480,
}
const reducedDuration = 90

private async run(
  channel: MotionChannel,
  target: string,
  kind: string,
  mode: MotionMode,
): Promise<void> {
  this.cancel(channel)
  if (mode === 'paused') return
  const duration = mode === 'reduced' ? reducedDuration : fullDurations[channel]
  const controller = new AbortController()
  const active = { controller, cancel: () => controller.abort() }
  this.active.set(channel, active)
  this.root.classList.add(this.className(channel))
  this.root.dataset[this.targetKey(channel)] = target
  this.root.dataset[this.kindKey(channel)] = mode === 'reduced' ? 'reduced' : kind
  this.root.style.setProperty(this.durationProperty(channel), `${duration}ms`)
  try {
    await this.clock.wait(duration, controller.signal)
  } finally {
    if (this.active.get(channel) === active) this.cleanup(channel)
  }
}
```

Map public methods to kinds: cover target (`open`/`closed`) maps to `open`/`close`; dossier maps to `replace`; record uses `inspect`/`return`; restriction uses `refuse`; packet uses `release`. Cleanup removes target, kind, duration property, and class. Delete `phaseKey` and all phase concepts.

- [ ] **Step 4: Run the coordinator tests and verify GREEN**

Run the same Vitest command. Expected: all motion tests PASS with one pending wait per active non-paused action.

- [ ] **Step 5: Commit the coordinator replacement**

```bash
git add review/excavation-folio/motion.ts tests/review/excavation-folio-motion.test.ts
git commit -m "refactor(review): replace folio motion phases"
```

---

### Task 2: Replace Phase CSS with Continuous Physical Timelines

**Files:**
- Modify: `tests/review/excavation-folio-browser.test.ts`
- Modify: `review/excavation-folio/motion.css`
- Modify: `review/excavation-folio/folio.css`
- Modify: `review/excavation-folio/main.ts`

**Interfaces:**
- Consumes: Task 1 descriptor classes, kinds, targets, and duration properties.
- Produces: complete CSS keyframe trajectories and the narrowed source geometry variables `--record-source-x`, `--record-source-y`, `--record-source-scale-x`, and `--record-source-scale-y`.

- [ ] **Step 1: Add RED browser tests for continuous record progress**

Replace phase assertions in return/preference tests with `data-motion-record-kind="return"` and active-class checks. Add a served test that clicks a record, samples `getBoundingClientRect()` every animation frame while `is-motion-record` is present, and asserts:

```ts
expect(frames.length).toBeGreaterThan(10)
const middle = frames.slice(2, -3)
for (let index = 1; index < middle.length; index += 1) {
  expect(middle[index]!.distanceToDestination)
    .toBeLessThan(middle[index - 1]!.distanceToDestination - 0.1)
}
```

The sampled distance is `rectDistance(frame, destination)`. This must catch the incumbent 135 ms stationary release and later rests.

- [ ] **Step 2: Add RED browser tests for a rigid dossier timeline**

Click the Myratic tab and sample the active incoming dossier each frame. Parse the CSS 2D matrix and assert `a=1`, `b=0`, `c=0`, `d=1` within `0.001`; only translation components may change. Assert distance to settled translation decreases monotonically and never reverses. Assert outgoing sheet geometry/transform remains unchanged and its z-index stays below active throughout.

- [ ] **Step 3: Add RED browser tests for the full cover edge and clipping**

After opening at 1600×1000, inspect points `x=4`, `20`, and `40` at the vertical center of the visible edge. Each `elementFromPoint` result must be `[data-cover-spine]` or its descendant; click each point in a fresh page and require `data-cover="closed"`.

For the released Myratic record, require guard computed opacity `0`, visibility `hidden`, and no intersection with the record; require tie/fastener to be hidden through their guard. Require the available `::after` tab's calculated right edge to exceed the record's right edge while remaining visible. Require `.record-face`, `.evidence-mount`, and `.record-guard` computed overflow to be `hidden`.

- [ ] **Step 4: Run focused browser tests and verify RED**

Run:

```bash
npm test -- --run tests/review/excavation-folio-browser.test.ts -t "continuous|rigid dossier|visible cover edge|Myratic release|clipping owner"
```

Expected: FAIL for stationary record frames, rotating/reversing dossier motion, uncovered edge points, released guard residue, and clipped status tab.

- [ ] **Step 5: Replace `motion.css` completely**

Delete every transition and `[data-*-phase]` selector. Define one keyframe family per kind:

```css
@keyframes record-inspect {
  from {
    transform: translate(var(--record-source-x), var(--record-source-y))
      scale(var(--record-source-scale-x), var(--record-source-scale-y))
      rotate(var(--record-status-rotation));
    box-shadow: 0.18rem 0.28rem 0.38rem rgb(12 7 9 / 30%);
  }
  to {
    transform: rotate(var(--record-status-rotation));
    box-shadow: 1.3rem 2rem 2.8rem rgb(12 7 9 / 58%);
  }
}

.is-motion-record[data-motion-record-kind="inspect"] .inspection-record {
  animation: record-inspect var(--motion-record-duration)
    cubic-bezier(0.2, 0.72, 0.25, 1) both;
}
```

Define `record-return` as the inverse, `cover-open`/`cover-close` between exact base poses, and `dossier-enter` from `translate(0.9rem, -0.3rem)` to `translate(0, 0)` with shadow interpolation only. During dossier motion set `.active-dossier { z-index: 5 }` and `.outgoing-dossier { z-index: 2; transform:none }`.

Define one `restricted-refusal` timeline for the record and one synchronized sleeve timeline with resistance/rebound keyframes. Define synchronized packet guard/tie/fastener/face timelines under kind `release`. Define one `reduced-depth` non-spatial brightness/shadow animation applied by any channel kind `reduced`.

- [ ] **Step 6: Narrow inspection geometry staging**

In `stageInspectionSource`, retain only source translation and scale variables. Delete lift/travel/return/lower variables because CSS now interpolates exact endpoints in one timeline.

- [ ] **Step 7: Correct hit and clipping ownership**

In `folio.css`:

```css
.cover-spine-hit {
  left: -1.7rem;
  width: 3.05rem;
  border: 0;
  background: transparent;
  box-shadow: none;
}
.cover-spine-hit::after {
  position: absolute;
  inset: 0 0 0 auto;
  width: 1.35rem;
  border-inline: 1px solid #6d5a47;
  background: linear-gradient(90deg, #161217, #51443a 48%, #1c171b);
  box-shadow: 0.3rem 0 0.5rem rgb(4 2 7 / 45%);
  content: "";
}
.artifact-record { overflow: visible; }
.record-face,
.evidence-mount,
.record-guard { overflow: hidden; }
.restricted-packet[data-packet-state="released"] .record-guard {
  visibility: hidden;
  opacity: 0;
  transform: translateX(-110%);
}
.is-motion-packet .restricted-packet .record-guard { visibility: visible; }
```

Keep pointer events on the expanded descendant only while open. Do not add a handler or control. Ensure packet animation selectors override settled opacity/visibility while active.

- [ ] **Step 8: Run browser tests and verify GREEN**

Run the focused command, then the whole browser file:

```bash
npm test -- --run tests/review/excavation-folio-browser.test.ts
```

Expected: all browser tests PASS after obsolete phase assertions are migrated.

- [ ] **Step 9: Commit continuous rendering and ownership**

```bash
git add review/excavation-folio/main.ts review/excavation-folio/motion.css review/excavation-folio/folio.css tests/review/excavation-folio-browser.test.ts
git commit -m "fix(review): make folio motion continuous"
```

---

### Task 3: Replace Phase Evidence with Timeline Evidence

**Files:**
- Modify: `scripts/capture-excavation-folio.mjs`
- Modify: `tests/review/excavation-folio-browser.test.ts`
- Regenerate: `review/excavation-folio/evidence/motion-trace.json`
- Regenerate: `review/excavation-folio/evidence/*.png`

**Interfaces:**
- Consumes: active classes, timeline kinds, and CSS animation state from Tasks 1–2.
- Produces: `motion-trace.json` with `timelines`, `reduced`, and `geometry`; no `phases` field.

- [ ] **Step 1: Write RED trace-schema assertions**

Change the evidence test to require:

```ts
expect(trace).not.toHaveProperty('phases')
expect(Object.keys(trace.timelines)).toEqual([
  'cover', 'dossier', 'record', 'restriction', 'packet',
])
for (const timeline of Object.values(trace.timelines)) {
  expect(timeline.kind).not.toBe('')
  expect(timeline.durationMs).toBeGreaterThan(0)
  expect(timeline.frames.length).toBeGreaterThanOrEqual(3)
  expect(new Set(timeline.frames.map(visualSignature)).size).toBeGreaterThan(1)
}
```

Require dossier frames to remain rigid and record frames to approach their target monotonically. Require reduced observations to report kind `reduced` and non-spatial visual change.

- [ ] **Step 2: Run the evidence contract and verify RED**

Run:

```bash
npm test -- --run tests/review/excavation-folio-browser.test.ts -t "timeline evidence"
```

Expected: FAIL because the current trace uses `phases`.

- [ ] **Step 3: Replace the capture schema and sampler**

Delete `observePhases`, phase selectors, the zero-duration trace style, and phase-specific visual selection. Implement `observeTimeline(page, channel, trigger)`:

1. capture `settled-before`;
2. trigger and wait for `is-motion-<channel>`;
3. read kind and parsed duration property;
4. sample every animation frame while active;
5. retain first, midpoint, and final active samples;
6. capture `settled-after`; and
7. return `{ kind, durationMs, frames }`.

For dossier observations sample `.active-dossier`; for all other channels retain the current physical-subject selectors. Replace `phases` with `timelines`. Update the restriction screenshot wait to the active restriction kind and allow its running animation for that capture; all settled screenshots continue disabling animations.

- [ ] **Step 4: Regenerate canonical evidence**

Run:

```bash
node scripts/capture-excavation-folio.mjs
```

Expected: exit 0; all canonical PNGs and `motion-trace.json` regenerated.

- [ ] **Step 5: Run the trace and browser contracts and verify GREEN**

```bash
npm test -- --run tests/review/excavation-folio-browser.test.ts
```

Expected: all browser and evidence assertions PASS.

- [ ] **Step 6: Commit evidence migration**

```bash
git add scripts/capture-excavation-folio.mjs tests/review/excavation-folio-browser.test.ts review/excavation-folio/evidence
git commit -m "test(review): record continuous folio timelines"
```

---

### Task 4: Final Validation and Conformance

**Files:**
- Modify outside repository: `/tmp/cursebreaker-folio-motion-system-refinement-20260716-foundation.md`
- Verify only: all committed files from Tasks 1–3

**Interfaces:**
- Consumes: complete reconstructed motion/clipping system.
- Produces: authoritative verification, independent review, and a served demo.

- [ ] **Step 1: Run the focused non-physics suite**

```bash
npm test -- --run tests/review/excavation-folio-model.test.ts tests/review/excavation-folio-motion.test.ts tests/review/excavation-folio-browser.test.ts
npm run typecheck
npx vite build review/excavation-folio --outDir /tmp/cursebreaker-folio-continuous-build --emptyOutDir
git diff --check
```

Expected: all focused tests, typecheck, build, and whitespace validation PASS. Do not run `test:physics`.

- [ ] **Step 2: Inspect regenerated visuals and runtime trace**

Inspect Seyric mixed, Seyric inspection, Myratic released, and motion trace. Confirm no guard residue, cutoff tab, sheet distortion, or source/destination flash. Re-run capture if a transient image decode fails; do not add retries or weaken validation.

- [ ] **Step 3: Request independent review**

Provide the reviewer the approved design, foundation record, commit range from `45cb577`, and explicit checks for phase removal, continuous frame progression, real cover hit area, rigid dossier motion, clipping ownership, unrelated-change preservation, and no physics tests. Address every Critical or Important finding through a new RED/GREEN cycle.

- [ ] **Step 4: Append foundation conformance**

Record replaced structures, migrated dependents, exact validation results, review outcome, and evidence that no phase model or settled packet residue remains.

- [ ] **Step 5: Confirm narrow status and launch the demo**

Verify unrelated dirty assets/spec work remains untouched. Start:

```bash
npx vite --host 0.0.0.0 --port 4173
```

Confirm `http://127.0.0.1:4173/review/excavation-folio/` returns HTTP 200 and provide the review URL.
