# Passive Guidance and Persistent Timeline Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the input-blocking teacher model with optional paged edge guidance, teach the first puzzle’s real basic interactions, and keep one inactive-or-active timeline slider mounted through every game mode while completing the mandatory archive/puzzle/pause/completion presentation integration.

**Architecture:** `GameControllerState` owns a non-transient `guidance` projection and puzzle-qualified `deliveredGuidance` identities; controller transitions deliver, page, clear, and save guidance atomically. `CursebreakerRuntime` mounts one `GamePresentationView` and one `TimelineLever` for its full lifetime, updating each from controller projections rather than mounting puzzle-only UI. The first visual gate uses temporary, uncommitted CSS candidates driven by the real runtime and is removed after selection.

**Tech Stack:** TypeScript, framework-free DOM/CSS, Vitest, Playwright Chromium, Vite, Electron build tooling.

## Global Constraints

- Preserve the approved desk, full-height lens, folio, substrate, gasket, timeline artwork, folio motion, and dark-neon proof palette.
- Do not change proof physics or run the dedicated physics battery.
- Do not launch Electron or any visible GUI; browser validation and capture are headless.
- Guidance never captures focus, blocks proof/timeline/folio input, takes Escape precedence, or requires acknowledgement.
- Each guidance page is one trimmed nonempty paragraph; only non-final pages expose one optional `Next` action.
- The first puzzle teaches hover highlighting, selection, deselection, empty-field clearing, and only on its final page the completing elimination command.
- The complete timeline slider retains one DOM identity in every mode and dispatches cursor changes only for an active puzzle with no higher-priority input owner.
- Completion has exactly one action and no rank, score, par, proof recording, review, replay, continue, or restart control.
- Preserve user changes and commit only files intentionally completed by each task.

---

## File and responsibility map

- `src/game/types.ts`: authored intervention pages and delivery identity.
- `src/game/catalog.ts`: page validation, completion-page cardinality, immutable snapshot, and logical fingerprint authority.
- `src/game/teaching.ts`: pure semantic trigger matching that returns passive guidance candidates.
- `src/game/content/opening.ts`: shipped tutorial and authored guidance pages.
- `src/game/controller-state.ts`: active guidance/page and delivered-guidance state.
- `src/game/controller.ts`: atomic delivery, page advancement, relevance clearing, Escape/input precedence, and completion.
- `src/game/save.ts`: strict save version and exact guidance/page restoration.
- `src/game/interface/timeline-lever.ts`: persistent active/inactive timeline projection and input semantics.
- `src/game/interface/game-presentation-view.ts`: completion, pause/settings, and passive guidance DOM only.
- `src/game/interface/game-presentation-view.css`: selected production presentation styling; temporary review variants remain uncommitted until selection.
- `src/game/interface/mount.ts`: sole runtime reconciliation owner for proof, folio, presentation, persistent timeline, persistence, and effects.
- `tests/game/*.test.ts`: direct domain/controller/save/DOM/browser authority; absence tests for the displaced model are deleted or inverted.

---

### Task 1: Replace single-string teacher content with validated pages

**Files:**
- Modify: `tests/game/catalog.test.ts`
- Modify: `tests/game/teaching.test.ts`
- Modify: `tests/game/opening-content.test.ts`
- Modify: `tests/game/catalog-fixture.ts`
- Modify: `tests/game/controller-fixture.ts`
- Modify: `tests/game/runtime-catalog-fixture.ts`
- Modify: `src/game/types.ts`
- Modify: `src/game/catalog.ts`
- Modify: `src/game/teaching.ts`
- Modify: `src/game/content/opening.ts`

**Interfaces:**
- Consumes: existing `TeacherTrigger`, `PuzzleDefinition`, catalog witness validation, and exact recognized-state matching.
- Produces: `TeacherIntervention.pages: readonly string[]`, `GuidanceDeliveryIdentity`, `guidanceDeliveryIdentity(puzzle, intervention)`, `isGuidanceDelivered(delivered, identity)`, and `guidanceInterventionsFor(puzzle, signal, delivered)`.

- [ ] **Step 1: Write failing domain and content tests**

Add catalog cases that reject `pages: []`, `pages: ['']`, leading/trailing whitespace, embedded `\n`, and completion interventions with more than one page. Assert changing page order or text changes the puzzle fingerprint. Replace teaching expectations with passive candidates and delivered identities. Pin the first puzzle’s ordered pages:

```ts
expect(puzzle('two-veils').teacher[0]!.pages).toEqual([
  expect.stringMatching(/move|hover|highlight/i),
  expect.stringMatching(/click|select/i),
  expect.stringMatching(/again|empty|clear/i),
  expect.stringMatching(/Eliminate the double cut|Delete|Backspace/i),
])
expect(puzzle('two-veils').teacher[0]!.pages.slice(0, -1).join(' '))
  .not.toMatch(/Eliminate the double cut|Delete|Backspace/i)
```

- [ ] **Step 2: Run the focused tests and verify RED**

Run:

```bash
npm test -- --run tests/game/catalog.test.ts tests/game/teaching.test.ts tests/game/opening-content.test.ts
```

Expected: type/test failures because fixtures and production interventions still expose `text` and page validation does not exist.

- [ ] **Step 3: Implement the page model and pure matcher**

Replace the single text field and acknowledgement identity helpers:

```ts
type TeacherInterventionBase = {
  readonly id: string
  readonly performance?: PerformanceId
  readonly pages: readonly string[]
  readonly repeat: 'once' | 'repeatable'
}

export type GuidanceDeliveryIdentity = {
  readonly puzzle: PuzzleId
  readonly intervention: string
}
```

Validate every page with `nonBlank`, reject `page.includes('\n')`, require exactly one page for completion triggers, and include ordered pages in fingerprint input. Rename the matcher to return `{ identity, intervention }` without modal/nonmodal presentation intents. Convert every fixture and shipped intervention to `pages`.

Author the first puzzle’s four direct interface paragraphs from actual production behavior. The final paragraph names the discovered “Eliminate the double cut” action and Delete/Backspace alternative; earlier pages do not name a logical proof move.

- [ ] **Step 4: Run the focused tests and verify GREEN**

Run the Step 2 command. Expected: all three files pass with no warnings.

- [ ] **Step 5: Commit the completed domain slice**

```bash
git add src/game/types.ts src/game/catalog.ts src/game/teaching.ts src/game/content/opening.ts tests/game/catalog.test.ts tests/game/teaching.test.ts tests/game/opening-content.test.ts tests/game/catalog-fixture.ts tests/game/controller-fixture.ts tests/game/runtime-catalog-fixture.ts
git commit -m "feat: model authored guidance as pages"
```

---

### Task 2: Rebuild controller and save ownership around passive guidance

**Files:**
- Modify: `tests/game/controller.test.ts`
- Modify: `tests/game/save.test.ts`
- Modify: `src/game/controller-state.ts`
- Modify: `src/game/controller.ts`
- Modify: `src/game/save.ts`

**Interfaces:**
- Consumes: `guidanceInterventionsFor`, `GuidanceDeliveryIdentity`, active `GameSession`, and catalog-authored interventions.
- Produces: `ActiveGuidance { identity, intervention, page }`, `GameControllerState.guidance`, `GameControllerState.deliveredGuidance`, and `GameAction { kind: 'advanceGuidancePage' }`.

- [ ] **Step 1: Replace controller tests that assert teacher transients**

Write tests proving selection atomically creates page zero and records once-only delivery, `advanceGuidancePage` changes only the page, the last page is a no-op, Escape opens pause while guidance remains, the first legal proof step clears opening guidance, exact recognized-unwinnable state replaces it, and rewind clears the recognized note. Delete tests and fixture calls for `openTeacher`, `acknowledgeTeacher`, and `closeTeacher`.

Use state assertions shaped as:

```ts
expect(state.guidance).toMatchObject({
  identity: { puzzle: FIRST, intervention: SHARED_TEACHER_ID },
  page: 0,
})
expect(state.deliveredGuidance).toContainEqual(state.guidance!.identity)
expect(transition(state, { kind: 'escape' }).state).toMatchObject({
  guidance: state.guidance,
  transient: { kind: 'pause', presentation: 'menu' },
})
```

- [ ] **Step 2: Replace save tests with delivery and exact-page restoration tests**

Require save version `4`, root fields `deliveredGuidance` and `guidance`, strict puzzle/intervention/page validation, exact round-trip of page index, rejection of repeatable identities in delivered state, and rejection of guidance whose puzzle does not match the active puzzle or whose page is out of range. Delete `acknowledgedTeachers` compatibility expectations; version 3 must be rejected rather than adapted.

- [ ] **Step 3: Run controller/save tests and verify RED**

```bash
npm test -- --run tests/game/controller.test.ts tests/game/save.test.ts
```

Expected: failures because state, reducer, and save still expose the acknowledgement/transient model.

- [ ] **Step 4: Implement atomic guidance transitions**

Define:

```ts
export type ActiveGuidance = {
  readonly identity: GuidanceDeliveryIdentity
  readonly intervention: TeacherIntervention
  readonly page: number
}
```

Remove teacher from `GameTransient` and delete the three teacher actions. On `selectPuzzle`, derive opening guidance and delivery in the same returned state. On `applyStep`, clear opening guidance before matching the resulting diagram; if completed, clear guidance; otherwise deliver an exact recognized note. On `moveTimeline`, recompute recognized relevance and keep only applicable repeatable guidance. `advanceGuidancePage` increments only below `pages.length - 1`. Remove teacher-specific proof/timeline/folio input gates.

Prepared motion commits must copy `guidance` and `deliveredGuidance` from the
authoritative precomputed transition alongside its timeline/completion fields;
delete runtime follow-up teacher dispatches so animation cannot split proof and
guidance into separate saves.

- [ ] **Step 5: Implement strict save version 4**

Encode and decode `deliveredGuidance` plus active `{ puzzle, intervention, page }` guidance. Resolve saved identities through the active catalog, validate once-only delivery, require active guidance only in puzzle mode for the active puzzle, and reconstruct its authored intervention from the catalog. Keep per-puzzle timeline replay validation unchanged.

- [ ] **Step 6: Run controller/save tests and verify GREEN**

Run the Step 3 command. Expected: both files pass.

- [ ] **Step 7: Commit controller/save replacement**

```bash
git add src/game/controller-state.ts src/game/controller.ts src/game/save.ts tests/game/controller.test.ts tests/game/save.test.ts
git commit -m "feat: deliver passive guidance atomically"
```

---

### Task 3: Make the timeline one persistent active-or-inactive instrument

**Files:**
- Modify: `tests/game/timeline-lever.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`
- Modify: `tests/game/authoritative-runtime-fixture.ts`
- Modify: `src/game/interface/timeline-lever.ts`
- Modify: `src/game/interface/lens-environment.css`
- Modify: `src/game/interface/mount.ts`

**Interfaces:**
- Consumes: active `GameTimeline | null`, `CompletionReceipt | null`, and runtime timeline-input predicate.
- Produces: `TimelineLeverProjection { kind: 'active'; timeline: GameTimeline } | { kind: 'inactive'; position: 'home' | 'complete'; moves: number }` and `MountedTimelineLever.update(projection)`.

- [ ] **Step 1: Write failing persistent-instrument unit tests**

Mount once with an inactive-home projection and assert role `slider`, `aria-disabled="true"`, `tabIndex === -1`, home handle fraction `0`, and ignored pointer/keyboard events. Update the same instance to active and assert enabled ARIA/range/input. Update to inactive completion with `moves: 3` and assert final fraction `1`, disabled input, and unchanged element identity.

- [ ] **Step 2: Replace browser absence assertions**

Archive startup must require exactly one `.curse-production-timeline-control`, disabled at home. Record its DOM identity in the fixture, select a puzzle, move the timeline, complete the puzzle, and return to archive while asserting the same element remains connected. Completion must be disabled at the final handle position. Pointer and keyboard attempts in archive/completion must produce no writes or cursor action.

- [ ] **Step 3: Run timeline and runtime tests and verify RED**

```bash
npm test -- --run tests/game/timeline-lever.test.ts tests/game/authoritative-runtime-browser.test.ts
```

Expected: archive assertion fails because the slider control is absent and the current lever requires a live timeline.

- [ ] **Step 4: Rebuild the lever around a projection**

Mount the rail once, replace `refresh()` with `update(projection)`, cancel active drag when disabled, set disabled ARIA/tab order/cursor class explicitly, and project home/final positions without fabricating a `GameTimeline`. Active projection retains exact cursor calculation and slider keys.

- [ ] **Step 5: Move mount ownership out of puzzle lifecycle**

Create the lever once in `CursebreakerRuntime` after the lens environment. Update it on every committed state. Remove timeline creation from `#mountPuzzle` and removal from `#disposePuzzle`. Keep input dispatch guarded by active puzzle mode, editor state, proof motion, and pause ownership. Add inactive CSS that removes the resize cursor and focus treatment without hiding any layer.

- [ ] **Step 6: Run timeline and runtime tests and verify GREEN**

Run the Step 3 command. Expected: both files pass.

- [ ] **Step 7: Commit persistent timeline ownership**

```bash
git add src/game/interface/timeline-lever.ts src/game/interface/lens-environment.css src/game/interface/mount.ts tests/game/timeline-lever.test.ts tests/game/authoritative-runtime-browser.test.ts tests/game/authoritative-runtime-fixture.ts
git commit -m "feat: keep timeline instrument persistent"
```

---

### Task 4: Replace modal presentation with the mandatory passive game view

**Files:**
- Modify: `tests/game/authoritative-runtime-browser.test.ts`
- Modify: `tests/game/authoritative-runtime-source.test.ts`
- Modify: `tests/game/production-interface-dom.test.ts`
- Modify: `src/game/interface/lens-environment.ts`
- Modify: `src/game/interface/lens-environment.css`
- Modify: `src/game/interface/index.ts`
- Rebuild: `src/game/interface/game-presentation-view.ts`
- Rebuild: `src/game/interface/game-presentation-view.css`
- Modify: `src/game/interface/mount.ts`
- Modify: `app/style.css`

**Interfaces:**
- Consumes: primary mode, active guidance/page, settings, completion receipt, resolved artifact/response copy, and typed `GameAction` dispatch.
- Produces: one required `MountedGamePresentationView` in `LensEnvironment.presentationHost` rendering completion, pause/settings, or passive guidance.

- [ ] **Step 1: Delete the rejected uncommitted teacher implementation**

Remove the current modal teacher DOM/CSS and shared `presentationCandidate` teacher variants before adding replacement tests. Preserve only behavior independently required by the approved completion and pause contracts when rewriting the files.

- [ ] **Step 2: Write failing passive-guidance browser assertions**

Drive the real first puzzle and require one `.curse-guidance-note` containing one `p`, one optional `button` labelled Next, no `[role="dialog"]`, no backdrop-sized pointer surface, and unchanged active element. Click Next through every page and assert only the paragraph/page indicator changes and writes persist. On the final page require zero buttons. From an earlier page, select/deselect proof geometry and invoke Escape; require proof selection behavior and pause to work while the guidance state remains. Perform the witness from an earlier page and require completion without page exhaustion.

Add exact recognized-unwinnable assertions: the passive note replaces opening guidance, timeline remains enabled, and rewind removes the note. Add compact/large-text geometry assertions proving the note does not intersect proof aperture, timeline track, folio drawer handle, or loupe terminal.

- [ ] **Step 3: Retain and correct completion/pause tests**

Require archive operability, dedicated completion content and exactly one Return action, saved completion restoration, pause’s four actions, settings controls, Escape precedence, settings persistence, and preserved underlying lens/timeline. Delete every assertion that treats blank presentation, modal teacher input ownership, acknowledgement, close buttons, or absent slider as success.

- [ ] **Step 4: Run presentation/browser tests and verify RED**

```bash
npm test -- --run tests/game/authoritative-runtime-browser.test.ts tests/game/authoritative-runtime-source.test.ts tests/game/production-interface-dom.test.ts
```

Expected: failures because the passive projection/view is absent and rejected teacher source names still remain.

- [ ] **Step 5: Rebuild the single presentation view**

Use a projection shaped as:

```ts
export type GamePresentationProjection = {
  readonly mode: GamePrimaryMode
  readonly transient: GameTransient | null
  readonly guidance: ActiveGuidance | null
  readonly settings: GameSettings
  readonly completion: CompletionPresentation | null
}
```

Render guidance as an `aside` with exactly the current paragraph and, when needed, one Next button dispatching `advanceGuidancePage`. Do not assign dialog/status/live-region semantics or auto-focus. Set the root to `pointer-events: none`; allow pointer events only on the note’s Next control, with note geometry outside all game controls. Hide the note visually beneath pause/editor without clearing controller state.

Render pause/settings and completion from the approved contracts. Mount the view automatically; delete optional presentation ports/no-op fallbacks. Resolve completion response from the single completion page or provenance response. Remove any CSS that hides the physical timeline in completion.

- [ ] **Step 6: Remove displaced source and test vocabulary**

Source tests must reject `modalInstruction`, teacher transients, `openTeacher`, `acknowledgeTeacher`, `closeTeacher`, `acknowledgedTeachers`, `emptyPresentation`, optional presentation ownership, and teacher candidate selectors. Remove obsolete serializers, fixtures, and assertions rather than aliasing them.

- [ ] **Step 7: Run presentation/browser tests and verify GREEN**

Run the Step 4 command. Expected: all three files pass with no browser console errors.

- [ ] **Step 8: Commit the mandatory presentation replacement**

```bash
git add app/style.css src/game/interface/index.ts src/game/interface/lens-environment.ts src/game/interface/lens-environment.css src/game/interface/game-presentation-view.ts src/game/interface/game-presentation-view.css src/game/interface/mount.ts tests/game/authoritative-runtime-browser.test.ts tests/game/authoritative-runtime-source.test.ts tests/game/production-interface-dom.test.ts
git commit -m "feat: render passive paged guidance"
```

---

### Task 5: Run structural integration verification

**Files:**
- No planned file changes; any failure returns to the task that owns the failing behavior.

**Interfaces:**
- Consumes: completed domain, controller/save, persistent timeline, presentation view, and runtime ownership.
- Produces: verified structural integration before any unapproved visual candidate is retained.

- [ ] **Step 1: Run relevant non-physics tests**

```bash
npm test -- --run tests/game/catalog.test.ts tests/game/teaching.test.ts tests/game/opening-content.test.ts tests/game/controller.test.ts tests/game/save.test.ts tests/game/timeline-lever.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-source.test.ts tests/game/authoritative-runtime-browser.test.ts
```

Expected: all pass.

- [ ] **Step 2: Run type, asset, and desktop build checks**

```bash
npm run typecheck
npm run assets:validate
npm run build:desktop
git diff --check
```

Expected: exit code 0 for every command. Do not run Electron.

- [ ] **Step 3: Scan for displaced authority**

```bash
rg -n "modalInstruction|openTeacher|acknowledgeTeacher|closeTeacher|acknowledgedTeachers|emptyPresentation|CursebreakerPresentationPort|presentationCandidate" src app tests
```

Expected: no matches except explicit negative source-test string lists.

- [ ] **Step 4: Repair and rerun within scope**

For any failure, add the smallest failing regression assertion if one is missing, repair the owning implementation, and rerun the failed command plus Step 1. Do not weaken expectations or add compatibility paths.

---

### Task 6: Produce the passive-guidance visual gate without committing rejected variants

**Files:**
- Temporarily modify, do not commit: `src/game/interface/game-presentation-view.css`
- Temporarily modify, do not commit: `src/game/interface/mount.ts`
- Temporarily retain, do not commit: `scripts/capture-game-review.mjs`
- Temporarily modify, do not commit: `package.json`
- Write captures outside repository: `/tmp/cursebreaker-game-captures/guidance-{a,b,c}.png`

**Interfaces:**
- Consumes: real runtime first-puzzle guidance projection and approved passive input contract.
- Produces: three high-fidelity headless captures differing only in edge-note material, typography, attachment, page indicator, and Next treatment.

- [ ] **Step 1: Add temporary review-only selectors**

Add `guidanceCandidate=a|b|c` handling isolated to the guidance root. All candidates use the same DOM, edge geometry, paragraph, optional Next action, lifecycle, and input behavior. They may vary only approved desk/indigo/vellum/gasket-derived materials and restrained settle motion. No centered panel, scrim, portrait, title, close control, dialog, focus capture, or overlap with proof/timeline/folio is permitted.

- [ ] **Step 2: Add semantic-equivalence browser coverage**

For A/B/C, assert identical paragraph, page index, button count, note bounding-box nonintersection, focus, proof input, timeline input, and Escape behavior. Run:

```bash
npm test -- --run tests/game/authoritative-runtime-browser.test.ts
```

Expected: all candidates pass the same behavioral contract.

- [ ] **Step 3: Capture with the stable approved command**

```bash
npm run game:capture -- --surface guidance --out-dir /tmp/cursebreaker-game-captures
```

Expected: three PNGs exist only under `/tmp/cursebreaker-game-captures`; no visible browser or Electron window opens.

- [ ] **Step 4: Stop at the visual decision gate**

Present the three real in-app guidance captures and ask the user to select A, B, or C. Do not commit candidate CSS, query selection, capture script, package script, or screenshots. After selection, delete rejected variants and review-only code before committing the selected production treatment. Pause/settings and completion visual gates follow in separate approved plan continuations.
