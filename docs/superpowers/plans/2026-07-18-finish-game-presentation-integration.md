# Complete Game Presentation Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace blank archive/completion/transient presentation with one mandatory production view and authoritative rendered-state validation.

**Architecture:** `CursebreakerRuntime` continues to own controller state and supplies a catalog-resolved projection to one `GamePresentationView` mounted in a persistent lens overlay host. The view emits existing typed controller actions and owns completion, pause/settings, and teacher DOM; visual candidates share semantics and differ only through a review-only root attribute and CSS.

**Tech Stack:** TypeScript, framework-free DOM, CSS, Vitest, Playwright Chromium, Vite, Electron.

## Global Constraints

- Preserve the approved desk, full-height lens, folio, motion, substrate, timeline artwork, and dark-neon proof palette.
- Do not run the dedicated unchanged physics battery.
- Do not launch Electron or any visible GUI on the user’s desktop.
- Completion has exactly one action and no score/rank/replay/review controls.
- Do not invent lore or character art.
- Candidate selection is review-only and must be deleted after user approval.

---

### Task 1: Replace absence-based runtime authority

**Files:**
- Modify: `tests/game/authoritative-runtime-browser.test.ts`
- Modify: `tests/game/authoritative-runtime-fixture.ts`
- Create: `tests/game/game-presentation-view.test.ts`

**Interfaces:**
- Consumes: existing `mountCursebreaker`, real controller actions, opening/controller catalogs.
- Produces: failing rendered expectations for archive, completion, saved completion, pause, settings, and teacher states.

- [ ] Remove the null-save assertion that describes success only as “without proof or timeline”; retain the correct no-proof/no-slider facts and require visible lens artwork, inactive timeline apparatus, folio, and unlocked record.
- [ ] Remove the completion assertion that accepts `hasProof: false` and `hasTimeline: false` without a replacement view.
- [ ] Add a completion scenario/save fixture that restores a real completed state through `encodeGameSave`.
- [ ] Add browser assertions for completion copy, artifact name, move count, authored response, exactly one button, preserved physical lens/timeline artwork, return-to-archive action, and saved-completion startup.
- [ ] Add browser assertions for pause menu actions, settings controls, changes routed through controller saves, modal instruction acknowledgement, nonblocking commentary, and Escape precedence while the underlying primary DOM remains connected.
- [ ] Run `npm test -- --run tests/game/authoritative-runtime-browser.test.ts tests/game/game-presentation-view.test.ts` and confirm failures are caused by missing presentation DOM/no-op ownership.

### Task 2: Create the single production presentation view

**Files:**
- Create: `src/game/interface/game-presentation-view.ts`
- Create: `src/game/interface/game-presentation-view.css`
- Modify: `src/game/interface/lens-environment.ts`
- Modify: `src/game/interface/lens-environment.css`
- Modify: `src/game/interface/index.ts`

**Interfaces:**
- Consumes: `GamePrimaryMode`, `GameTransient`, `GameSettings`, `CompletionReceipt`, resolved puzzle identity/provenance/teacher text.
- Produces: `mountGamePresentationView(options): MountedGamePresentationView`, `GamePresentationProjection`, and one persistent overlay host from `MountedLensEnvironment.presentationHost`.

- [ ] Define a projection with resolved display copy so the view never imports catalog/controller authority.
- [ ] Define callbacks for `resume`, `levelSelection`, `openPauseSettings`, `escape`, `exitGame`, `acknowledgeTeacher`, `closeTeacher`, `setReducedMotion`, `setFullscreen`, and `setTextSize`.
- [ ] Mount one overlay root and update state-specific semantic DOM in place; completion must render the exact required fields and exactly one button.
- [ ] Render pause/settings and teacher surfaces with correct modal/nonmodal roles and labels.
- [ ] Add a persistent overlay host above the substrate/proof but below refusal/editor surfaces without changing lens geometry or pointer mapping.
- [ ] Run the focused tests and make the presentation-view unit tests pass.

### Task 3: Make presentation mandatory in the real runtime

**Files:**
- Modify: `src/game/interface/mount.ts`
- Modify: `app/main.ts`
- Modify: `app/style.css`
- Modify: `tests/game/authoritative-runtime-source.test.ts`

**Interfaces:**
- Consumes: `mountGamePresentationView` and the existing `reduceGame` action surface.
- Produces: one mandatory presentation owner automatically mounted by `mountCursebreaker`.

- [ ] Delete `CursebreakerPresentationPort`, `emptyPresentation`, and the optional `presentation` mount option.
- [ ] Resolve completion response from the completed puzzle’s authored completion teacher intervention, falling back to its provenance function/summary without fabricated text.
- [ ] Update the view on every committed state and dispatch callbacks through the runtime.
- [ ] Keep folio/proof lifecycle state-specific while preserving environment and presentation roots through every transition.
- [ ] Remove CSS that hides the physical timeline artwork in completion; disable only logical slider input by disposing the puzzle timeline.
- [ ] Run focused source, controller, and browser tests until green.

### Task 4: Add high-fidelity review candidates

**Files:**
- Modify: `src/game/interface/game-presentation-view.ts`
- Modify: `src/game/interface/game-presentation-view.css`
- Modify: `app/main.ts`
- Create: `tests/game/game-presentation-candidates-browser.test.ts`
- Create: `tests/game/game-presentation-candidates-fixture.html`
- Create: `tests/game/game-presentation-candidates-fixture.ts`

**Interfaces:**
- Consumes: the same production projection and callbacks for every candidate.
- Produces: review-only `presentationCandidate` query selection and headless captures for teacher, pause/settings, and completion A/B/C compositions.

- [ ] Implement Field annotation, Conservation slip, and Optical marginalia teacher compositions without character art.
- [ ] Implement Instrument rest, Registrar folio, and Shutter interval pause/settings compositions.
- [ ] Implement Clearance docket, Developed plate, and Released mount completion compositions.
- [ ] Ensure candidate selection changes only a root data attribute and never the semantic DOM/action count.
- [ ] Add browser geometry/overflow/role assertions at 1600×1000 and compact large-text viewports.
- [ ] Capture actual controller-driven headless PNGs for the first visual gate.

### Task 5: Full non-GUI verification and visual gate

**Files:**
- Modify: `tests/game/authoritative-runtime-browser.test.ts`
- Modify: `.superpowers/sdd/progress.md`
- Append: `/tmp/cursebreaker-finish-integration-Kw9WW3/foundation.md`

**Interfaces:**
- Consumes: completed production view and browser candidates.
- Produces: authoritative evidence and user-visible candidate images.

- [ ] Run all focused controller/interface/browser tests, then the relevant non-physics game suite.
- [ ] Run `npm run typecheck`, `npm run assets:validate`, `npm run build:desktop`, and `git diff --check`.
- [ ] Scan for `emptyPresentation`, optional presentation ownership, and assertions that accept blank completion.
- [ ] Obtain a read-only review of the diff without launching a GUI.
- [ ] Append foundation conformance for completed structural integration and list the remaining visual selections.
- [ ] Present the first surface’s three real in-app captures and stop for user selection before deleting unselected candidates or claiming final styling complete.

