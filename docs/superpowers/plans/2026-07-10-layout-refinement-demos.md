# Layout Refinement Demos Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the obsolete Round 14 layout comparison with three distinct, real-application-backed demonstrations of Compass Aperture, Phase Compass, and Readable Margin Compass.

**Architecture:** `layout-frame.ts` remains the single demonstration compositor around one actual application iframe and its authoritative Library, mode, replay, and theme state. Variant-specific CSS projects the same state into three layout grammars; it may alter chrome, but never resize, redraw, or semantically replace the application. Round entry points and the lab index identify the new choices.

**Tech Stack:** TypeScript, DOM APIs, CSS, Vite, Playwright.

## Global Constraints

- Use the actual application diagram and interactions; do not draw a mock diagram.
- All three Library surfaces overlay the application without resizing, refitting, or changing physics.
- Preserve exact-orange application selection, explicit right-click actions, pointer-local errors, silent success, Indexed Ledger, real replay scrubbing, Porcelain surfaces, and Basalt typography.
- Do not run physics tests because this round does not change physics.
- Commit the completed, validated round and leave the repository clean.

---

### Task 1: Specify the three replacement projections

**Files:**
- Modify: `e2e/layout-frame.spec.ts`

**Interfaces:**
- Consumes: Round 14 pages at `/ui-lab/round14-{a,b,c}.html` and the real iframe debug seam.
- Produces: browser-level requirements for variant identity, stable overlay geometry, phase response, readable margins, authoritative state, and removal of obsolete demo structures.

- [x] **Step 1: Replace the old Workbench/Bookmark assertions with failing behavior tests**

  Require `data-variant` values `aperture`, `phase`, and `margin`; require A to expose stable north/west/south landmarks, B to mark its frame with the current lifecycle phase and suppress the Edit timeline, and C to expose horizontally readable Library and labeled utilities. Require every Library opening to leave the iframe bounding box unchanged. Assert `.layout-trail`, `.layout-identity`, `.layout-workflow-kicker`, and workflow-reference links are absent.

- [x] **Step 2: Run the focused browser test and verify RED**

  Run: `npx playwright test e2e/layout-frame.spec.ts --project=chromium`

  Expected: FAIL because the pages still report `compass`, `bookmark`, and `workbench`, Workbench resizes the iframe, and obsolete trail/workflow structures remain.

### Task 2: Rebuild the Round 14 compositor and visual variants

**Files:**
- Modify: `ui-lab/layout-frame.ts`
- Modify: `ui-lab/layout-frame.css`
- Modify: `ui-lab/round14-a.ts`
- Modify: `ui-lab/round14-b.ts`
- Modify: `ui-lab/round14-c.ts`
- Modify: `ui-lab/round14-a.html`
- Modify: `ui-lab/round14-b.html`
- Modify: `ui-lab/round14-c.html`
- Modify: `ui-lab/round15-a.ts`
- Modify: `ui-lab/round15-b.ts`
- Modify: `ui-lab/round15-c.ts`
- Modify: `ui-lab/round16.ts`
- Modify: `ui-lab/round17.ts`

**Interfaces:**
- Consumes: `mountLayoutFrame(host, variant)` with `variant` in `'aperture' | 'phase' | 'margin'`; authoritative application controls and `__vpaDebug.replay()`.
- Produces: three visually distinct layouts over the same real app and `data-mode`, `data-theme`, and `data-ready` state attributes for styling and tests.

- [x] **Step 1: Replace the variant model and remove competing chrome**

  Change `LayoutVariant` to `'aperture' | 'phase' | 'margin'`. Remove identity, trail, duplicate replay step, workflow-reference links, and their event handlers. Keep one lifecycle capsule, one utilities disclosure, one Library anchor/drawer, and one temporal surface.

- [x] **Step 2: Project authoritative phase state**

  In synchronization, set `host.dataset.mode = replay.mode`, keep the lifecycle capsule as the only mode label, and continue deriving theme and temporal values from the real application. Give Phase Compass mode-specific readable supporting text without creating a second state authority.

- [x] **Step 3: Implement the three CSS grammars**

  A uses compact centered north controls, a vertical west Library anchor, and a conditional south rail. B keeps Edit extremely quiet and expands/repositions only the phase-relevant lifecycle/history chrome. C uses a slightly larger stable top margin, horizontal readable Library tab, and a labeled `View` utility disclosure. All three use overlay drawers and leave `.layout-stage` at `inset: 0`.

- [x] **Step 4: Update entry points and titles**

  Map A/B/C to `aperture`/`phase`/`margin` and title them `Compass Aperture`, `Phase Compass`, and `Readable Margin Compass`.

- [x] **Step 5: Migrate later redesign rounds to the surviving frame model**

  Replace their deleted `compass` argument with `aperture` so aesthetic, Library, and feedback demonstrations remain on the one selected frame implementation rather than a compatibility alias.

- [x] **Step 6: Use the approved real application surfaces and verify GREEN**

  Default the layout round to the Ledger-backed real Porcelain application fixture so the diagrams are populated and Browse/Sources is the approved Library. Suppress the displaced PiP companion rather than exposing a wrong proving layout.

  Run: `npx playwright test e2e/layout-frame.spec.ts --project=chromium`

  Expected: all focused tests pass with zero failures.

### Task 3: Publish, inspect, and validate the redesign round

**Files:**
- Modify: `ui-lab/index.html`
- Modify: `docs/superpowers/plans/2026-07-03-plan-19-interface-overhaul.md`

**Interfaces:**
- Consumes: the three verified Round 14 pages.
- Produces: accurate lab navigation and redesign tracker state.

- [x] **Step 1: Update catalogue and tracker copy**

  Describe A/B/C as Compass Aperture, Phase Compass, and Readable Margin Compass; explain that all use the real application and overlay-only surfaces. Record that the new options are ready for user judgment without marking the layout decision approved.

- [x] **Step 2: Run non-physics validation**

  Run: `npm run typecheck`

  Run: `npx playwright test e2e/layout-frame.spec.ts e2e/aesthetic-frame.spec.ts e2e/library-frame.spec.ts e2e/feedback-frame.spec.ts --project=chromium`

  Expected: typecheck and all relevant UI browser tests pass with zero failures.

- [x] **Step 3: Inspect rendered desktop screenshots**

  Capture A/B/C at 1440×900 in Edit and at least one stateful surface. Confirm actual diagrams remain visible, alternatives are visibly distinct, no panel changes the iframe bounds, Light/Dark agree, and comparison chrome is visually separate from product chrome.

- [x] **Step 4: Append foundation conformance evidence**

  Add implemented ownership, deleted models, migrated surfaces, and exact validation results to `/tmp/vpa-layout-demos-foundation-20260710.md` without changing its pre-action sections.

- [x] **Step 5: Commit and confirm a clean repository**

  Run: `git add docs/superpowers/plans/2026-07-10-layout-refinement-demos.md docs/superpowers/plans/2026-07-03-plan-19-interface-overhaul.md ui-lab/layout-frame.ts ui-lab/layout-frame.css ui-lab/round14-a.ts ui-lab/round14-b.ts ui-lab/round14-c.ts ui-lab/round14-a.html ui-lab/round14-b.html ui-lab/round14-c.html ui-lab/round15-a.ts ui-lab/round15-b.ts ui-lab/round15-c.ts ui-lab/round16.ts ui-lab/round17.ts ui-lab/index.html e2e/layout-frame.spec.ts`

  Run: `git commit -m "feat: demo refined whole-app layouts"`

  Run: `git status --short`

  Expected: commit succeeds and status output is empty.
