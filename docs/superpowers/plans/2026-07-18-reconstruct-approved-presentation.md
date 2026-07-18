# Reconstruct Approved Presentation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the simplified production workspace with the approved full-scale lens, excavation-folio layout, five-channel motion system, and rendered dark-neon proof presentation while retaining real game state and interactions.

**Architecture:** Promote the recoverable approved presentation implementation into `src/game/interface` and make `FolioProjection` its only state input. The game controller continues to own logical state; the folio owns only physical presentation state such as cover pose, motion lifecycles, and lifted-record geometry. Browser-computed geometry, frame traces, and canvas pixels become the presentation authority.

**Tech Stack:** TypeScript, framework-free DOM, CSS, Canvas 2D, Vitest, Playwright, Vite, Electron.

## Global Constraints

- Preserve the approved PNG pixels exactly.
- Do not restore review demos, fake progression, keyboard review controls, source scenes, render generators, or hash authority.
- Do not change proof physics or run `test:physics`.
- Keep the proof canvas transparent over the approved substrate.
- Full folio motion durations remain cover 380ms, dossier 260ms, record 340ms, restriction 320ms, and packet 480ms; reduced motion is 90ms and non-spatial.
- At desktop widths the lens is exactly `100vh` and uses the approved asymmetric aperture.
- The current game controller remains the sole logical state and persistence authority.

---

### Task 1: Restore production asset completeness

**Files:**
- Modify: `scripts/assets/production-interface-assets.ts`
- Modify: `tests/assets/production-interface-assets.test.ts`
- Restore: `assets/interface/generated/excavation-folio/guard-leaf.png`
- Restore: `assets/interface/generated/excavation-folio/mount-rubbing.png`
- Restore: `assets/interface/generated/excavation-folio/mount-tracing.png`
- Restore: `assets/interface/generated/excavation-folio/priority-band.png`

**Interfaces:**
- Consumes: approved blobs at commit `c556eaed2b6f574436519e1d266c3a349c58ef2b`.
- Produces: four semantically registered runtime assets consumed by `folio.css`.

- [ ] **Step 1: Add the four required paths to `expectedRuntimeAssets` and `PRODUCTION_INTERFACE_ASSETS`**

  Use the reference PNG dimensions and `rgba` color type. Set each consumer to
  `src/game/interface/folio.css` and use its exact relative URL token.

- [ ] **Step 2: Run the focused asset test and verify RED**

  Run: `npm test -- --run tests/assets/production-interface-assets.test.ts`

  Expected: FAIL because the four production files are absent or unregistered.

- [ ] **Step 3: Restore only the four approved blobs**

  Read each blob from the reference commit and add it at the production path.
  Do not restore `review/`, generators, manifests, or source scenes.

- [ ] **Step 4: Run semantic asset validation and verify GREEN**

  Run: `npm test -- --run tests/assets/production-interface-assets.test.ts`

  Run: `npm run assets:validate`

- [ ] **Step 5: Commit**

  ```bash
  git add assets/interface/generated/excavation-folio scripts/assets/production-interface-assets.ts tests/assets/production-interface-assets.test.ts
  git commit -m "assets: restore approved folio layers"
  ```

### Task 2: Restore authoritative workspace geometry

**Files:**
- Modify: `src/game/interface/folio-layout.ts`
- Modify: `src/game/interface/lens-environment.ts`
- Modify: `src/game/interface/lens-environment.css`
- Modify: `tests/game/folio-layout.test.ts`
- Modify: `tests/game/production-interface-dom.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`

**Interfaces:**
- Consumes: `interfaceLayout(width, height)`.
- Produces: desktop lens `{left, top, size}` plus folio workspace width derived from approved aperture/timeline boundaries; compact drawer geometry remains explicit.

- [ ] **Step 1: Write failing exact desktop geometry tests**

  For `1600x1000`, assert lens `{left: 600, top: 0, size: 1000}` and folio
  workspace width `min(736.2, 628.8)` within one pixel. For `1920x1080`, assert
  lens `{left: 840, top: 0, size: 1080}`. Assert the desktop folio does not alter
  lens size. Retain compact drawer assertions below 980px.

- [ ] **Step 2: Run geometry tests and verify RED**

  Run: `npm test -- --run tests/game/folio-layout.test.ts tests/game/production-interface-dom.test.ts`

  Expected: FAIL because current desktop layout caps the folio at 420px and shrinks/recenters the lens.

- [ ] **Step 3: Implement the approved desktop equations**

  Compute `lensSize = height`, `lensCenterX = max(width / 2, width - height / 2)`,
  and `folioWidth = max(0, min(lensCenterX - height * 0.3638,
  lensCenterX - height * 0.4712))`. Preserve the compact drawer branch.

- [ ] **Step 4: Restore approved aperture and substrate CSS geometry**

  Set the lens top to zero at desktop widths, use aperture inset
  `7.57% 13.62% 19.65%`, place the proof slot at the aperture, and preserve the
  substrate's `-8% / 116%` overscan. Gasket and timeline remain full-lens layers.

- [ ] **Step 5: Add a browser rectangle assertion and verify GREEN**

  Assert actual bounding rectangles at 1600x1000 and 1920x1080, then run:

  `npm test -- --run tests/game/folio-layout.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts`

- [ ] **Step 6: Commit**

  ```bash
  git add src/game/interface/folio-layout.ts src/game/interface/lens-environment.ts src/game/interface/lens-environment.css tests/game/folio-layout.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts
  git commit -m "fix: restore approved workspace geometry"
  ```

### Task 3: Promote the complete motion coordinator

**Files:**
- Replace: `src/game/interface/folio-motion.ts`
- Create: `src/game/interface/folio-motion.css`
- Modify: `tests/game/folio-motion.test.ts`

**Interfaces:**
- Produces: `FolioMotion.cover`, `.dossier`, `.recordInspection`, `.restrictedRefusal`, `.packetRelease`, and `.settleAll`.
- Produces descriptors `is-motion-<channel>`, `data-motion-<channel>-target`, `data-motion-<channel>-kind`, and `--motion-<channel>-duration`.

- [ ] **Step 1: Replace the reduced unit tests with the approved five-channel contract**

  Add RED tests for exact durations and descriptors, reduced 90ms motion, no
  paused compatibility mode, interrupted cover/record computed-style snapshots,
  replacement cleanup ownership, and `settleAll` descriptor removal.

- [ ] **Step 2: Run the focused motion tests and verify RED**

  Run: `npm test -- --run tests/game/folio-motion.test.ts`

- [ ] **Step 3: Promote the approved coordinator**

  Adapt the reference `motion.ts` to game `CultureId` and `PuzzleId`. Use
  `reducedMotion: boolean` at the public boundary; internally map it to full or
  reduced motion. Do not retain the old `FolioDossierMotion` class.

- [ ] **Step 4: Promote the authored CSS timelines**

  Copy the approved cover, dossier, record inspect/return, restriction, packet,
  and reduced-depth keyframes without changing their transforms or easings.

- [ ] **Step 5: Verify GREEN and absence of the displaced owner**

  Run: `npm test -- --run tests/game/folio-motion.test.ts`

  Run: `rg -n "FolioDossierMotion|curse-dossier-settle|folio-dossier-duration" src tests`

  Expected scan output: none.

- [ ] **Step 6: Commit**

  ```bash
  git add src/game/interface/folio-motion.ts src/game/interface/folio-motion.css tests/game/folio-motion.test.ts
  git commit -m "feat: promote approved folio motion"
  ```

### Task 4: Promote the approved physical folio with real projections

**Files:**
- Replace: `src/game/interface/folio-view.ts`
- Replace: `src/game/interface/folio.css`
- Modify: `src/game/interface/folio-projection.ts`
- Modify: `tests/game/folio-projection.test.ts`
- Modify: `tests/game/production-interface-dom.test.ts`
- Modify: `tests/game/authoritative-runtime-browser.test.ts`

**Interfaces:**
- Consumes: `FolioProjection`, existing archive selection/refusal callbacks, scroll callbacks, and theorem drag callbacks.
- Produces: one approved layered folio root with stable records, cover, inspection/lift stage, and packet presentation.

- [ ] **Step 1: Write failing DOM and projection tests**

  Assert exactly one lower board, two dossier underlays for the opening cultures,
  one guard leaf, one active dossier, one cover, one inspection/lift stage, and
  one continuous sheet. Assert desktop records use two columns and six records
  occupy three visible rows. Assert projection marks the restricted packet record
  explicitly, allowing the view to detect its locked-to-unlocked transition.

- [ ] **Step 2: Run the tests and verify RED**

  Run: `npm test -- --run tests/game/folio-projection.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts`

- [ ] **Step 3: Promote the approved DOM hierarchy**

  Build the reference physical layers with DOM APIs. Keep real record IDs,
  statuses, labels, accessibility, stable ordering, and callbacks. Remove the
  current `.curse-folio-dossier`/`.curse-folio-sheet` simplified hierarchy.

- [ ] **Step 4: Promote the approved layout CSS**

  Copy approved layer insets, tab geometry, two-column record scale, mounts,
  clearance/priority/restriction layers, cover, and inspection stage. Convert
  review-relative asset URLs to production-relative URLs. Make the record grid a
  vertically scrolling continuous sheet by adding rows below the first three;
  hide its software scrollbar and retain per-culture `scrollTop`.

- [ ] **Step 5: Connect real interactions without demo state**

  Archive unlocked records select immediately; locked records resist. Puzzle
  completed records use pointer capture and theorem drag callbacks. The lifted
  record follows exact client coordinates and returns through the record channel
  after drop or cancellation. Other puzzle records remain inert. The cover toggles
  only local presentation state and starts open for restored puzzles.

- [ ] **Step 6: Verify GREEN**

  Run: `npm test -- --run tests/game/folio-projection.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts`

- [ ] **Step 7: Commit**

  ```bash
  git add src/game/interface/folio-view.ts src/game/interface/folio.css src/game/interface/folio-projection.ts tests/game/folio-projection.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts
  git commit -m "feat: promote approved excavation folio"
  ```

### Task 5: Establish rendered geometry, motion, and dark-neon authority

**Files:**
- Create: `tests/game/approved-presentation-browser.test.ts`
- Create: `tests/game/approved-presentation-fixture.html`
- Create: `tests/game/approved-presentation-fixture.ts`
- Modify: `src/game/interface/proof-surface.ts` only if the failing pixel test identifies a production paint defect.
- Modify: `src/game/interface/proof-surface.css` only if the failing pixel test identifies an opaque/light surface.
- Modify: `package.json`

**Interfaces:**
- Produces: `npm run presentation:validate`, the single reusable visual-conformance command.

- [ ] **Step 1: Write a browser conformance suite that fails on the current presentation**

  At 1600x1000 compare actual rectangles to the approved reference measurements.
  Sample multiple animation frames for all five channels and require distinct
  painted transforms/opacity with correct settled endpoints. Reverse cover and
  record motion mid-flight and require less than one pixel of immediate pose jump.
  Exercise reduced motion and require no large translation or rotation.

- [ ] **Step 2: Add actual proof-canvas color probes**

  Mount a dark-theme diagram containing a wire, bubble, cut, and named node over
  the substrate. Read canvas pixels and require dark field/paper samples plus
  luminous cyan/purple proof pixels. Assert there is no opaque light canvas fill
  and no Light (Manuscript) palette color in the rendered surface.

- [ ] **Step 3: Run the new suite and verify RED before remaining fixes**

  Run: `npm test -- --run tests/game/approved-presentation-browser.test.ts`

- [ ] **Step 4: Fix only conformance defects exposed by the test**

  Preserve `DARK` when it already produces the approved result. If canvas
  composition suppresses glow or substitutes light fills, repair the production
  paint/composition boundary rather than defining a third theme.

- [ ] **Step 5: Add the stable validation command and verify GREEN**

  Add `"presentation:validate": "vitest run tests/game/approved-presentation-browser.test.ts"`.

  Run: `npm run presentation:validate`

- [ ] **Step 6: Commit**

  ```bash
  git add package.json tests/game/approved-presentation-browser.test.ts tests/game/approved-presentation-fixture.html tests/game/approved-presentation-fixture.ts src/game/interface/proof-surface.ts src/game/interface/proof-surface.css
  git commit -m "test: enforce approved presentation conformance"
  ```

### Task 6: Full production verification

**Files:**
- Modify only files required to repair failures caused by Tasks 1-5.
- Modify: `/tmp/cursebreaker-approved-presentation-Ua8FXR/foundation.md` conformance section.

**Interfaces:**
- Consumes: completed production reconstruction.
- Produces: verified desktop game and conformance receipt.

- [ ] **Step 1: Run focused game and asset tests**

  Run: `npm test -- --run tests/assets/production-interface-assets.test.ts tests/game/folio-layout.test.ts tests/game/folio-motion.test.ts tests/game/folio-projection.test.ts tests/game/production-interface-dom.test.ts tests/game/authoritative-runtime-browser.test.ts tests/game/approved-presentation-browser.test.ts`

- [ ] **Step 2: Run project validations**

  Run: `npm run typecheck`

  Run: `npm run assets:validate`

  Run: `npm run build:desktop`

  Do not run `npm run test:physics`.

- [ ] **Step 3: Run the real Electron smoke test**

  Run `npm run app` with an isolated user-data directory and remote debugging,
  inspect archive and puzzle screenshots, exercise culture switch, locked refusal,
  puzzle entry, pause/Escape, reduced motion, fullscreen switching, and clean exit.

- [ ] **Step 4: Prove displaced authorities are absent**

  ```bash
  rg -n "FolioDossierMotion|curse-folio-dossier|curse-folio-sheet|reviewActionForKey|ReviewProgression" src tests scripts
  ```

  Expected: no simplified folio or review-only state authority.

- [ ] **Step 5: Append foundation conformance and commit repairs**

  Record implemented owners, restored assets, displaced structures, exact commands,
  rendered evidence paths, and all results in the scratch foundation record. Commit
  any final in-scope repair with a focused message.
