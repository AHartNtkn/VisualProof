# Excavation Folio Demo Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a standalone, high-fidelity interactive excavation-folio demonstration beside the approved Cursebreaker lens.

**Architecture:** A demo-only TypeScript state model drives semantic HTML and physically modeled CSS motion. One reusable institutional asset system presents copied opening-catalog content; Playwright capture and tests use the same keyboard/state authority as manual review. No application or game runtime is imported.

**Tech Stack:** TypeScript, Vite, CSS, SVG/PNG asset generation, Playwright, Vitest.

## Global Constraints

- The demo is standalone under `review/excavation-folio/`.
- It imports nothing from `src/app`, `src/game`, `src/kernel`, or `src/view`.
- The corrected central instrument remains full viewport height and unobstructed.
- One institutional folio, page, mount, label, status, and animation language serves every culture.
- Cultural distinction comes only from artifact and documentary evidence.
- Each artifact has one image and no more than three short player-facing text lines.
- Every visible player-facing control is a physical folio part.
- Review controls are keyboard-only with no visible strip, buttons, legend, or help overlay.
- No proof interaction, real progression, persistence, teacher UI, right-side library, or file management.
- Physics tests remain excluded; this demo changes no diagram physics.

---

### Task 1: Demo state, content projection, and approved desk composition

**Files:**
- Create: `review/excavation-folio/index.html`
- Create: `review/excavation-folio/main.ts`
- Create: `review/excavation-folio/model.ts`
- Create: `review/excavation-folio/content.ts`
- Create: `review/excavation-folio/base.css`
- Create: `tests/review/excavation-folio-model.test.ts`

**Interfaces:**
- Produces: `createInitialState()`, `transition(state, action)`, `artifactStatus(progression, artifactId)`, and a mounted demo root with deterministic `data-*` state attributes.
- Consumes: existing approved desk and mechanical image assets only by URL.

- [ ] **Step 1: Write model tests for every progression, culture, cover, inspection, restriction, motion, reset, and Escape transition.**
- [ ] **Step 2: Run the focused model tests and verify they fail because the demo model does not exist.**
- [ ] **Step 3: Implement the closed demo state model and copied lean content projection for six Seyric artifacts and one Myratic artifact.**
- [ ] **Step 4: Implement the full-height approved lens and left workspace composition without folio artwork.**
- [ ] **Step 5: Add keyboard-only review mappings: digits 1–5 select progression, M toggles full/reduced motion, P pauses motion, R resets, Escape closes inspection.**
- [ ] **Step 6: Run model tests and typecheck; commit the task.**

### Task 2: Institutional folio and artifact asset system

**Files:**
- Create: `scripts/assets/build-excavation-folio-assets.py`
- Create: `assets/interface/generated/excavation-folio/folio-shell.png`
- Create: `assets/interface/generated/excavation-folio/guard-leaf.png`
- Create: `assets/interface/generated/excavation-folio/dossier-sheet.png`
- Create: `assets/interface/generated/excavation-folio/mount-photo.png`
- Create: `assets/interface/generated/excavation-folio/mount-rubbing.png`
- Create: `assets/interface/generated/excavation-folio/mount-tracing.png`
- Create: `assets/interface/generated/excavation-folio/restricted-sleeve.png`
- Create: `assets/interface/generated/excavation-folio/clearance-slip.png`
- Create: `assets/interface/generated/excavation-folio/priority-band.png`
- Create: `assets/interface/generated/excavation-folio/specimens/*.png`
- Create: `assets/interface/source/inputs/excavation-folio/provenance.json`
- Create: `review/excavation-folio/folio.css`
- Create: `tests/review/excavation-folio-assets.test.ts`

**Interfaces:**
- Produces: one reusable institutional folio asset family plus seven distinct specimen images.
- Consumes: Task 1 semantic class and `data-status` contracts.

- [ ] **Step 1: Write asset-contract tests for required files, image dimensions, alpha use, distinct specimen hashes, and absence of placeholder-sized outputs.**
- [ ] **Step 2: Run the focused asset tests and verify missing-asset failures.**
- [ ] **Step 3: Generate physically detailed folio, sheet, mount, sleeve, clearance, and priority assets with consistent lighting and material scale.**
- [ ] **Step 4: Generate one distinct specimen image per artifact using evidence types from the shared mount family.**
- [ ] **Step 5: Compose the default Seyric and Myratic dossiers using the one institutional grammar and all five physical status treatments.**
- [ ] **Step 6: Inspect at 1600×1000, correct visual defects, run asset tests, and commit the task.**

### Task 3: Physical folio interactions and animation choreography

**Files:**
- Create: `review/excavation-folio/motion.ts`
- Create: `review/excavation-folio/motion.css`
- Modify: `review/excavation-folio/main.ts`
- Modify: `review/excavation-folio/folio.css`
- Create: `tests/review/excavation-folio-motion.test.ts`

**Interfaces:**
- Consumes: Task 1 transitions and Task 2 DOM/asset grammar.
- Produces: interruptible cover, dossier, tab, record, inspection, restricted-resistance, and packet-release motion with reduced-motion equivalents.

- [ ] **Step 1: Write tests for animation class/state cleanup, interruption, reduced-motion substitution, and inaccessible-record refusal settling.**
- [ ] **Step 2: Run the focused motion tests and verify they fail.**
- [ ] **Step 3: Implement cover hinge and stacked dossier/tab choreography.**
- [ ] **Step 4: Implement record release, lift, inspection, return, and believable height-dependent shadow changes.**
- [ ] **Step 5: Implement inaccessible sleeve resistance and Myratic packet release without software feedback.**
- [ ] **Step 6: Implement interruptible transitions and reduced-motion equivalents; run tests and commit the task.**

### Task 4: Deterministic review capture and conformance

**Files:**
- Create: `scripts/capture-excavation-folio.mjs`
- Create: `tests/review/excavation-folio-browser.test.ts`
- Create: `review/excavation-folio/evidence/*.png`
- Create: `review/excavation-folio/evidence/motion-trace.json`
- Create: `review/excavation-folio/README.md`

**Interfaces:**
- Consumes: complete demo and keyboard review authority.
- Produces: required still scenarios, motion trace, shortcut documentation, and final validation evidence.

- [ ] **Step 1: Write browser tests for all required scenarios, no visible review UI, runtime-import prohibition, and folio/lens non-overlap.**
- [ ] **Step 2: Run focused browser tests and verify capture/evidence failures.**
- [ ] **Step 3: Implement deterministic Vite serving, keyboard-driven scenario capture, and animation-frame tracing.**
- [ ] **Step 4: Capture closed, default Seyric, mixed Seyric, inspection, inaccessible resistance, Myratic restricted/released, reduced-motion, and both viewport sizes.**
- [ ] **Step 5: Run focused tests, typecheck, default non-physics tests relevant to review code, and visual inspection.**
- [ ] **Step 6: Correct defects, rerun validation, document shortcuts, and commit the task.**
