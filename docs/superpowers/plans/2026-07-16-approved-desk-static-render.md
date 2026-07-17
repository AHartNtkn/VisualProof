# Approved Desk Static Render Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce one noninteractive browser render composed solely from approved Cursebreaker desk, substrate, gasket, and timeline assets.

**Architecture:** A standalone review document owns only image composition. Asset-generation scripts derive the standalone desk texture from its approved source treatment and render the candidate-04 timeline groups with transparency; the actual game application remains untouched.

**Tech Stack:** Blender 4.5, Pillow/ImageMagick-compatible PNG processing, HTML, CSS, headless Chromium.

## Global Constraints

- No unapproved assets.
- No JavaScript or interaction.
- No changes to the game runtime.
- Unapproved side regions remain bare desk.
- The substrate fills the gasket aperture and has no independent silhouette.

---

### Task 1: Collect the approved standalone visual layers

**Files:**
- Create: `scripts/assets/render-approved-static-assets.py`
- Create: `scripts/assets/render-corrected-mechanical.py`
- Create: `assets/interface/generated/desk/natural-indigo-hardwood.png`
- Create: `assets/interface/generated/substrates/static-review-substrate.png`
- Create: `assets/interface/generated/central-lens/timeline-housing.png`
- Create: `assets/interface/generated/central-lens/timeline-handle.png`

**Interfaces:**
- Consumes: approved source maps and candidate-04 Blender scene named in the specification.
- Produces: transparent or opaque PNG layers consumed by the static HTML document.

- [x] **Step 1: Implement deterministic desk and substrate collection**

Create a focused image-processing script that applies the approved hardwood color window and palette to the retained `dark_wood` diffuse source and copies one existing indigo substrate color map without any Blender composition.

- [x] **Step 2: Validate the desk and substrate images**

Run image inspection and confirm both images are opaque textures, have useful review resolution, and contain no baked interface geometry.

- [x] **Step 3: Implement candidate-04 timeline group export**

Create a Blender script that hides every mesh except the approved housing group or handle group, uses the approved orthographic camera and lighting, renders with transparent film, and aligns both exports to the same square coordinate system as `gasket-frame.png`.

- [x] **Step 4: Render and inspect the timeline layers**

Run Blender twice and confirm transparent corners, nonempty content, a nearly full-width lower housing, and a small independent handle.

### Task 2: Build and capture the static browser composition

**Files:**
- Create: `review/interface-static/index.html`
- Create: `review/interface-static/style.css`
- Create: `scripts/capture-interface-static.mjs`
- Create: `review/interface-static/cursebreaker-approved-desk.png`

**Interfaces:**
- Consumes: the five approved image layers from Task 1.
- Produces: one reviewable browser capture and no application behavior.

- [x] **Step 1: Create the static document**

Use semantic-neutral image layers only. Do not add scripts, buttons, links, controls, text, paper placeholders, or hidden interactive regions.

- [x] **Step 2: Compose the square central assembly**

Center a square assembly at nearly viewport height, clip the oversized substrate to the authored aperture, overlay the gasket, and align the fixed timeline layers to their candidate-04 coordinates.

- [x] **Step 3: Capture the browser render**

Serve the worktree locally and capture the page at 1600×1000 with headless Chromium.

- [x] **Step 4: Validate scope and appearance**

Confirm the HTML has no script or interactive element; inspect the capture for square lens geometry, bare side regions, correct substrate fit, and integrated timeline; confirm git diff contains no runtime source changes.
