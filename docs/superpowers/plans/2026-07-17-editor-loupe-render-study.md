# Editor Loupe Render Study Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Render four finished editor-loupe construction candidates that share the approved silhouette and gasket-derived materials, then present isolated and game-scale comparisons over HTTP.

**Architecture:** One Blender Python builder owns the shared scene, camera, lighting, procedural materials, normalized loupe envelope, and four candidate-specific mechanical constructions. A separate deterministic composition script places transparent renders over the already-approved desk/gasket capture and builds contact sheets. A static review page displays only generated evidence; it contains no proof or editor interaction.

**Tech Stack:** Blender 4.5.11, Python 3, Pillow, Cycles/EEVEE Next, HTML, CSS, headless image inspection.

## Global Constraints

- Preserve the approved circular aperture, narrow rim, 42° down-right handle, small terminal grip, and complete absence of application chrome.
- Candidate A is the literal gasket derivative; B is refined; C is heavy field; D is precision.
- All candidates share camera, aperture, outer diameter, handle centerline, lighting, exposure, desk crop, and comparison placement.
- Use the approved archaeological-bronze and dark-gunmetal hierarchy in every candidate.
- Every option must be textured, clearly lit, and corrected after full-resolution and game-scale inspection.
- Do not modify approved desk, gasket, timeline, folio, or substrate assets.
- Do not integrate with the game or promote runtime loupe assets.
- Do not run physics tests.
- End each commit with an empty worktree.

---

### Task 1: Build the shared high-fidelity render scene and candidate models

**Files:**
- Create: `scripts/assets/build-editor-loupe-study.py`
- Create: `assets/interface/source/blender/editor-loupe-study.blend`
- Create: `review/editor-loupe-study/isolated/candidate-{a,b,c,d}.png`
- Create: `tests/review/editor-loupe-study.test.ts`

**Interfaces:**
- Consumes: Blender 4.5.11 and the normalized measurements in the design spec.
- Produces: `build_scene(output_root: Path)`, four candidate collections, one saved `.blend`, and four 1400×1400 RGBA renders.

- [ ] **Step 1: Write the failing output-contract test**

Test that the builder exists and, once rendered, every isolated image is 1400×1400 RGBA, has nonempty alpha, transparent corners, and a transparent circular aperture centered at the shared normalized location. Assert the four alpha bounds differ by no more than two pixels at the circular rim while their opaque RGB content is not identical.

- [ ] **Step 2: Run the test and verify RED**

```bash
npm test -- --run tests/review/editor-loupe-study.test.ts
```

Expected: failure because the builder and images do not exist.

- [ ] **Step 3: Implement shared scene authorities**

In `build-editor-loupe-study.py` define:

```python
APERTURE_RADIUS = 5.0
OUTER_RADIUS = 5.6
HANDLE_ANGLE_DEGREES = -42.0
HANDLE_START = 5.15
HANDLE_END = 9.15
RENDER_SIZE = 1400
```

Create reusable helpers for revolved annular profiles, beveled extruded handle outlines, socket/yoke construction, fasteners, collars, procedural bronze/gunmetal/dark-grip materials, candidate collections, and deterministic render setup. Use one orthographic camera and the same broad area-key/fill/world settings for every candidate.

- [ ] **Step 4: Implement Candidate A**

Model one three-stage gasket-derived annular profile with bronze outer land, gunmetal channel, bronze inner lip, a compact two-fastener socket, dark structural handle core, bronze side cheeks/collars, and sparse contact wear.

- [ ] **Step 5: Implement Candidate B**

Model a smoother two-step annular profile, continuous gunmetal lens bed, tapered neck, visible structural spine, shaped dark grip, and restrained longitudinal grip texture.

- [ ] **Step 6: Implement Candidate C**

Model a deeper gunmetal rear cradle within the shared outer envelope, integrated ribbed yoke, faceted gunmetal handle, bronze wear rails, sparse aligned fasteners, and compact capped grip.

- [ ] **Step 7: Implement Candidate D**

Model a narrow bronze retaining ring, inset gunmetal channel, fine bronze collet, collared socket joint, machined dark grip, bronze end collars, and restrained engraved index ticks that cannot read as controls.

- [ ] **Step 8: Render, save source, and verify GREEN**

Run Blender headlessly with the builder, save the resulting source to `assets/interface/source/blender/editor-loupe-study.blend`, render the four isolated outputs, then run the focused test. Expected: four passing image contracts.

- [ ] **Step 9: Commit**

```bash
git add scripts/assets/build-editor-loupe-study.py assets/interface/source/blender/editor-loupe-study.blend review/editor-loupe-study/isolated tests/review/editor-loupe-study.test.ts
git commit -m "assets: build editor loupe candidates"
```

---

### Task 2: Compose controlled game-scale evidence

**Files:**
- Create: `scripts/build-editor-loupe-comparison.py`
- Create: `review/editor-loupe-study/context/candidate-{a,b,c,d}.png`
- Create: `review/editor-loupe-study/comparison-context.png`
- Create: `review/editor-loupe-study/comparison-isolated.png`
- Modify: `tests/review/editor-loupe-study.test.ts`

**Interfaces:**
- Consumes: the four isolated RGBA renders and `review/interface-static/cursebreaker-approved-desk.png` without modifying either authority.
- Produces: four 1600×1000 in-context images and two labeled 2×2 contact sheets.

- [ ] **Step 1: Extend the failing test**

Assert every context image is 1600×1000, its exterior pixels match the approved desk composition outside the loupe bounds, and all four use the same loupe alpha placement. Assert contact sheets contain all four labeled cells at identical dimensions.

- [ ] **Step 2: Verify RED**

Run the focused test and expect missing comparison outputs.

- [ ] **Step 3: Implement deterministic composition**

Use Pillow to scale each isolated render to the same 860-pixel square, derive a soft offset contact shadow from its alpha, place it at `(640, 54)` over a copy of the approved 1600×1000 composition, and composite the loupe without changing the source. Build 2×2 context and isolated sheets with labels outside candidate pixels.

- [ ] **Step 4: Generate and verify GREEN**

Run the composer and focused test. Expected: all comparison contracts pass.

- [ ] **Step 5: Commit**

```bash
git add scripts/build-editor-loupe-comparison.py review/editor-loupe-study tests/review/editor-loupe-study.test.ts
git commit -m "review: compose editor loupe study"
```

---

### Task 3: Critical visual correction pass

**Files:**
- Modify: `scripts/assets/build-editor-loupe-study.py`
- Modify: `assets/interface/source/blender/editor-loupe-study.blend`
- Modify: `review/editor-loupe-study/**/*.png`
- Modify if contracts reveal a real omission: `tests/review/editor-loupe-study.test.ts`

- [ ] **Step 1: Inspect every isolated render at original resolution**

Check silhouette, aperture ratio, stepped profile, socket/handle continuity, bevel scale, material response, texture artifacts, alpha fringes, exposure, and grip size.

- [ ] **Step 2: Inspect the context contact sheet at 1600×1000 scale**

Check gasket-family resemblance, visual hierarchy over the desk/main gasket, readable differences, shadow seating, host-interface legibility, and whether any candidate looks primitive, cartoony, dark, or ornamented like controls.

- [ ] **Step 3: Correct authoritative causes and rerender**

Make geometry, material, camera, or light corrections in the builder—not offsets or paint-over patches in the contact sheet. Rerender all candidates after any shared-authority change.

- [ ] **Step 4: Repeat inspection until every candidate meets the presentation floor**

Do not present a knowingly defective candidate merely to preserve a four-option count.

- [ ] **Step 5: Run focused validation and commit corrections**

```bash
npm test -- --run tests/review/editor-loupe-study.test.ts
git diff --check
git add scripts/assets/build-editor-loupe-study.py assets/interface/source/blender/editor-loupe-study.blend review/editor-loupe-study tests/review/editor-loupe-study.test.ts
git commit -m "fix(review): refine editor loupe candidates"
```

---

### Task 4: Serve the visual comparison over HTTP

**Files:**
- Create: `review/editor-loupe-study/index.html`
- Create: `review/editor-loupe-study/style.css`
- Create: `scripts/validate-editor-loupe-study.mjs`
- Modify: `tests/review/editor-loupe-study.test.ts`

**Interfaces:**
- Consumes: the final isolated, context, and contact-sheet images.
- Produces: a static HTTP review page with full-resolution links and no application behavior.

- [ ] **Step 1: Extend the failing page contract**

Assert the page contains all eight primary candidate images, candidate names, full-resolution links, no script, no buttons/inputs, and no references to runtime game code.

- [ ] **Step 2: Implement the static review page**

Use a dark neutral page with one context comparison, one isolated comparison, and per-candidate full-size sections. Keep labels outside images and do not add aesthetic decoration that competes with the renders.

- [ ] **Step 3: Validate and serve**

```bash
node scripts/validate-editor-loupe-study.mjs
npx vite review/editor-loupe-study --host 0.0.0.0 --port 4175
```

Expected: validator exits 0 and `http://localhost:4175/` returns 200.

- [ ] **Step 4: Commit and verify clean status**

```bash
git add review/editor-loupe-study/index.html review/editor-loupe-study/style.css scripts/validate-editor-loupe-study.mjs tests/review/editor-loupe-study.test.ts
git commit -m "review: serve editor loupe comparison"
git status --porcelain=v1
```

Expected: no worktree output while the committed HTTP server remains available for user review.
