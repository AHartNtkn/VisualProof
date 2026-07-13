# Square Lens and Broad Lighting Revision Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Revise the approved reference-led loupe candidate so its optical opening reads as a rounded square, its desktop composition reserves lateral paper space, and one broad soft source illuminates the dark materials clearly.

**Architecture:** The temporary Blender construction script remains the editable candidate authority until aesthetic approval. Optical proportions are owned together by the glass, diagram field, gasket, registration bead, and aperture plate; the chassis and timeline retain independent mechanically justified widths. A single rectangular area light and explicit exposure replace the three-light rig, and deterministic inspection scripts validate both scene structure and rendered framing.

**Tech Stack:** Blender 4.5.11 LTS, Blender Python API, ImageMagick, Vite static review server

## Global Constraints

- The optical glass, gasket, and usable opening form a nearly viewport-height rounded square viewed straight-on.
- The surrounding chassis may be wider where its structure and integrated timeline require it.
- The existing compact timeline nub and long recessed rail remain intact.
- One large, soft, slightly warm source above and forward of the loupe is the only light object.
- Dark materials and surroundings establish the theme; exposure must leave mechanical detail readable.
- Work remains under `/tmp/central-lens-reference-rebuild/` until aesthetic approval.
- No proof interaction, timeline semantics, physics, or physics tests change.

---

### Task 1: Rounded-Square Optical Assembly

**Files:**
- Modify: `/tmp/central-lens-reference-rebuild/build_reference_loupe.py`
- Regenerate: `/tmp/central-lens-reference-rebuild/central-loupe-reference-rebuild.blend`

**Interfaces:**
- Consumes: `rounded_prism(name, width, height, radius, y_front, y_back, material, center_z, bevel)`, `rounded_ring(name, outer, inner, radii, y_front, y_back, material, center_z, inner_center_z, bevel)`, and the existing reference-led chassis and timeline construction in `build_reference_loupe.py`
- Produces: a centered optical assembly whose visible glass width and height differ by no more than 2%, nested within an independently proportioned chassis

- [ ] **Step 1: Record the failing optical aspect ratio**

Run:

```bash
rg -n 'Squared loupe glass|Diagram field|Compressible lens gasket' /tmp/central-lens-reference-rebuild/build_reference_loupe.py
```

Expected: the glass is `11.72` units wide and `8.50` units high, so its ratio is about `1.38:1` and fails the rounded-square requirement.

- [ ] **Step 2: Replace the coupled optical dimensions**

Modify the aperture assembly as one coordinated set:

```python
lens_center_z = 0.75
rounded_ring("Worn brass aperture plate", (10.85, 10.25), (9.40, 9.40), (0.64, 0.54), -0.49, -0.29, brass, center_z=lens_center_z, bevel=0.055)
rounded_ring("Inner brass registration bead", (9.65, 9.65), (9.37, 9.37), (0.57, 0.52), -0.57, -0.46, brass_edge, center_z=lens_center_z, bevel=0.025)
rounded_ring("Compressible lens gasket", (9.38, 9.38), (9.04, 9.04), (0.52, 0.46), -0.535, -0.39, rubber, center_z=lens_center_z, bevel=0.018)
rounded_prism("Squared loupe glass", 9.05, 9.05, 0.47, -0.43, -0.20, glass, center_z=lens_center_z, bevel=0.065)
rounded_prism("Diagram field", 8.81, 8.81, 0.40, -0.11, 0.02, black, center_z=lens_center_z, bevel=0.02)
```

Retain the current depth order and materials. Reposition aperture joint plates and fasteners to the new plate edges instead of leaving hardware floating at the old width.

- [ ] **Step 3: Adjust the chassis width without assigning it square ownership**

Set the chassis and lower mechanism to coherent independent widths:

```python
rounded_prism("Continuous structural chassis", 13.55, 12.20, 0.78, -0.12, 0.72, steel, center_z=-0.08, bevel=0.075)
rounded_ring("Chassis front reveal", (13.20, 11.85), (12.65, 11.30), (0.68, 0.52), -0.31, -0.12, steel_edge, center_z=-0.02, bevel=0.045)
rounded_ring("Timeline brass bezel", (11.70, 1.58), (10.84, 0.91), (0.16, 0.09), -0.52, -0.30, brass, center_z=timeline_z, bevel=0.045)
rounded_prism("Timeline recessed well", 10.86, 0.93, 0.09, -0.41, -0.24, black, center_z=timeline_z, bevel=0.022)
rounded_prism("Timeline machined rail", 10.32, 0.54, 0.055, -0.54, -0.40, rail_metal, center_z=timeline_z, bevel=0.018)
```

Scale the timeline slot positions, end bearings, and lower service plates to the revised rail and chassis edges while preserving the compact central nub unchanged.

- [ ] **Step 4: Render and inspect the neutral clay construction**

Run:

```bash
.tools/blender/4.5.11/blender --background --python /tmp/central-lens-reference-rebuild/build_reference_loupe.py
```

Expected: Blender exits `0` and regenerates `02-reference-rebuild-clay.png`; the clay image shows a rounded-square opening, complete chassis, integrated lower apron, and no floating fasteners.

### Task 2: Single Broad Source and Review Evidence

**Files:**
- Modify: `/tmp/central-lens-reference-rebuild/build_reference_loupe.py`
- Modify: `/tmp/central-lens-reference-rebuild/index.html`
- Regenerate: `/tmp/central-lens-reference-rebuild/renders/01-reference-rebuild-front.png`
- Regenerate: `/tmp/central-lens-reference-rebuild/renders/02-reference-rebuild-clay.png`
- Regenerate: `/tmp/central-lens-reference-rebuild/renders/03-timeline-integration-detail.png`

**Interfaces:**
- Consumes: the Task 1 optical assembly and the existing orthographic camera
- Produces: one-light Blender scene, brighter dark-theme renders, and an HTTP review page showing the selected generated reference and revised candidate

- [ ] **Step 1: Record the failing light count**

Run:

```bash
rg -n 'area_light\(' /tmp/central-lens-reference-rebuild/build_reference_loupe.py
```

Expected: three light-creation calls are present.

- [ ] **Step 2: Replace the lighting rig**

Replace all three calls with one rectangular source:

```python
key = area_light("Broad workshop source", (0.0, -9.0, 8.0), 2400, (1.0, 0.86, 0.70), 11.0)
key.data.shape = "RECTANGLE"
key.data.size = 11.0
key.data.size_y = 8.0
scene.view_settings.exposure = 0.8
```

Keep the world near-black. Do not add fill, rim, spot, point, or emissive illumination objects.

- [ ] **Step 3: Verify the authoritative scene structure**

Run:

```bash
.tools/blender/4.5.11/blender --background /tmp/central-lens-reference-rebuild/central-loupe-reference-rebuild.blend --python-expr "import bpy; lights=[o for o in bpy.data.objects if o.type=='LIGHT']; print('LIGHT_COUNT', len(lights)); print('LIGHTS', [(o.name, o.data.type, o.data.shape) for o in lights]); assert len(lights)==1 and lights[0].data.type=='AREA' and lights[0].data.shape=='RECTANGLE'"
```

Expected: `LIGHT_COUNT 1`, followed by the broad workshop source as a rectangular area light, and exit `0`.

- [ ] **Step 4: Verify proportions from the source and rendered output**

Run:

```bash
rg -n 'Squared loupe glass", 9\.05, 9\.05|camera\.data\.ortho_scale = 23\.0' /tmp/central-lens-reference-rebuild/build_reference_loupe.py
identify /tmp/central-lens-reference-rebuild/renders/01-reference-rebuild-front.png
```

Expected: both source declarations match and the render is `1536x864`; visual inspection shows the complete height-driven loupe with broad desk gutters at left and right.

- [ ] **Step 5: Update and verify the HTTP review page**

Change the review copy to describe the rounded-square optical opening and single broad source. Keep the original recovered image unaltered as the first comparison figure.

Run:

```bash
curl -I http://127.0.0.1:4173/
google-chrome --headless=new --disable-gpu --no-sandbox --window-size=1440,1000 --screenshot=/tmp/central-lens-reference-rebuild/http-review.png http://127.0.0.1:4173/
```

Expected: HTTP `200`, Chrome exits `0`, and the screenshot shows the reference followed by the revised material and clay renders without missing images or overflow.

- [ ] **Step 6: Preserve repository scope**

Run:

```bash
git status --short
```

Expected: no source, proof-interaction, timeline-semantic, physics, or test files are modified; only the already-approved documentation commits exist in the worktree.
