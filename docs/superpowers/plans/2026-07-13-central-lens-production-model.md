# Central Lens Production Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce one reviewable, production-intent central-lens model whose coherent chassis, lens seat, and near-full-width timeline mechanism can be judged before repository asset replacement.

**Architecture:** An artist-editable Blender file owns the geometry. One annular quad subdivision cage owns the brass chassis; a curve-derived gasket and separate glass volume depend on its aperture; a separately movable handle and physically attached guide assembly occupy the integrated lower chassis. Disposable construction scripts and review renders remain under `/tmp/central-lens-production/` until aesthetic approval, so current game assets and interaction code remain untouched.

**Tech Stack:** Blender 4.5.11 LTS, Blender Python API for repeatable initial construction and diagnostics, Eevee review rendering, HTML over a local HTTP server.

## Global Constraints

- The lens is square, straight-on, and nearly viewport-height in the intended composition.
- The chassis is one authored surface, not four rails, stacked rounded rectangles, or curve-swept tubing.
- A border or rounded-square reading is allowed when it follows from coherent construction.
- The gasket is dark and visibly seats a separate lens.
- The lens center remains visually plain; mild edge distortion belongs to the later runtime shader.
- The timeline mechanism spans most of the lower frame and has visible guide, stop, and attachment logic.
- No menus, legends, title bars, orbiting controls, or new interactions are introduced.
- No game assets, interaction code, physics, or generated runtime files change before aesthetic approval.

---

### Task 1: Production-intent geometry and diagnostic review

**Files:**
- Create: `/tmp/central-lens-production/build.py`
- Create: `/tmp/central-lens-production/central-lens-v2.blend`
- Create: `/tmp/central-lens-production/index.html`
- Create: `/tmp/central-lens-production/renders/*.png`

**Interfaces:**
- Consumes: the approved physical hierarchy and the validated subdivision/derived-curve workflow.
- Produces: one editable `.blend` authority plus straight-on, three-quarter, silhouette, and control-cage review evidence.

- [ ] **Step 1: Construct the authoritative chassis cage**

Create one closed annular quad mesh with independent aperture and outer contours, a broadened lower structural region, a shallow fascia profile, support loops only at the lens seat and exterior edge, and Catmull-Clark subdivision at render level two. Name the object `Chassis_Authority`; retain the unsubdivided control cage in the `.blend`.

- [ ] **Step 2: Construct dependent seating geometry**

Create `Gasket_Path` from the aperture contour and use a Geometry Nodes `Curve to Mesh` graph to derive a dark compliant gasket. Create a separate shallow `Lens_Volume` behind it with a flat center and modeled edge thickness, without decorative glass figures or simulated refraction.

- [ ] **Step 3: Construct the lower mechanism**

Build a recessed guide occupying 78–86% of the chassis width, two end stops that visibly transfer into the lower body, a physical scale, and a separate centered `Timeline_Handle` whose horizontal translation is unobstructed. The guide may use beveled hard-surface parts because it is secondary mechanical geometry; it may not visually replace the chassis with another rectangular panel.

- [ ] **Step 4: Render diagnostic evidence**

Render neutral-material views at 1200×1200: intended straight-on framing, three-quarter raking light, orthographic silhouette, and an unsubdivided cage diagnostic. Use the same camera framing for geometry revisions so changes are directly comparable.

- [ ] **Step 5: Inspect and revise the source geometry**

Inspect every render at full resolution for pipe-like section, stacked-border ambiguity, faceting, corner pinching, arbitrary decoration, weak lower attachment, undersized mechanism, and wasted screen area. Revise the source model and rerender until the remaining issues are aesthetic decisions rather than construction defects.

- [ ] **Step 6: Publish review evidence without repository migration**

Create a local HTML review page that labels the model as a production-intent geometry candidate, shows all diagnostic views, and distinguishes modeled structure from deferred materials and runtime glass distortion. Verify the page and each image returns HTTP 200. Stop for aesthetic review; do not replace the committed `.blend`, generated images, manifest hashes, layout, or interaction code.
