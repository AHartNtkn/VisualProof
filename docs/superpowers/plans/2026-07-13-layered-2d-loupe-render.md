# Layered 2D Loupe Render Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the top-lit beauty render with deterministic, light-free 2D asset passes and a controlled review composite whose frame brightness is even from top to bottom.

**Architecture:** The temporary Blender script continues to own the approved loupe geometry, but production rendering becomes pass-oriented. Emissive material-color passes, AO/contact passes, view-dependent bevel accents, ownership masks, and a derived soft shadow are exported independently for the frame, glass, lever housing, and movable handle; Blender's compositor combines them over a review-only walnut background. No production light object or physical source gradient participates.

**Tech Stack:** Blender 4.5.11 LTS, Blender Python API, Blender compositor, ImageMagick, Vite static review server

## Global Constraints

- The interface consumes 2D image assets; it does not render the loupe as runtime 3D.
- Production scenes contain no light objects.
- Base color is evenly illuminated and contains no directional brightness gradient.
- Depth comes from restrained AO/contact darkening at declared opacity.
- Accents are sparse bevel/edge cues at declared opacity and imply no visible lamp.
- Glass contains no baked lamp reflection; runtime shaders own live distortion and optical effects.
- Frame, glass, lever housing, movable handle, masks, and cast shadow remain independently composable.
- Work remains under `/tmp/central-lens-reference-rebuild/` until aesthetic approval.
- No proof interaction, timeline semantics, physics, or physics tests change.

---

### Task 1: Light-Free Pass Materials and Ownership Groups

**Files:**
- Modify: `/tmp/central-lens-reference-rebuild/build_reference_loupe.py`

**Interfaces:**
- Consumes: the approved square-lens geometry and named Blender objects created by `build_reference_loupe.py`
- Produces: `flat_procedural_material(name, dark, light, noise_scale) -> bpy.types.Material`, `flat_material(name, color) -> bpy.types.Material`, pass materials named `Depth pass`, `Accent pass`, and `Mask pass`, plus `asset_groups: dict[str, set[str]]`

- [ ] **Step 1: Record the displaced lighting path**

Run:

```bash
rg -n 'Broad workshop source|area_light\(|scene\.view_settings\.exposure' /tmp/central-lens-reference-rebuild/build_reference_loupe.py
```

Expected: the script creates `Broad workshop source` and applies exposure `0.8`.

- [ ] **Step 2: Convert production materials to even emissive color**

Replace the Principled output of procedural metals and simple production materials with emission output while retaining their existing color/noise inputs:

```python
def emission_output(node_tree, color_socket, strength=1.0):
    out = node_tree.nodes.new("ShaderNodeOutputMaterial")
    emission = node_tree.nodes.new("ShaderNodeEmission")
    emission.inputs["Strength"].default_value = strength
    node_tree.links.new(color_socket, emission.inputs["Color"])
    node_tree.links.new(emission.outputs["Emission"], out.inputs["Surface"])
    return emission
```

The glass base uses `(0.008, 0.018, 0.023, 1.0)` through emission and has no Principled specular, coat, or transmission response. The review-only walnut material retains procedural grain through emission.

- [ ] **Step 3: Add light-free depth, accent, and mask materials**

Add these constructors:

```python
def depth_pass_material():
    material = bpy.data.materials.new("Depth pass")
    material.use_nodes = True
    nodes = material.node_tree.nodes
    nodes.clear()
    ao = nodes.new("ShaderNodeAmbientOcclusion")
    ao.inputs["Distance"].default_value = 0.75
    ao.inputs["Samples"].default_value = 16
    emission_output(material.node_tree, ao.outputs["AO"])
    return material


def accent_pass_material():
    material = bpy.data.materials.new("Accent pass")
    material.use_nodes = True
    nodes = material.node_tree.nodes
    nodes.clear()
    layer = nodes.new("ShaderNodeLayerWeight")
    invert = nodes.new("ShaderNodeMath")
    invert.operation = "SUBTRACT"
    invert.inputs[0].default_value = 1.0
    power = nodes.new("ShaderNodeMath")
    power.operation = "POWER"
    power.inputs[1].default_value = 3.0
    material.node_tree.links.new(layer.outputs["Facing"], invert.inputs[1])
    material.node_tree.links.new(invert.outputs[0], power.inputs[0])
    emission_output(material.node_tree, power.outputs[0])
    return material


def mask_pass_material():
    return flat_material("Mask pass", (1.0, 1.0, 1.0))
```

- [ ] **Step 4: Define mutually exclusive render groups**

Create `asset_groups` after geometry construction with these exact keys and membership rules:

```python
asset_groups = {
    "glass": {"Squared loupe glass"},
    "lever-housing": {name for name in renderable_names if name.startswith(("Timeline brass bezel", "Timeline recessed well", "Timeline machined rail", "Travel slot", "Index rivet", "Timeline end bearing", "End bearing screw"))},
    "lever-handle": {name for name in renderable_names if name.startswith(("Timeline carriage shoe", "Carriage index tongue", "Timeline black grip nub", "Left brass nub collar", "Right brass nub collar", "Left nub axle", "Right nub axle", "Grip turning line"))},
}
excluded = {"Walnut desk", "Diagram field"}
assigned = set().union(*asset_groups.values())
asset_groups["frame"] = renderable_names - assigned - excluded
assert not (asset_groups["frame"] & assigned)
assert set().union(*asset_groups.values()) == renderable_names - excluded
```

`renderable_names` contains mesh-object names only. Duplicate Blender names created from repeated helper calls are accepted by their generated suffixes because each membership rule uses `startswith`.

- [ ] **Step 5: Delete the production light rig**

Remove `area_light`, all light creation calls, and explicit exposure compensation. Before saving the `.blend`, assert:

```python
assert not [obj for obj in bpy.data.objects if obj.type == "LIGHT"]
```

### Task 2: Deterministic Asset-Pass Export

**Files:**
- Modify: `/tmp/central-lens-reference-rebuild/build_reference_loupe.py`
- Create: `/tmp/central-lens-reference-rebuild/passes/*.png`

**Interfaces:**
- Consumes: `asset_groups`, flat production materials, and the shared straight-on camera
- Produces: `render_group_pass(group_name: str, pass_name: str, override_material: bpy.types.Material | None, path: str) -> None` and full-canvas PNG files named `{group}-{base|depth|accent|mask}.png`

- [ ] **Step 1: Record the missing pass directory**

Run:

```bash
test -d /tmp/central-lens-reference-rebuild/passes
```

Expected: nonzero exit before implementation.

- [ ] **Step 2: Implement isolated pass rendering**

Add a renderer that stores and restores visibility and material slots:

```python
def render_group_pass(group_name, pass_name, override_material, path):
    members = asset_groups[group_name]
    saved_visibility = {obj.name: obj.hide_render for obj in bpy.context.scene.objects}
    saved_materials = {}
    try:
        for obj in bpy.context.scene.objects:
            if obj.type != "MESH":
                continue
            obj.hide_render = obj.name not in members
            if obj.name in members and override_material is not None:
                saved_materials[obj.name] = list(obj.data.materials)
                obj.data.materials.clear()
                obj.data.materials.append(override_material)
        scene.render.film_transparent = True
        scene.render.filepath = path
        bpy.ops.render.render(write_still=True)
    finally:
        for obj in bpy.context.scene.objects:
            obj.hide_render = saved_visibility[obj.name]
            if obj.name in saved_materials:
                obj.data.materials.clear()
                for material in saved_materials[obj.name]:
                    obj.data.materials.append(material)
```

- [ ] **Step 3: Export all declared passes**

Create `/tmp/central-lens-reference-rebuild/passes` and render these sixteen outputs at `1536x864`:

```python
for group_name in ("frame", "glass", "lever-housing", "lever-handle"):
    render_group_pass(group_name, "base", None, os.path.join(PASSES, f"{group_name}-base.png"))
    render_group_pass(group_name, "depth", depth_material, os.path.join(PASSES, f"{group_name}-depth.png"))
    render_group_pass(group_name, "accent", accent_material, os.path.join(PASSES, f"{group_name}-accent.png"))
    render_group_pass(group_name, "mask", mask_material, os.path.join(PASSES, f"{group_name}-mask.png"))
```

- [ ] **Step 4: Export the review-only walnut background**

Hide every object except `Walnut desk`, render its emissive procedural material with `film_transparent = False`, and write `/tmp/central-lens-reference-rebuild/passes/review-background.png`. Restore all visibility afterward.

- [ ] **Step 5: Verify output completeness and alpha**

Run:

```bash
rg --files /tmp/central-lens-reference-rebuild/passes | sort
identify /tmp/central-lens-reference-rebuild/passes/*.png
```

Expected: seventeen PNG files; every file is `1536x864`; the sixteen mechanical pass files report RGBA.

### Task 3: Blender-Composited Review and Tonal Validation

**Files:**
- Modify: `/tmp/central-lens-reference-rebuild/build_reference_loupe.py`
- Modify: `/tmp/central-lens-reference-rebuild/index.html`
- Create: `/tmp/central-lens-reference-rebuild/passes/frame-shadow.png`
- Create: `/tmp/central-lens-reference-rebuild/renders/04-layered-2d-review.png`

**Interfaces:**
- Consumes: the seventeen Task 2 pass files
- Produces: `compose_layered_review() -> None`, a separate transparent shadow, and the canonical review composite

- [ ] **Step 1: Build one compositor chain per moving group**

For each group, load its base, depth, accent, and mask images. Use `CompositorNodeMixRGB` with `blend_type = 'MULTIPLY'` and factor `0.18` to mix depth into base; then use a second `CompositorNodeMixRGB` with `blend_type = 'ADD'` and factor `0.10` for the accent. Apply the mask alpha with `CompositorNodeSetAlpha`.

- [ ] **Step 2: Derive the independent soft shadow**

Union the four mask images, blur the union with `CompositorNodeBlur` using `filter_type = 'GAUSS'`, `size_x = 18`, and `size_y = 18`, offset it downward by six pixels, and apply it as alpha to `(0.0, 0.0, 0.0, 0.34)`. Connect this image to `CompositorNodeComposite`, set `scene.render.filepath` to `passes/frame-shadow.png`, hide scene geometry, and call `bpy.ops.render.render(write_still=True)` so Blender writes the exact declared filename without frame-number suffixes.

- [ ] **Step 3: Assemble the review composite**

Alpha-over the soft shadow and the four composited moving groups onto `review-background.png` in this order: shadow, frame, lever housing, glass, lever handle. Reconnect `CompositorNodeComposite` to this assembled image, set `scene.render.filepath` to `renders/04-layered-2d-review.png`, and call `bpy.ops.render.render(write_still=True)`. The compositor node tree and declared factors remain saved in `central-loupe-reference-rebuild.blend`.

- [ ] **Step 4: Verify no production lights and declared files**

Run:

```bash
.tools/blender/4.5.11/blender --background /tmp/central-lens-reference-rebuild/central-loupe-reference-rebuild.blend --python-expr "import bpy; lights=[o.name for o in bpy.data.objects if o.type=='LIGHT']; print('LIGHTS', lights); assert not lights"
identify /tmp/central-lens-reference-rebuild/renders/04-layered-2d-review.png /tmp/central-lens-reference-rebuild/passes/frame-shadow.png
```

Expected: `LIGHTS []`, exit `0`, and both images are `1536x864`.

- [ ] **Step 5: Measure top-to-bottom brass consistency**

Run these ImageMagick measurements on matched unobstructed aperture-frame runs:

```bash
convert /tmp/central-lens-reference-rebuild/renders/04-layered-2d-review.png -crop 360x18+588+47 -colorspace Gray -format '%[fx:mean]\n' info:
convert /tmp/central-lens-reference-rebuild/renders/04-layered-2d-review.png -crop 360x18+588+693 -colorspace Gray -format '%[fx:mean]\n' info:
```

Expected: the absolute difference divided by the larger mean is at most `0.12`. If either crop intersects a mechanical joint after rendering, move both crops by the same horizontal amount while keeping their dimensions and matched material role.

- [ ] **Step 6: Update and verify the HTTP review**

Make `04-layered-2d-review.png` the first reconstruction figure. State that it is assembled from light-free base, depth, accent, mask, and shadow layers; retain the exact generated reference and expose individual passes below the composite.

Run:

```bash
curl -I http://127.0.0.1:4173/
google-chrome --headless=new --disable-gpu --no-sandbox --window-size=1440,1000 --screenshot=/tmp/central-lens-reference-rebuild/http-review.png http://127.0.0.1:4173/
git status --short
```

Expected: HTTP `200`, Chrome exits `0`, the review page shows the new composite without missing images, and repository status contains no source, physics, proof-interaction, timeline-semantic, or test changes.
