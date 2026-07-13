---
name: interface-asset-pipeline-design
created: 2026-07-12
status: draft-for-user-review
---

# Cursebreaker Interface Asset Pipeline

## 1. Outcome

Cursebreaker will have a reproducible production-art pipeline capable of making a dark, materially convincing, magical-academic desk interface. The first production milestone is one reviewable central-lens family: the straight-on rounded-square lens frame, its dark glass treatment, and its near-full-width bottom timeline lever, rendered around real opening-puzzle content.

The milestone proves the material language and the production workflow before the rest of the desk is made. It does not implement the folios, vellum library, construction loupe, teacher presentation, thought effects, or culture-specific variants.

Generated concept images and earlier HTML/SVG mockups remain references only. They establish atmosphere or layout intent but are never production sources, trace targets, or substitutes for authored assets.

## 2. Fixed product constraints

The asset system must preserve these decisions:

- The live proof canvas remains the sole proof-surface and proof-input authority.
- The existing canvas interaction, coordinate, zoom, history, and hit-testing contracts do not change.
- The optical glass, gasket, and usable opening form a nearly viewport-height rounded square viewed straight-on. The surrounding chassis may be wider where its structure and integrated timeline require it; chassis proportion must not turn the optical opening into a rectangle.
- Nothing resembling a title bar, menu, orbiting button, unexplained indicator, or permanent legend appears within or around the glass.
- The timeline lever is centered across the bottom structural mass and spans most of the lens width. Its guide, end stops, and attachments must read as a substantial mechanism belonging to the chassis rather than a small control panel placed beside it.
- Decorative layers never handle pointer input. Application-owned geometry positions the proof canvas and timeline interaction above or through those layers.
- The material palette is dark walnut, subdued warm papers and leather, aged brass, dark glass, and the existing Dark (Slate) neon proof colors. Seals are not tan or brown.
- Mechanical interface assets use controlled layered 2D shading, not a photographed-object lighting model. Dark materials and surroundings establish the theme; directional brightness gradients, theatrical spots, baked lamp reflections, and underexposure do not.
- Physics behavior and physics validation are outside this work.
- Every material milestone is demonstrated with real game content and reviewed before it becomes the basis for further assets.

## 3. Production model

The pipeline is hybrid because mechanical and organic materials need different source authorities.

### 3.1 Mechanical assets

Blender owns modeled objects: the lens frame, lever assembly, construction loupe, fasteners, hinges, clips, and later culture-specific hardware. A committed `.blend` file is the editable authority for each asset family. A small Blender Python render script owns only repeatable scene setup and export operations such as camera, render engine, output resolution, transparency, color management, named pass visibility, compositing, and filenames. It does not replace the artist-editable model with an opaque one-off generated image.

Mechanical assets use an orthographic, axis-aligned camera. Geometry, wear, restrained ambient occlusion, contact depth, and sparse bevel accents create legible form; perspective distortion and physically simulated source lighting do not. Production scenes contain no light objects. Fixed random seeds and CPU rendering are used for reproducible exports.

Each mechanical source exports these named transparent passes for every independently composited moving group:

1. **Base:** even material color and wear with alpha, without directional illumination.
2. **Depth:** low-amplitude ambient occlusion and contact darkening, multiplied over the base at a declared opacity.
3. **Accent:** sparse edge and bevel highlights, added at a declared opacity without implying a visible lamp.
4. **Mask:** binary ownership masks for the frame, glass, lever housing, and movable handle.
5. **Shadow:** a separate soft cast/contact shadow used only when seating the asset on the desk.

The Blender compositor is the sole authority for combining these passes into review and runtime derivatives. It applies one declared color grade and opacity values; the desk, papers, proof content, and runtime glass effects never enter the mechanical source render. A review composite is derived evidence, not a parallel editable source.

### 3.2 Organic assets

GIMP `.xcf` documents own layered walnut, leather, paper, vellum, stains, edge wear, and masks. Layers retain separable base color, grain, wear, dirt, height cues, and alpha masks so later cultural art direction can vary without repainting a flattened image.

The first central-lens milestone does not require an external texture. Its brass, glass, wear, and shadowing are authored in Blender. When organic desk assets begin, selected CC0 texture inputs may be incorporated into the `.xcf` sources only after their origin, license, download URL, and checksum are recorded. Poly Haven is an approved source because its published license places its textures under CC0; it is not a requirement to use any particular Poly Haven asset.

### 3.3 Derived runtime assets

Transparent PNG files are the initial runtime format because they preserve authored alpha and can be emitted directly by the pinned renderer. WebP optimization is a later derivation only after the integrated interface has been profiled; it may not become a second hand-maintained source.

Every runtime image is generated from a named editable source. No runtime image may be edited directly. The application imports generated assets through its build graph rather than depending on machine-local paths.

## 4. Toolchain and repository ownership

Blender **4.5.11 LTS for Linux x64** is the pinned mechanical authoring and render version. Blender 4.5 is an active LTS line; Blender documents portable deployment and background command-line rendering. The local system satisfies Blender's published Linux requirement.

The binary is not committed. `scripts/assets/install-blender.sh` installs it beneath the ignored path `.tools/blender/4.5.11/`. The installer obtains the versioned archive and published checksum from Blender's release service, verifies the archive before extraction, rejects a version mismatch, and records the resolved archive checksum locally. It does not silently select a newer patch release.

The repository owns this layout:

```text
assets/interface/
  source/
    blender/          committed .blend authorities
    gimp/             committed .xcf authorities
    inputs/           selected external inputs and provenance records
  generated/          committed runtime PNG exports
  manifest.json       committed source/export/provenance contract
scripts/assets/
  install-blender.sh
  render-interface.sh
  blender/            deterministic render/export helpers
tests/assets/          pipeline and manifest validation
.tools/blender/        ignored local tool installation
```

The committed generated images let ordinary game builds run without Blender. The editable sources, scripts, and manifest prevent those images from becoming an unexplained binary authority.

## 5. Asset manifest

`assets/interface/manifest.json` is the single inventory for production interface art. Each asset-family entry records:

- stable asset and layer identities;
- authoritative source path and source checksum;
- required tool and exact version;
- render script and named scene/view layer;
- output paths, pixel dimensions, color space, and alpha mode;
- responsive stretch-safe insets or non-stretching status;
- external input identities with origin URL, license, and checksum;
- output checksums from the accepted canonical render;
- review state: `candidate` or `approved`.

The manifest does not contain layout coordinates or input geometry. Those remain application responsibilities. `approved` means the user accepted the asset milestone in realistic application context; a technically valid render alone remains `candidate`.

## 6. Central-lens family

The first family is deliberately small and separable:

1. **Frame:** one straight-on mechanical chassis with a rounded-square transparent opening, authored so its aperture corners and ornamental masses remain fixed while mechanically plain outer runs may accommodate the timeline assembly.
2. **Glass:** a separate rounded-square, restrained dark-glass overlay that adds edge depth and faint optical falloff without a baked lamp reflection, reducing proof legibility, or pretending to be the proof surface. Runtime shaders own distortion and live optical effects.
3. **Frame shadow:** a separate soft occlusion/cast-shadow layer so the frame can sit on later desk materials without baking a particular walnut image into the brass asset.
4. **Lever housing:** a near-full-width brass guide, notch, end-stop, and attachment assembly integrated into the bottom chassis.
5. **Lever handle:** a separate movable part whose application position represents the existing timeline cursor. Decorative artwork does not calculate history or cursor state.

The frame uses a declared nine-slice contract. Aperture corner quadrants and decorated junctions never stretch; only unornamented chassis runs may extend. The glass remains rounded-square and the shadow may scale continuously because neither owns semantic interaction geometry. The lever housing has one intrinsic aspect ratio, spans most of the lower frame, and remains inside the chassis silhouette; the handle translates only along the application-defined track.

The first source scene renders a 4096-by-4096 frame master and separately sized lever passes. This is a review master, not an unconditional shipping budget. After browser integration, the pipeline measures decoded dimensions, transferred bytes, and frame cost, then derives the smallest runtime resolution that remains visually equivalent at the supported display sizes. Compression or downsampling cannot precede the material review or disguise weak source work.

## 7. Application composition contract

Runtime composition follows this ownership order:

```text
desk and papers (later)
  → frame shadow
  → live proof canvas and its existing interaction surface
  → glass optical overlay
  → brass frame
  → application-owned timeline interaction geometry
  → lever housing and cursor-positioned handle artwork
```

All decorative image elements use `pointer-events: none`, are omitted from the accessibility tree, and receive no keyboard focus. The existing semantic timeline and canvas elements remain the accessible interactive surfaces. Asset insets may inform decoration sizing but never redefine canvas coordinates or proof hit regions.

The lens is sized from available viewport height first. Side content must yield before the lens becomes a small dashboard panel. Compact layouts may reduce surrounding desk context, but they preserve the square glass and the established canvas behavior.

## 8. Production and review flow

The pipeline has one linear authority path:

1. Provision the pinned Blender tool after checksum verification.
2. Edit the committed `.blend` or `.xcf` source.
3. Run `scripts/assets/render-interface.sh <family>`.
4. Render to a temporary staging directory, validate dimensions and alpha, and compare with the manifest.
5. Promote a deliberate candidate into `assets/interface/generated/` and update its manifest checksums.
6. Render the real application at desktop and compact viewports with an opening artifact under the lens.
7. Present those realistic renders for aesthetic review.
8. Mark the family `approved` only after user acceptance.

Failed download verification, missing sources, tool-version drift, render errors, undeclared outputs, invalid alpha, or manifest mismatch stop the pipeline with a specific error. The scripts do not use stale generated files as a success fallback.

## 9. Validation

Pipeline validation proves responsibility and result directly:

- A toolchain check reports exactly Blender 4.5.11 and rejects another version.
- A clean render uses only declared committed sources and declared external inputs.
- Manifest tests reject missing sources, missing provenance, invalid licenses, duplicate identities, path escapes, invalid dimensions/insets, undeclared generated files, and mismatched accepted-output checksums.
- A canonical CPU render with fixed seeds is compared to the accepted output. Exact file checksums verify canonical committed exports; a pixel comparison with a narrowly documented tolerance diagnoses renderer-level encoding variance without silently approving a visual change.
- Scene validation rejects any production light object or undeclared pass. Composite validation rebuilds the accepted image from the declared base, depth, accent, mask, and shadow inputs.
- Tonal validation compares matched unobstructed brass samples on the top and bottom aperture runs. Their median relative luminance may differ by at most 12 percent; edge accents and ambient-occlusion samples are excluded. The glass center contains no baked source reflection.
- Browser tests render real opening content at representative desktop and compact viewports and capture the full lens, glass, and lever composition.
- Interaction tests confirm the same canvas coordinate mapping and proof hit targets before and after decorative composition, confirm decorative layers cannot receive input, and confirm the lever artwork follows the existing timeline cursor.
- A repository scope check confirms no physics, proof-rule, proof-interaction, timeline-semantic, or proof-renderer files changed as part of the asset milestone.
- User approval of the integrated browser renders is required before the family becomes `approved` or the pipeline expands to the surrounding desk.

The physics battery stays off. Ordinary type checking, focused asset tests, focused application interaction tests, the production build, and browser render capture are the relevant checks.

## 10. Sources informing the tool decision

- [Blender 4.5 LTS dashboard](https://www.blender.org/get-involved/Dashboard/)
- [Blender production deployment](https://docs.blender.org/manual/es/4.5/advanced/deploying_blender.html)
- [Blender command-line rendering](https://docs.blender.org/manual/es/3.5/advanced/command_line/render.html)
- [Blender system requirements](https://www.blender.org/download/requirements/)
- [Blender 4.5 release index](https://mirror.clarkson.edu/blender/release/Blender4.5/)
- [Poly Haven license](https://polyhaven.com/license)
