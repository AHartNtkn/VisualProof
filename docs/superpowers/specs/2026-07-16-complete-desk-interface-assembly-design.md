---
name: complete-desk-interface-assembly-design
created: 2026-07-16
status: draft-for-user-review
---

# Cursebreaker Complete Desk Interface Assembly

## 1. Outcome

Cursebreaker will have one working browser interface assembled from independent approved assets around the existing live proof engine. The demonstration will be as complete as current approved design decisions allow: a full-bleed Natural-indigo hardwood desk, left artifact folio, right solved-vellum library, central square loupe, deterministic puzzle substrate, live backward proof diagram, optical layer, approved mechanical frame and gasket, full-width timeline mechanism with independent movable handle, teacher dialogue, and pointer-adjacent invalid-move thoughts.

The result is the real game shell, not a static concept page and not a Blender composition. Puzzle selection, proof interaction, timeline scrubbing, substrate selection, refusal feedback, and responsive layout operate in HTML. Blender is used only to export isolated mechanical PNG layers from the already approved model.

This milestone completes the central visual assembly and establishes the asset contracts needed for later refinement. Paper ornament, typography, and character portrait treatment that have not been aesthetically approved remain restrained and provisional rather than being presented as finished art.

## 2. Fixed responsibility model

The runtime composition has one owner per responsibility:

```text
HTML application
├── full-bleed desk texture
├── left artifact folio and puzzle selection
├── right solved-vellum library
├── teacher dialogue surface
└── central responsive square stage
    ├── deterministic overscanned substrate
    ├── live ProofFrontViewport canvas
    ├── optical glass image and display shader
    ├── frame shadow image
    ├── approved gasket/frame image
    └── semantic timeline control
        ├── fixed housing image
        └── independently translated handle image
```

No image may contain another layer's responsibility. In particular:

- The frame image contains no desk, glass, diagram field, proof, timeline, or background.
- The glass image contains no proof, substrate, frame, or baked central reflection.
- The timeline housing contains no movable handle.
- The timeline handle contains its carriage, collars, axle, grip, and small knob as one independently translated mechanical part.
- The desk image contains no interface objects.
- Substrate images contain material appearance only and do not contain a rounded artifact silhouette, proof, lens, or gasket.
- Teacher dialogue and refusal thoughts are HTML, not baked artwork.

All decorative images use `pointer-events: none` and are absent from the accessibility tree. The existing canvas and semantic slider remain the only proof and timeline interaction authorities.

## 3. Approved visual authorities

### 3.1 Mechanical family

The approved source is:

`/tmp/central-loupe-texture-comparison-20260715/candidate-04/scene.blend`

It owns the selected Gunmetal and archaeological bronze material treatment and the final integrated chassis geometry. The game repository receives a durable copy as the central-lens Blender source before export.

The family exports five runtime images:

| Asset | Output | Master dimensions | Alpha contract |
|---|---|---:|---|
| gasket/frame | `gasket-frame.png` | 4096×4096 | transparent exterior and exact gasket aperture |
| glass | `glass.png` | 4096×4096 | transparent exterior; broad clear center; optical edge only |
| frame shadow | `frame-shadow.png` | 4096×4096 | soft alpha only outside/under frame; no opaque field |
| timeline housing | `timeline-housing.png` | 4096×1024 | transparent around fixed rail, well, notches, bearings, and end stops |
| timeline handle | `timeline-handle.png` | 1024×1024 | transparent around independently movable carriage, collars, axle, grip, and knob |

The semantic object grouping from the approved scene is authoritative:

- `glass`: `Squared loupe glass`.
- `timeline-housing`: timeline bezel, recessed well, rail, travel slots, index rivets, end bearings, and bearing screws.
- `timeline-handle`: carriage shoe, index tongue, black grip nub, collars, axles, and grip turning lines.
- `gasket/frame`: all remaining mechanical meshes except desk and diagram field.

The structural chassis contains a backing face across the aperture. Export therefore uses a render-only holdout derived from the authored gasket inner contour; the holdout changes exported alpha without changing the model.

The frame shadow is generated from the same frame ownership mask and declared blur/offset. It is not a second model or a baked desk shadow.

### 3.2 Desk

The approved desk is Natural-indigo hardwood. Its external authority is Poly Haven `dark_wood`, CC0, with retained diffuse, roughness, OpenGL normal, and displacement maps and exact checksums. The runtime receives:

- a color texture derived from the approved continuous-grain indigo remap;
- the original retained source maps and provenance record under `assets/interface/source/inputs/desk/`;
- one CSS presentation contract for scale, crop, and responsive cover behavior.

The runtime desk is not copied from a full Blender composition. It is a standalone organic texture with subtle CSS shading sufficient to seat the interface.

### 3.3 Puzzle substrates

The curated global library contains ten retained CC0 material families:

- smooth paper;
- cartonage paper;
- fibrous paper;
- fine linen;
- worn leather;
- fine wood;
- grey plaster;
- rough stone;
- oxidized metal;
- blackened metal.

Each family contributes a 2048×2048 indigo-remapped runtime color texture plus retained provenance. The game does not ship the rejected Blender full compositions. Runtime selection uses the stable versioned seed `substrate-v1:<puzzle-id>` and independently derives material, crop, scale, and rotation.

The substrate element is larger than the aperture and clipped by the lens stage. It has no border radius, bevel, box shadow, or independent visible silhouette. The gasket/frame image is the visible aperture boundary.

## 4. Repository asset ownership

The family becomes:

```text
assets/interface/
  source/
    blender/
      central-lens.blend
    inputs/
      desk/
        provenance.json
        color-source.jpg
        roughness-source.jpg
        normal-source.jpg
        height-source.jpg
      substrates/
        provenance.json
        <material-id>/
          color-source.*
          roughness-source.*
          normal-source.*
          height-source.*
          metalness-source.*   # only where supplied
  generated/
    central-lens/
      gasket-frame.png
      glass.png
      frame-shadow.png
      timeline-housing.png
      timeline-handle.png
    desk/
      natural-indigo-hardwood.png
    substrates/
      paper-smooth.png
      paper-cartonage.png
      paper-fibrous.png
      linen-fine.png
      leather-worn.png
      wood-fine.png
      plaster-grey.png
      stone-rough.png
      metal-oxidized.png
      metal-blackened.png
  manifest.json
```

`.staging` is disposable and never an alternative runtime authority. Obsolete generated names (`frame.png`, `shadow.png`, `lever-housing.png`, and `lever-handle.png`) are removed rather than aliased or retained beside the selected contract.

The manifest records source paths and hashes, output dimensions and hashes, alpha requirements, provenance, render tool/version, review status, and responsive usage. Layout coordinates remain application code, not manifest data.

## 5. Central HTML composition

### 5.1 Desk and workspace

The root `.curse-desk` fills the viewport and uses the approved desk texture. A low-amplitude vignette and ambient gradient may be CSS overlays, but they cannot simulate a spotlight or obscure the grain.

The desk uses three layout regions:

- left folio: cultures and available artifacts;
- central loupe: active puzzle and timeline;
- right vellum stack: completed seals and later manifest/dissolve affordances.

The loupe is sized from viewport height and remains a square. Desktop layouts reserve paper space on both sides. Compact layouts reduce or collapse side papers before shrinking the loupe below useful proof interaction size.

Slight paper rotations are decorative transforms on fixed layout regions; they do not make controls unpredictable.

### 5.2 Lens layer order

The stage uses one shared square coordinate system. Its layers are:

1. frame shadow seated on the desk behind the loupe;
2. substrate container clipped to the authored gasket aperture;
3. live proof canvas sized to that same aperture;
4. glass image and mild CSS/WebGL edge distortion;
5. gasket/frame PNG;
6. timeline housing;
7. semantic slider track;
8. movable timeline handle.

The proof canvas remains centered and fills the aperture. The substrate overscans it by at least 5 percent on all sides after crop and rotation. The center 72 percent of the optical transform is identity-mapped; only the perimeter transitions to at most 1.8 percent inward distortion. Input coordinates remain based on the existing undistorted proof viewport contract.

### 5.3 Timeline

The existing `GameTimeline` and `nearestTimelineCursor` remain authoritative. The fixed housing image spans nearly the entire lower chassis. The transparent semantic rail is aligned to the housing's travel path. The handle image translates along that rail using the existing cursor fraction.

Pointer dragging, arrow keys, Home, and End retain current behavior. The handle position is derived output; it never stores or calculates timeline state.

### 5.4 Side papers

The left folio shows two visible culture sections:

- the initial oldest propositional tradition, containing the six opening artifacts;
- the Myratic tradition, showing the first `∃P.P` artifact and its locked/unlocked state from the catalog.

Required and elective artifacts are visually distinct without presenting the content as a linear campaign. Puzzle names use the artifact naming direction already established; formal formulas remain metadata or an optional development detail, not primary player copy.

The right vellum stack derives from completed puzzles. At this milestone it renders solved entries and their availability honestly; it does not invent manifest/dissolve controls before those interactions are integrated.

## 6. Working behavior

The HTML demonstration is the real mount path and supports:

- selecting any unlocked opening artifact;
- rebuilding the session and proof viewport for the selected artifact;
- deterministic substrate selection and presentation from puzzle ID;
- existing proof pointer and keyboard interactions;
- existing undo/redo hotkeys;
- timeline pointer and keyboard scrubbing;
- independent visual handle movement;
- durable completion state within the mounted demo session;
- completed-puzzle vellum listing;
- authored teacher intervention display at opening and recognized events already represented by game data;
- pointer-adjacent refusal thoughts using the existing refusal callback;
- responsive desktop and compact layouts.

Invalid actions remain kernel refusals and do not change state. Teacher interventions remain separate authored events and are never represented as refusal thoughts.

The demo does not add a menu inside the lens, orbiting buttons, redundant undo/redo buttons, forward proof, a second proof front, or any game-only proof interaction.

## 7. Teacher and thought presentation

Teacher dialogue is a paper note or margin annotation outside the lens. It appears for authored interventions, shows concise text, and can be dismissed or advanced without blocking proof input longer than the authored beat requires. This milestone does not invent a finished character portrait.

Refusal thoughts remain pointer-adjacent HTML output:

- subtly red translucent paper/cloud treatment;
- non-color cue such as irregular edge or small thought-tail marks;
- concise first-person copy;
- automatic removal after the existing short lifetime;
- no persistent log and no effect on teacher state.

## 8. Provisional versus approved styling

Approved and fixed:

- Natural-indigo hardwood desk;
- dark overall theme;
- candidate-04 archaeological bronze and gunmetal mechanical treatment;
- central nearly viewport-height square loupe;
- neon Dark-theme proof colors;
- integrated near-full-width timeline;
- separate movable handle;
- subtle red pointer thoughts;
- left artifact papers and right vellum papers.

Provisional in this milestone:

- exact paper fibers, borders, typography, stamps, clips, and tabs;
- teacher note shape and typography;
- culture-specific paper ornament;
- animation timing beyond existing proof/timeline behavior.

Provisional styling must be coherent and restrained. It may demonstrate layout and behavior but is not marked approved in the manifest or documentation.

## 9. Validation

### 9.1 Asset validation

Direct checks require:

- exact declared dimensions and RGBA mode;
- nonempty alpha for every mechanical output;
- transparent corners for all mechanical layers;
- entirely transparent central aperture for gasket/frame;
- broad clear center for glass;
- housing and handle alpha bounding boxes that do not overlap unrelated frame regions;
- no desk, diagram field, glass, or timeline object in the wrong Blender export group;
- output hashes and source hashes matching the manifest;
- all external inputs retained with CC0 provenance;
- no undeclared generated or staging runtime authority.

### 9.2 Application validation

Focused tests prove:

- layer order and `pointer-events: none` on decoration;
- lens and proof aperture remain square and aligned at desktop and compact sizes;
- substrate covers the entire aperture under maximum declared rotation;
- substrate presentation exactly replays from puzzle ID;
- puzzle selection changes session content and deterministic substrate;
- timeline drag and keyboard changes cursor and handle position;
- proof canvas input and coordinate mapping survive decoration;
- invalid actions produce pointer-adjacent refusal thoughts without state change;
- teacher data renders separately;
- completed puzzles appear in the vellum stack;
- no old assistant import/export/library surface appears.

The production build and HTTP browser capture run at representative desktop and compact viewports. Captures include real opening-puzzle content and are inspected before any provisional paper styling is treated as final.

Physics tests remain disabled because this milestone does not change physics.

## 10. Completion boundary

This milestone is complete when:

1. all approved mechanical, desk, and substrate assets are durably collected and validated;
2. obsolete central-lens runtime/staging authorities are removed;
3. the real HTML game shell composes the layers correctly;
4. representative puzzle selection, proof interaction, timeline movement, teacher presentation, refusal thoughts, and responsive layouts work;
5. an HTTP review URL and desktop/compact evidence are presented;
6. remaining provisional paper/teacher aesthetics are clearly identified for later visual refinement.

It does not finalize every level, construction-loupe artwork, culture-specific ornament, teacher portrait, sound, or animation.
