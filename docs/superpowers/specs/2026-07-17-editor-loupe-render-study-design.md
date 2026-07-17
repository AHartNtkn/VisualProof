# Editor Loupe Render Study Design

**Date:** 2026-07-17
**Status:** Approved design; awaiting written-spec review
**Scope:** Four controlled, high-fidelity editor-loupe candidates for visual selection

## Outcome

Produce four finished Blender renders that determine how the already-approved
editor loupe inherits the main gasket's visual language. This is not another
silhouette exploration and not a material-swatch exercise. The candidates share
the approved circular form and differ in meaningful object construction: rim
profile, socket transition, handle construction, and restrained mechanical
detailing.

The comparison must make it possible to choose a production direction from the
rendered objects themselves. Every candidate is modeled, textured, lit, and
composited to a standard suitable for the actual game. No clay renders, dark
silhouettes, primitive assemblies, or untextured geometry are presented as
options.

## Fixed visual authority

The approved clean-loupe mock remains authoritative for:

- one large circular optical aperture;
- a narrow rim that leaves nearly all of the instrument useful for construction;
- an integrated handle extending diagonally down-right at approximately 42°;
- a small terminal grip rather than a broad cylindrical knob;
- an independent instrument overlapping the main lens and desk;
- no title, menu, buttons, labels, legend, or other application chrome.

The approved central gasket remains authoritative for:

- archaeological bronze against dark gunmetal;
- stepped, credible mechanical construction;
- realistic bevels, recesses, fasteners, roughness, and restrained wear;
- a dark, serious presentation rather than bright brass, cartoon outlines, or
  decorative fantasy filigree;
- straight-on composition with broad soft illumination and readable shadow detail.

## Controlled comparison envelope

All four candidates use one shared scene, camera, and normalized envelope:

- identical circular aperture;
- aperture diameter between 88% and 91% of the outer rim diameter;
- identical outer diameter and screen position;
- identical handle centerline, angle, and visible extension, with the handle
  extending approximately one third of the outer diameter beyond the rim;
- identical small terminal sizing-grip location and reachable area;
- identical orthographic camera, render resolution, exposure, light placement,
  desk crop, and main-gasket context;
- identical transparent aperture and layer registration.

Candidate construction may change local profiles within this envelope but may not
change the interaction silhouette, aperture capacity, handle reach, or comparison
composition. The same gasket-derived base materials are used across all four so
geometry is not confounded with unrelated palettes.

## Shared production quality

The loupe is modeled as one designed instrument. The rim, lens seat, socket,
handle, and terminal grip may be separate manufactured parts only where their
joint is mechanically legible. PNG boundaries, overlapping primitive rings, and
unexplained plates are not acceptable joints.

Every candidate receives:

- authored rim and handle profiles rather than default cylinders or tori;
- consistent bevel radii and weighted/shaded normals at final render scale;
- modeled recesses, collars, fasteners, seams, and grip features where specified;
- gasket-matched bronze and gunmetal materials with roughness variation, darker
  recess response, sparse contact wear, and no procedural noise large enough to
  read as damage or camouflage;
- a lens seat and transparent aperture that remain clean enough for live diagram
  content;
- a coherent contact shadow that seats the complete instrument on the desk.

The render uses the previously approved broad-source lighting direction: one
large soft key, restrained ambient/fill, no burned-out top edge, no black timeline
or handle, and no flat material-preview lighting.

## Candidate A — Literal gasket derivative

This is the baseline and the most likely production direction.

- A three-stage circular rim directly translates the gasket's stepped face:
  bronze outer land, narrow dark gunmetal channel, and bronze inner retaining lip.
- Step depths, bevel rhythm, and recess darkness visibly match the main gasket.
- The socket grows from the lower-right rim as a compact continuation of the
  gasket structure, with two restrained fasteners and no ornamental bridge.
- The handle uses a dark gunmetal structural core with bronze side cheeks or
  collars, narrowing toward the small terminal grip.
- Wear concentrates on the outer bronze land, socket shoulders, and grip contact
  points.

This candidate should look as though the same workshop made both the fixed gasket
and the portable instrument.

## Candidate B — Refined hand instrument

This candidate asks how much the gasket language can be made lighter and more
comfortable without becoming a generic modern magnifier.

- The rim uses two smoother gasket-derived steps with a slimmer bronze face and a
  continuous gunmetal lens bed.
- The socket transitions through a compact tapered neck rather than a blocky lug.
- A dark shaped grip surrounds a visible bronze or gunmetal spine; the grip has a
  subtle palm swell and restrained longitudinal texture.
- Mechanical seams are fewer and cleaner than Candidate A, but all remain
  credible and gasket-related.

This candidate must read as a professional hand instrument, not a polished luxury
object or minimalist consumer product.

## Candidate C — Heavy field instrument

This candidate explores a more robust archaeological working tool while retaining
the narrow usable rim.

- The circular rim keeps the shared outer envelope but gains a deeper rear
  gunmetal cradle visible at the edge and lower-right socket.
- The socket is reinforced with a short ribbed yoke integrated into the rim rather
  than attached to a separate plate.
- The handle is a stronger faceted gunmetal body with bronze wear rails and a
  compact capped terminal grip.
- Fasteners and seams are more visible than in A or B but remain sparse, aligned,
  and functional.

The result may feel heavier but may not obscure more of the live aperture or look
military, industrial-cartoon, or improvised.

## Candidate D — Precision variant

This candidate explores finer mechanical articulation within the gasket family.

- A narrow bronze retaining ring surrounds an inset gunmetal channel and a fine
  inner bronze collet.
- A small number of engraved index ticks or inset pips appears only on the fixed
  metal face; they are texture/detail, not controls or labels.
- The socket uses a precise collared transition with a visible but restrained
  joint line.
- The handle has fine longitudinal fluting or a machined dark grip with bronze
  end collars and the same small terminal sizing grip.

Detail must remain legible at game scale and must not turn into jewelry,
clockwork ornament, or a radial button interface.

## Render outputs

Each candidate produces two primary views:

1. **Isolated asset view:** high-resolution transparent-background render showing
   the complete loupe, aperture transparency, rim construction, handle, grip, and
   contact-shadow relationship without other interface clutter.
2. **Game-scale context view:** 1600×1000 composition over the approved Natural-
   indigo hardwood desk and approved central gasket, with the loupe placed and
   scaled as the editor would appear during use.

A 2×2 comparison sheet uses identical crops and labels outside the rendered
objects. An HTTP review page exposes the full-resolution isolated and context
views without adding simulated editor controls or alternate interaction.

## Critical production pass

The four candidates are not generated once and accepted mechanically. Before
presentation, each is inspected at full resolution and actual game scale for:

- broken silhouette or aperture proportions;
- primitive-looking rim/socket/handle joins;
- inconsistent bevel scale or shading;
- insufficient exposure or lost dark-material detail;
- texture scale, repetition, or procedural-noise artifacts;
- detached or implausible shadows;
- handle/grip mismatch with the approved mock;
- failure to resemble the approved gasket when seen in context.

Problems are corrected in the candidate's authoritative geometry, material, or
lighting. The comparison is not padded with knowingly defective options.

## Repository and selection boundary

The study keeps one editable Blender source and review renders. It does not:

- promote any candidate to runtime assets;
- render alternate handle orientations;
- implement the circular editor or resize behavior;
- change the game mount, CSS, proof engine, or popup menu;
- produce final optical overlays or animation layers;
- regenerate or modify the approved desk, gasket, timeline, folio, or substrate
  assets.

After review, only the selected candidate or an explicitly requested hybrid moves
to production-layer rendering. Rejected candidates remain labeled review evidence
and are not silently retained as alternate runtime authorities.

## Validation

The study is successful when:

1. all four candidates preserve the shared approved envelope and comparison
   controls;
2. each reads as a coherent, finished, clearly lit mechanical object;
3. each visibly belongs beside the approved gasket;
4. construction differences remain legible at actual game scale;
5. isolated renders preserve a transparent circular aperture;
6. context renders use the approved desk and gasket without modifying them;
7. the HTTP comparison loads every view at full resolution;
8. the user can select a candidate or specify a concrete hybrid from the evidence.
