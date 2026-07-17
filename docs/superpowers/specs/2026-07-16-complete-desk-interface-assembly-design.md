---
name: approved-desk-static-render
created: 2026-07-16
status: approved-scope
---

# Cursebreaker Approved Desk Static Render

## Outcome

Produce one static browser render that shows how the approved Cursebreaker interface assets compose together. HTML and CSS are only the means of arranging the images for review. This is not an application implementation or an interactive prototype.

## Included

- The approved Natural-indigo hardwood desk treatment filling the viewport.
- The approved candidate-04 central gasket/frame as a transparent image.
- The approved candidate-04 timeline housing and its small independent handle, exported as transparent images.
- One substrate from the approved indigo material direction, using the selected E dark, subdued, low-contrast treatment and filling the lens aperture.
- A centered square lens assembly sized nearly to the viewport height.
- Bare desk space to the left and right.

## Excluded

- Teacher presentation or assets.
- Artifact papers, culture papers, folios, vellum, libraries, labels, legends, menus, or other unapproved interface assets.
- Puzzle diagrams or proof-canvas content.
- Artifact selection, progression, browsing, timeline input, proof input, animation, or any other interaction.
- JavaScript application logic, game state, event listeners, controls, focus behavior, accessibility behavior for controls, or duplicate implementations of existing application behavior.
- Changes to the real game mount, proof engine, timeline implementation, or interaction code.

Unapproved areas remain empty. They are not filled with provisional substitutes.

## Composition

The static page has one full-viewport desk layer and one centered square lens assembly. The lens assembly uses a shared square coordinate system:

1. An indigo substrate covers the full authored aperture area with enough excess to prevent exposed edges.
2. The transparent gasket/frame image overlays the substrate and supplies the only visible aperture boundary.
3. The transparent timeline housing overlays the lower chassis at the position authored in the approved candidate-04 model.
4. The transparent small handle overlays the housing at a representative fixed position.

The substrate has no independent border, rounded rectangle, shadow, or inset silhouette. The gasket masks it visually. The timeline is visually integrated with the chassis; the separate PNGs are compositing layers from the same approved model, not separately designed geometry.

## Asset authority

- Mechanical source: `/tmp/central-loupe-texture-comparison-20260715/candidate-04/scene.blend`
- Approved mechanical treatment: “Gunmetal and archaeological bronze.”
- Desk source: Poly Haven `dark_wood`, transformed according to the approved “Natural-indigo hardwood” material specification.
- Substrate source: an existing indigo-remapped texture from the approved substrate study. Rejected full-scene Blender renders are not used.

Only assets needed for this render are collected. This specification does not choose a final production asset library, retention policy, manifest schema, or runtime API.

## Validation

- The HTML contains no script and no interactive element.
- It references only the collected desk, substrate, gasket/frame, timeline housing, and timeline handle images.
- Browser capture confirms the lens is square and nearly viewport-height, with bare desk visible on both sides.
- The substrate fills the aperture without appearing as a floating inset square.
- The timeline housing spans nearly the full lower chassis and the handle is a small nub.
- Transparent mechanical image regions reveal the desk or substrate beneath them.
- No game runtime source file is changed.
