# Independent Editor Loupe Design

**Date:** 2026-07-17  
**Status:** Design approved in conversation; pending written-spec review  
**Scope:** Circular editor geometry in the main assistant, followed by a faithful game presentation of the approved clean-loupe mock

## Outcome

The temporary construction editor used by anonymous comprehension and similar
focused diagram-building moves appears in the game as a large independent hand
loupe resting over the desk. Its live construction diagram fills a circular
optical aperture. The instrument can be moved and resized, the host proof remains
visible around it, and existing host-to-draft gestures continue to work.

This work does not invent another editor or another proof interaction. The main
proof assistant first receives the circular boundary and proportional sizing
behavior. The game then consumes that behavior and replaces only the generic
window presentation with the loupe. The presentation is not
comprehension-specific: later temporary construction editors reuse the same
shell while retaining their own semantic transactions.

## Visual Authority

The controlling mock is:

`.superpowers/brainstorm/131325-1783786690/content/diegetic-loupe-clean.html`

Its approved characteristics are authoritative:

- a large circular optical aperture;
- a narrow warm-metal rim;
- one integrated handle extending diagonally down and right when space permits;
- a strong but controlled contact shadow over the desk and underlying objects;
- substantial overlap with the main lens while leaving useful host content
  visible;
- the live construction diagram occupying nearly the entire aperture;
- no persistent title bar, toolbar, action buttons, label, legend, idle
  connector, or other application chrome.

The mock is a layout and silhouette authority, not a finished material render.
Final metal, handle, glass, wear, and lighting detail must be demonstrated at
game scale. Material studies may refine the surface treatment but may not alter
the approved form.

## Responsibility Model

### Main proof assistant

The main assistant owns the interaction and geometry shared by every surface:

- one circular construction boundary;
- one diameter as the complete size authority;
- proportional resizing from a reachable sizing locus;
- placement and viewport clamping;
- exact canvas-to-pointer mapping;
- move, focus, construction, cross-surface connection, local history,
  commit/cancel, and teardown behavior.

The high-aspect-ratio editor state is removed rather than retained behind a
compatibility path. The existing independent width and height representation is
replaced everywhere that consumes editor geometry.

### Game presentation

The game owns only the physical presentation:

- layered loupe imagery;
- optical edge treatment;
- desk shadow and overlap;
- handle orientation imagery;
- set-down and lift-away presentation;
- diegetic hit regions that delegate to the shared move and resize operations.

The game does not create a second editor state, command map, sizing model, or
gesture implementation. The loupe shell receives live canvas content and
lifecycle callbacks from the owning editor; it contains no comprehension rule
or draft semantics.

## Circular Boundary and Sizing

The editor's DOM and canvas allocation is a square whose side is the current
diameter. The proof frame within it is circular. Diagram fit, boundary slots,
camera fit, rim scale, and optical overlay all derive from that diameter.

The preferred and minimum diameters inherit the useful scale of the existing
editor rather than its rectangular aspect ratio. The preferred instrument must
offer at least the current editor's vertical construction span. The minimum must
keep the full boundary and ordinary pointer targets usable. Exact constants are
selected from realistic browser evidence in the implementation plan; there is
no independent width or height constant.

Resizing changes the diameter proportionally. No stretch, ellipse, rectangular
letterbox, or one-axis dead zone is permitted. Content outside the circle is not
editor space: it belongs to the rim, handle, transparent overflow, or underlying
desk.

## Placement and Reachability

The circle opens on the available side of the invocation using the existing
adjacent-placement intent. The complete interactive instrument—not merely its
aperture—is considered when clamping.

The approved handle orientation is down-right. It is the first placement
candidate whenever its terminal sizing grip remains reachable. Near viewport
edges, the system may mirror or rotate the instrument, or shift the whole loupe,
to keep that grip within the supported viewport inset. The method is subordinate
to these invariants:

1. the sizing grip is always reachable;
2. the circular aperture remains fully usable;
3. the invocation and useful host proof remain visible when the viewport allows;
4. orientation changes are deterministic and do not occur while the player is
   already dragging or resizing the instrument.

Clear rim and handle areas delegate to the existing move operation. The terminal
grip delegates to proportional resize. Neither surface adds a command.

## Layered Asset Composition

The live diagram is never rendered into a static image. The composed loupe uses
separate authorities:

1. a rear contact-shadow layer;
2. the live editor canvas clipped to the circular aperture;
3. a coherent rim-and-handle layer with a transparent circular aperture;
4. a front optical-edge/reflection layer with `pointer-events: none`;
5. transient interaction paint above the optics.

The rim and handle must read as one designed object even if render layers are
separated for composition. Visible seams must correspond to credible mechanical
joints, not to the boundaries of PNGs or DOM elements.

Orientation variants are produced from one approved construction. They may be
separate renders so screen-space lighting remains coherent; casually mirroring a
lit raster is not sufficient when it reverses the apparent light direction.

Assets must have enough source resolution for the preferred diameter on a
high-density display. The final raster size is chosen from measured use rather
than by regenerating or comparing exact bytes.

## Optics and Pointer Accuracy

The central editor field remains geometrically flat. Edge shading may imply
thickness, refraction, slight chromatic separation, or magnification only within
the nonessential outer optical band. It must not visibly displace actionable
nodes, wires, boundary positions, selection paint, or the pointer target under
the cursor.

The optical overlay never owns input. Pointer coordinates continue to resolve
against the unwarped live canvas. If a proposed shader cannot preserve that
correspondence, the shader is rejected rather than compensated by a second hit
testing transform.

## Existing Interaction Presentation

The instrument contains no persistent editor controls. Existing keyboard and
contextual construction behavior remains authoritative. A transient spawn
palette or refusal may appear when the existing interaction invokes it; that is
not embedded loupe chrome.

Host-to-draft connection feedback appears only during the existing hover or
active gesture. No idle thread or line links the loupe to the host proof. Active
gesture paint and pointer-adjacent red thought bubbles render above the front
optical layer and remain unclipped by the circular aperture.

The absence of visible game buttons must not create a game-only command. Any
keyboard or resize behavior required by the game exists in the main assistant
first.

## Opening and Closing

Opening reads as the independent instrument being set onto the desk. Closing
reads as it being lifted away. Motion may combine a short vertical offset,
contact-shadow convergence, and restrained optical settling.

The editor reaches its authoritative final geometry immediately. Presentation
does not delay focus or input, introduce an intermediate editor state, or alter
commit/cancel timing. Reduced-motion presentation substitutes a short opacity
and shadow change without spatial travel.

## Integration Order

1. In the main proof assistant, replace rectangular editor geometry with the
   circular boundary, one diameter, proportional resize, reachable sizing locus,
   placement/clamping, and migrated tests.
2. Validate every existing editor interaction in ordinary, backward, and
   fixed-side proving.
3. Merge that main-assistant work into the game branch.
4. Build and approve high-fidelity layered assets faithful to the clean-loupe
   mock.
5. Compose those assets around the shared live editor canvas in the game.
6. Validate the completed visual and behavioral integration at realistic
   viewport sizes.

The game branch does not prototype unique resizing or boundary behavior ahead of
the main assistant.

## Prohibited Competing Paths

- No generic rectangular editor window underneath or alongside the loupe.
- No independent width and height or high-aspect-ratio editor state.
- No elliptical stretching of the approved instrument.
- No baked diagram content.
- No persistent title bar, toolbar, buttons, labels, legend, or connector.
- No geometric optical distortion of actionable content.
- No game-only command, resize algorithm, or pointer transform.
- No duplicate editor lifecycle or construction controller.
- No alternative loupe silhouette exploration.

## Validation

Main-assistant validation proves:

1. the boundary is circular and the canvas allocation is square;
2. exactly one diameter owns size;
3. every resize is proportional and clamped;
4. the sizing locus is reachable at every supported viewport edge;
5. pointer targeting remains exact at the center and usable boundary band;
6. ordinary, backward, and fixed-side editors retain their existing construction,
   history, connection, commit/cancel, focus, and teardown behavior;
7. no high-aspect-ratio or rectangular compatibility model remains.

Game visual validation uses an HTTP-served composition at preferred and minimum
diameters and at representative viewport edges. It proves:

1. fidelity to the clean-loupe silhouette and hierarchy;
2. coherent rim/handle construction and material detail;
3. reachable handle/grip orientation;
4. legible host proof beneath and around the instrument;
5. exact live canvas alignment with the circular aperture;
6. absence of persistent application chrome and idle connectors;
7. correct z-order for transient palettes, gestures, and red thought bubbles;
8. set-down/lift and reduced-motion presentation without input delay.

Physics sources and the dedicated physics battery are excluded unless editor
physics itself is changed.
