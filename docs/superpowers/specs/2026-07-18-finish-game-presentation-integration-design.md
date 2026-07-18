# Complete Game Presentation Integration Design

## Outcome

Cursebreaker always renders a complete game composition for every controller state. Archive startup shows the approved physical workspace and usable folio; puzzle mode adds proof and logical timeline input; completion replaces puzzle interaction with a dedicated success surface; pause/settings and teacher states layer above the preserved primary view. A persisted completion restores to the same success surface rather than a blank lens.

## Ownership

`CursebreakerRuntime` remains the sole owner of controller state, proof, folio, timeline interaction, persistence, and effects. A required `GamePresentationView` becomes the sole owner of non-proof state presentation. It consumes a projection containing the current mode, completion receipt and resolved catalog copy, settings, and transient data. It emits typed `GameAction` callbacks to the runtime; it never mutates state or simulates progression.

The approved desk, full-height lens, substrate, gasket, timeline artwork, and folio remain persistent physical workspace layers. The presentation view mounts once into a dedicated overlay host owned by `LensEnvironment`. State changes update that one view. There is no optional presentation port and no no-op production fallback.

## State compositions

### Archive

The continuous folio remains the level selector. The empty lens substrate is intentional, but the physical timeline housing and handle remain visible. No logical timeline slider is mounted because no timeline exists. The archive is not considered valid unless at least one unlocked record is visible and operable.

### Puzzle

The proof canvas, theorem-capable folio, and timeline slider remain as implemented. Opening teacher instructions, recognized unwinnable commentary, pause, and settings are presentation overlays; they do not replace or remount the underlying proof.

### Completion

Completion keeps the physical desk/lens substrate and renders a dedicated success surface. It contains:

- one small non-diegetic top line in a distinct color;
- the completed artifact’s professional identity;
- the receipt move count, already calculated as `timeline.states.length - 1` by the controller;
- one concise authored completion-teacher response when available, otherwise the artifact’s authored provenance response;
- exactly one button, “Return to level selection,” dispatching `levelSelection`.

It contains no rank, score, par, proof recording, review, replay, continue, or restart control. The folio and proof are inactive during completion, but the surrounding physical workspace does not disappear.

### Pause and settings

Pause is modal over the preserved primary state. Its menu has Resume, Level selection, Settings, and Exit game. Settings exposes reduced motion, fullscreen, and interface text size through existing actions, plus a Back action that uses Escape precedence to return to the pause menu. There is no restart action.

### Teacher

Opening instructions are modal and acknowledge through the existing controller action. Recognized unwinnable commentary is nonblocking, remains visually attached to the workspace edge, states the authored recovery direction, and closes without blocking proof/timeline input. Completion commentary is resolved into the dedicated completion response rather than opening a second competing overlay.

## Visual review candidates

The three unapproved surfaces each receive three high-fidelity CSS compositions built from existing approved desk, indigo, vellum, gasket, and neon materials. They contain identical semantics and actions; only composition changes.

- Teacher: **Field annotation** (narrow lens-edge note), **Conservation slip** (mounted folio insert), **Optical marginalia** (dark translucent lens annotation).
- Pause/settings: **Instrument rest** (centered indigo instrument panel), **Registrar folio** (stacked physical cards), **Shutter interval** (dark lens aperture composition).
- Completion: **Clearance docket** (catalog slip and artifact identity), **Developed plate** (dark lens plate with luminous result), **Released mount** (completed record lifted into a central conservation mount).

Candidate selection is debug/review configuration only and never appears as a player-facing picker. Actual controller state drives every candidate. Headless captures provide the visual gate. After user selection, unselected candidate CSS and debug selection code are deleted.

## Lifecycle and input

The presentation view mounts once, updates in place, and disposes all listeners and DOM once. Modal pause and teacher surfaces own input. Escape closes the topmost transient, settings returns to pause, and otherwise opens pause. Completion accepts only its return action. The timeline’s physical artwork is persistent; logical slider input exists only with an active puzzle session.

## Validation authority

Delete assertions that declare blank completion or absent presentation successful. Real-browser tests must drive the actual controller and assert visible semantic content, action counts, preserved underlying geometry, and restored saved modes. Tests must cover archive startup, puzzle selection, first completion, completion return, persisted completion restoration, pause menu, settings changes, modal and nonblocking teacher behavior, Escape precedence, and disposal. Candidate capture tests verify all variants use the same real projection and actions. The unchanged proof physics battery remains excluded.

