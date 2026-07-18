# Complete Game Presentation Integration Design

## Outcome

Cursebreaker always renders a complete game composition for every controller state. Archive startup shows the approved physical workspace and usable folio; puzzle mode adds proof and logical timeline input; completion replaces puzzle interaction with a dedicated success surface; pause/settings layer above the preserved primary view while passive guidance remains at its edge. A persisted completion restores to the same success surface rather than a blank lens.

## Ownership

`CursebreakerRuntime` remains the sole owner of controller state, proof, folio, timeline interaction, persistence, and effects. A required `GamePresentationView` becomes the sole owner of non-proof state presentation. It consumes a projection containing the current mode, completion receipt and resolved catalog copy, settings, and transient data. It emits typed `GameAction` callbacks to the runtime; it never mutates state or simulates progression.

The approved desk, full-height lens, substrate, gasket, timeline artwork, and folio remain persistent physical workspace layers. The presentation view mounts once into a dedicated overlay host owned by `LensEnvironment`. State changes update that one view. There is no optional presentation port and no no-op production fallback.

## State compositions

### Archive

The continuous folio remains the level selector. The empty lens substrate is intentional. The complete timeline slider remains mounted and visible at its home detent, with disabled semantics and no pointer or keyboard effect. The archive is not considered valid unless at least one unlocked record is visible and operable.

### Puzzle

The proof canvas, theorem-capable folio, and timeline slider remain as implemented. Passive opening and recognized-unwinnable guidance updates in place at the workspace edge. Pause and settings overlay the composition without replacing or remounting the underlying proof.

### Completion

Completion keeps the physical desk/lens substrate and renders a dedicated success surface. It contains:

- one small non-diegetic top line in a distinct color;
- the completed artifact’s professional identity;
- the receipt move count, already calculated as `timeline.states.length - 1` by the controller;
- one concise authored completion-teacher response when available, otherwise the artifact’s authored provenance response;
- exactly one button, “Return to level selection,” dispatching `levelSelection`.

It contains no rank, score, par, proof recording, review, replay, continue, or restart control. The folio and proof are inactive during completion, but the surrounding physical workspace does not disappear. The persistent timeline slider freezes at the completed final detent and remains noninteractive.

### Timeline instrument

The housing, track, handle, detents, and slider control are one permanent
instrument. They mount once with the lens and retain DOM identity across archive,
puzzle, completion, pause, settings, editor, and guidance transitions. Puzzle mode
binds the instrument to the active session timeline. Archive mode displays the
home detent and completion displays the final detent implied by the completion
receipt; both are semantically disabled and dispatch no timeline action. No mode
uses a decorative substitute or hides, disposes, or remounts the slider.

### Pause and settings

Pause is modal over the preserved primary state. Its menu has Resume, Level selection, Settings, and Exit game. Settings exposes reduced motion, fullscreen, and interface text size through existing actions, plus a Back action that uses Escape precedence to return to the pause menu. There is no restart action.

### Guidance

All in-puzzle guidance follows the approved passive-edge-note contract in
`2026-07-18-passive-guidance-design.md`. Opening and specifically recognized
unwinnable interventions never become input-owning transients, never capture
focus, never block proof/timeline/folio input, and expose no acknowledgement or
close action. Multi-page notes may expose one optional Next action; it changes
only the visible paragraph and is never required for progression. Completion
commentary is resolved into the dedicated completion response rather than opening
a second competing surface.

## Visual review candidates

The two remaining unapproved modal/success surfaces each receive three high-fidelity CSS compositions built from existing approved desk, indigo, vellum, gasket, and neon materials. They contain identical semantics and actions; only composition changes.

- Pause/settings: **Instrument rest** (centered indigo instrument panel), **Registrar folio** (stacked physical cards), **Shutter interval** (dark lens aperture composition).
- Completion: **Clearance docket** (catalog slip and artifact identity), **Developed plate** (dark lens plate with luminous result), **Released mount** (completed record lifted into a central conservation mount).

Teacher modal candidates are rejected. A later guidance gate may compare only
passive edge-note treatments using the same nonblocking behavior.

Candidate selection is debug/review configuration only and never appears as a player-facing picker. Actual controller state drives every candidate. Headless captures provide the visual gate. After user selection, unselected candidate CSS and debug selection code are deleted.

## Lifecycle and input

The presentation view mounts once, updates in place, and disposes all listeners
and DOM once. Pause and editor transients own input when present; guidance never
does. Escape closes the topmost input-owning transient, settings returns to pause,
and otherwise opens pause. Completion accepts only its return action. The complete
timeline slider is persistent; its state-changing input authority exists only with
an active puzzle session and no higher-priority input owner.

## Validation authority

Delete assertions that declare blank completion or absent presentation successful.
Real-browser tests must drive the actual controller and assert visible semantic
content, action counts, preserved underlying geometry, input availability, and
restored saved modes. Tests must cover archive startup, puzzle selection, first
completion, completion return, persisted completion restoration, pause menu,
settings changes, passive guidance delivery and clearing, persistent timeline DOM
identity and inactive behavior, Escape precedence, and disposal. Candidate capture
tests verify all retained variants use the same real projection and actions. The
unchanged proof physics battery remains excluded.
