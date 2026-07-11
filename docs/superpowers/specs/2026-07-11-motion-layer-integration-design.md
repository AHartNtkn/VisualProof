# Motion Layer Integration Design

**Status:** Approved for written review  
**Date:** 2026-07-11

## Outcome

The production application uses the approved Round 7 motion language. βη conversion visibly follows its certificate as a continuous shape morph before semantic commit; structural changes leave short-lived location cues; hover emphasis eases; and users control every layer from Compass utilities. Motion remains entirely visual and cannot race diagram, proof, history, or physics state.

## Motion preferences

Compass utilities own one session-wide mutable preferences object:

```ts
type MotionPreferences = {
  conversionAnimation: boolean
  connectedMorph: boolean
  speed: number
  transitionGhosts: boolean
  hoverEaseMs: 0 | 120
}
```

The controls and defaults are:

- **βη animation:** on;
- **connected morph:** on; off selects the approved pinned-v1 geometry interpolator;
- **speed:** 1×, clamped to 0.25×–3× in 0.25 increments;
- **transition ghosts:** on;
- **hover ease:** on, using 120ms.

When `prefers-reduced-motion: reduce` matches at application mount, βη animation, transition ghosts, and hover ease initialize off. Connected-morph choice and speed remain available. An explicit user change applies for the rest of the application session and is not overwritten by later media-query changes.

Preferences are view state. They are not saved into theories, diagrams, sessions, the Library, or proof history.

## Authoritative ownership

Each interactive production viewport owns one `MotionCoordinator`. The main shell viewport owns one coordinator; every `ProofFrontViewport` owns one coordinator using the same preferences object. `FixedSideWorkspace` aggregates active playback from its two coordinators to guard its shared `ProofSession`.

The coordinator owns only:

- at most one active conversion transition;
- removed-body ghost and added-body pulse overlays;
- hover target and easing time;
- transition timing and exact completion/cancellation;
- whether the viewport currently guards semantic input.

It never owns a diagram, proof session, timeline, theorem, engine loop, camera, selection, pins, or persistence state. It never calls `requestAnimationFrame`; existing production frame owners call `frame(now)` and consume its transient render state.

## Pending semantic operation

Conversion uses a deferred operation contract:

```ts
type PendingMotionCommit = {
  readonly before: Diagram
  readonly step: ProofStep
  readonly commit: () => void
}
```

The caller validates and constructs the step before offering it. The coordinator either starts playback and retains the closure, or immediately invokes it when animation is disabled, reduced, hidden, identical, unsupported, or has no meaningful certificate frames.

The closure is invoked at most once. Until it runs, the before diagram and its proof/edit history position remain authoritative. Hit testing, selection, pins, theorem state, Library state, and serialization continue to see the before state.

A failure while deriving playback occurs before transition activation. The coordinator invokes no commit and the caller reports the existing pointer-local refusal. A failure inside the eventual commit clears playback and propagates through the same refusal path; it does not show a success-shaped fallback.

## Conversion frame derivation

For a conversion step on a term node:

1. Begin with the node's source term.
2. Replay `certificate.leftSteps`, appending every intermediate through the common reduct.
3. Begin separately with the step's target term.
4. Replay `certificate.rightSteps`, reverse that sequence, and append it after the common reduct without duplicating the shared term.
5. Convert every term frame to `TrompGrid`.
6. Build adjacent segment interpolators with `mkGridMorph` when `connectedMorph` is on, or `mkGeomMorph(bendGrid(...), bendGrid(...))` when it is off.

Every segment lasts `520ms / speed`. Time within a segment uses the approved C1 smoothstep:

```ts
p * p * (3 - 2 * p)
```

At each sample, the affected term body's geometry, output anchor, named-port anchors, and anatomy radius are derived from that single interpolated geometry. Connected wires therefore remain attached to the drawn rail tips throughout the connected morph. No source/target crossfade or midpoint snap is permitted.

The coordinator mutates only the viewport's temporary render engine body for the sampled frame. The semantic diagram and proof engine authority remain unchanged. At the final endpoint, the coordinator invokes the commit closure once; the ordinary existing reconciliation/carry-over route creates the after engine; then the coordinator clears conversion state.

## Structural ghosts and born pulses

Non-conversion diagram commits remain immediate. Before reconciliation, the viewport records the last visual position and radius of bodies absent from the after diagram. After reconciliation, it records ids newly present in the after engine.

When transition ghosts are enabled:

- removed bodies render as neutral theme-compatible circles at their last positions, expanding slightly and fading to zero over 320ms;
- added bodies render a theme-compatible accent ring around their live after-engine body, expanding and fading over 450ms.

These are paint overlays only. They are never inserted into `Diagram`, `Engine.bodies`, physics constraints, hit testing, selection, pins, serialization, theorem checking, or history. Missing born bodies simply end their pulse. A second commit may coexist with unexpired overlays; expired entries are pruned during ordinary frame sampling.

Conversion completion may produce ordinary structural ghosts/pulses only for actual node-id additions or removals outside the morphed persistent node. The converting node itself is neither ghosted nor pulsed when its identity survives.

## Hover easing

The coordinator tracks the current hover identity and the time it became current. Production paint receives an emphasis fraction:

```ts
hoverEaseMs === 0 ? 1 : clamp((now - hoverSince) / hoverEaseMs, 0, 1)
```

The fraction controls highlight opacity/intensity only. Hover does not mutate engine or semantic state and never activates the playback input guard. Changing target restarts easing for the new identity; leaving clears it immediately.

The same hover channel is used by the main viewport and both fixed-side fronts. Binder-group highlighting and ordinary node/region/wire highlighting consume the same eased fraction.

## Input guard and cancellation

While a conversion is active, the affected viewport rejects:

- pointer and context-menu gestures;
- wheel zoom;
- selection and pin gestures;
- proof or construction commands;
- Delete, normalization, and citation actions;
- Undo, Redo, and temporal-rail movement;
- non-lifecycle keyboard commands.

The guard acts before a gesture can create transient controller state. It does not display repeated refusal messages; the visibly playing transition is sufficient feedback.

In fixed-side proving, either front playing sets a workspace-wide semantic guard. Both panes continue passive settle/paint, but neither can begin proof or history mutation until playback completes. Focus and divider resizing may remain available only when they do not create a semantic or viewport gesture conflict; beginning a seam drag cancels no active conversion.

Mode exit or viewport/workspace disposal cancels playback without invoking its uncommitted closure. This is exact because the before state remains authoritative. It clears transition render state, ghosts, pulses, and hover state and removes every owned listener. Escape does not cancel conversion independently; lifecycle exit is the explicit cancellation boundary.

## Production integration

The intended boundaries are:

- `src/app/interact/motion.ts`: preferences, certificate-frame derivation, timing, coordinator state, conversion sampling, ghost/pulse sampling, hover easing, and disposal;
- `src/app/proof-front.ts`: owns one coordinator, routes proof commits through it, guards `InteractiveViewport`/`ProofMoveController`, and appends motion overlays during its existing `frame()`;
- `src/app/fixed-side-workspace.ts`: aggregates `playing` across fronts and guards both proof/history mutation paths;
- `src/app/shell.ts`: owns the main coordinator, routes Edit and ordinary-track proof conversions through it, samples it in the existing frame, guards main input/history, and cancels on lifecycle changes;
- `src/app/compass.ts` and `app/style.css`: render the five utility controls with Porcelain/Basalt and dark-theme parity.

`InteractiveViewport` receives an input-admission callback or equivalent narrow guard checked before pointer, wheel, double-click, context-menu, and key dispatch. It does not acquire motion semantics.

Proof/edit operation producers continue emitting ordinary diagrams or `ProofStep`s. They do not know how conversion is animated and do not own timers. Replay remains immediate: cursor movement keeps using cached authoritative diagrams and engine carry-over, with no deferred commit or conversion interception.

## Frame ownership

The shell remains the only application request-animation-frame owner. On each frame:

1. sample the applicable coordinator with the current timestamp;
2. allow the existing viewport physics/fit step when safe;
3. paint the ordinary engine, with sampled conversion geometry when active;
4. append ghosts, pulses, and eased hover overlays;
5. paint once.

`ProofFrontViewport.frame(now)` receives the shared timestamp from `FixedSideWorkspace.frame(now)`. Neither front nor coordinator schedules another frame. Motion completion may trigger semantic reconciliation during that frame; painting then uses the newly authoritative engine without an intermediate stale frame.

## Feedback and accessibility

Motion success produces no toast or message. The visible transition and resulting diagram are the result.

The controls use explicit labels and expose current values. The speed slider reports its multiplier. Reduced-motion initialization is honored before the first transition. Disabling a layer takes effect for future transitions; changing preferences during active conversion is guarded until it finishes.

Theme colors for ghosts, pulses, and eased highlights derive from the production `Theme` contract rather than hard-coded lab green/gray values.

## Validation

Focused automated evidence must prove:

1. Normal and reduced-motion preference initialization, five independent controls, and speed clamping.
2. Exact certificate frame order `source → common reduct → target`.
3. Connected and pinned-v1 interpolator selection, smoothstep timing, speed scaling, and endpoint convergence.
4. Mid-play semantic diagram/timeline remains at before; final commit happens exactly once.
5. Immediate/off/hidden/identical/no-frame paths commit once without transition.
6. Conversion sample anchors coincide with interpolated output and named-port rail tips.
7. Removed ghosts and born pulses have exact lifetimes, theme-derived paint, expiry, and no semantic/hit-test presence.
8. Hover target changes ease over 120ms when enabled and apply immediately when disabled.
9. Pointer, wheel, keyboard, proof/edit, Undo/Redo, and scrubber input are guarded before controller state while playing.
10. Either fixed-side front playing guards both shared-session mutation paths while both panes continue rendering.
11. Completion hands off to the ordinary reconciled after engine; disposal/mode exit cancels without commit and removes transient state.
12. Replay cursor movement remains immediate and acquires no deferred motion authority.
13. Production imports no lab motion code, creates no coordinator/front animation loop, emits no success toast, and stores no ghost/pulse in diagram, engine, session, or history state.

Only focused semantic/unit tests, type checking, and relevant production browser tests are required. Existing pure morph tests may run because morph code is consumed but not changed. Physics sources and physics-heavy tests are excluded.
