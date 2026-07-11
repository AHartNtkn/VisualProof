# Fixed-Side Two-Front Workspace Design

**Status:** Approved for written review  
**Date:** 2026-07-10

## Outcome

Fixed-side proving presents the approved adjustable side-by-side workspace in the production application. Both proof fronts are continuously visible, equally interactive, and backed by one authoritative `ProofSession`. Neither front is a companion, preview, or hidden alternate state.

## Authoritative ownership

The fixed-side system has three owners:

- `ProofSession` remains the sole semantic authority for forward and backward timelines, cursor states, step application, meet, assembly, and theorem checking.
- `FixedSideWorkspace` owns workspace composition only: the two front viewports, focused side, divider ratio, seam status, global routing, and disposal.
- Each `ProofFrontViewport` owns one pane's visual and interaction state: canvas adapter, render engine, camera and user zoom, selection, pins, hover, active gesture, pointer-local palette/refusal anchor, and animation lifecycle.

No diagram, timeline, cursor, or proof step is copied into the workspace or viewport as mutable semantic state. A viewport reads the current authoritative diagram and boundary for its side and emits ordinary `ProofStep` values to the workspace. The workspace applies them through `applyForward` or `applyBackward` and then refreshes only the affected viewport.

## Shared production viewport

`ProofFrontViewport` is extracted from the real production shell rather than copied from the lab prototype. It uses the same production components as ordinary proving:

- `InteractiveViewport` for pointer, keyboard, selection, pin, and zoom behavior;
- `ProofMoveController` for explicit-right-click proof discovery, contextual Delete, wrapping, normalization, iteration, citation, folding, and instantiation;
- the production engine, camera, paint, hit testing, feedback, and carry-over paths;
- the production theme and pointer-local refusal contract.

The component accepts a narrow side-facing interface:

```ts
type ProofFrontModel = {
  readonly side: 'forward' | 'backward'
  diagram(): Diagram
  boundary(): readonly WireId[]
  context(): ProofContext
  apply(step: ProofStep): void
  focused(): boolean
  focus(): void
  refuse(text: string, pointer: Vec2): void
}
```

The viewport never owns a `ProofSession`, timeline, or theorem context copy. It can be understood and tested as one interactive projection over a changing diagram source.

Ordinary one-origin proving may continue using the existing single-canvas path during this slice. The extraction must select shared production responsibilities cleanly enough that the fixed-side viewports do not fork interaction behavior; it does not require rewriting unrelated Edit or Replay composition.

## Workspace layout

The workspace replaces the single main canvas only while a fixed-side proof is active.

- Forward occupies the left pane and backward occupies the right pane.
- A vertical seam separates them.
- The divider ratio is initialized to 50%, clamps continuously to 30–70%, and returns to 50% on seam double-click.
- Resizing changes canvas CSS bounds and backing resolution without resetting either engine, camera state, selection, or pins.
- Focus is shown through border/header treatment only. Focusing a pane never changes the divider ratio or pane geometry.
- Each pane has a compact orientation label and cursor position. It does not acquire its own duplicate toolbar or history strip.

Compass lifecycle, Indexed Ledger, utilities, contextual palettes, refusals, and the south temporal rail remain overlays above the workspace. Opening any overlay leaves both pane rectangles, cameras, and diagram state unchanged.

## Input routing

Pointer entry establishes focus before routing the initiating gesture. A click, drag, wheel, right-click, or double-click within a pane is handled entirely by that pane's viewport.

Keyboard input resolves the focused pane at the time of the key event:

- proof commands use the focused pane's orientation and selection;
- `Ctrl+Z` and `Ctrl+Shift+Z` move that side's authoritative cursor;
- Home resets only that pane's user zoom;
- Escape cancels only the focused pane's active palette or gesture unless a global Compass overlay owns Escape.

The global temporal rail presents the focused side's timeline and names that side in its copy. Rail dragging changes only the focused side cursor. Changing focus immediately rebinds the rail to the other timeline without moving either cursor.

The seam claims pointer gestures before either pane. Beginning a divider drag cancels active gestures in both viewports, closes previews and palettes, and then changes only the ratio. Seam interaction never changes focused side.

## Independent continuity

Each front preserves its visual and interaction continuity independently:

- applying a step rebuilds only the affected side's engine using carry-over from that side's prior engine;
- cursor travel rebuilds only the affected side;
- a step on one side does not reseed, refit, clear selection, clear pins, or reset zoom on the other;
- resizing a pane recomputes its camera projection for the new rectangle while retaining its user zoom and engine coordinates;
- selection and pins are pruned only when their referenced semantic identities disappear from that side's current cursor state.

Both viewports run under one workspace animation owner. The workspace schedules one frame and asks each live viewport to settle and paint into its own canvas. A viewport does not create an independent global animation loop.

## Meet and declaration

The seam is the only fixed-side meet indicator:

- it shows `DISTINCT` while `meet(session)` is false;
- it shows `MEET` when the two cursor diagrams have equal canonical form;
- only `MEET` enables the declaration action.

Declaration remains explicit. It calls `assembleTheorem` using both cursor prefixes, verifies through the existing theorem checker, adopts through the existing session and Indexed Ledger path, and exposes the verified theorem to replay. No success toast is shown; the seam/lifecycle transition and adopted theorem are the visible result.

If the fronts cease to meet after cursor movement, declaration disables immediately. A failed declaration or proof step leaves both session timelines and both viewport states unchanged and reports the kernel refusal beside the initiating pointer when a pointer exists.

## Lifecycle and obsolete presentation

Fixed-side entry still requires explicit LHS and RHS snapshots. Starting it:

1. creates one `ProofSession`;
2. replaces the single-canvas proof surface with `FixedSideWorkspace`;
3. creates forward and backward viewports at their origin diagrams;
4. focuses forward initially without changing the 50/50 layout;
5. binds the temporal rail to the forward timeline.

Exit cancels both front gestures, disposes every viewport and workspace listener, removes both canvases and the seam, restores the Edit canvas, and clears fixed-side-only visual state.

The production side-toggle control and fixed-side companion presentation are deleted. `companionFor` remains available only where independently required by theorem replay; it is never called as the fixed-side workspace. Production does not import `dual-front-prototype.ts`, `ui-lab/dual-front.css`, or any lab history/interaction authority.

## Component boundaries

The intended production boundaries are:

- `src/app/proof-front.ts`: disposable `ProofFrontViewport`, its view state, production proof interaction wiring, diagram reconciliation, resize, settle, and paint;
- `src/app/fixed-side-workspace.ts`: two-front composition, divider/focus/seam routing, single animation ownership, session application callbacks, meet/declaration presentation, and disposal;
- `src/app/shell.ts`: lifecycle entry/exit, authoritative `ProofSession` reference, adoption/Library integration, Compass and temporal binding, and switching between ordinary canvas and fixed-side workspace;
- `src/app/session.ts`: unchanged semantic authority;
- `app/style.css`: production pane, seam, focus, and responsive styling.

If extracting `ProofFrontViewport` reveals a shell-only interaction dependency, that dependency moves behind the narrow viewport interface. The workspace must not reach into shell-local engine, selection, or controller fields.

## Responsive boundary

The approved side-by-side form remains authoritative. On widths too narrow to give both panes usable space, fixed-side entry refuses locally with an explanation that the workspace requires a wider window. It does not silently switch to stacked panes, a toggle, or PiP. The minimum supported workspace width is derived from two 320-pixel panes plus the seam and outer insets and is enforced consistently in entry and resize handling.

## Validation

Focused automated evidence must prove:

1. One `ProofSession` feeds two viewports without timeline or diagram duplication.
2. The same production proof gesture applies on both panes with the correct orientation.
3. Pointer focus precedes gesture routing; keyboard and the temporal rail follow visible focus.
4. Each side retains an independent cursor, future, camera/zoom, selection, pins, hover, and engine continuity.
5. Applying or scrubbing one side does not rebuild or reset the other.
6. Divider dragging clamps at 30–70%; double-click restores 50%; focus never resizes panes.
7. Compass, Ledger, utilities, palettes, refusals, and previews do not change pane bounds or cameras.
8. `DISTINCT` disables declaration; canonical `MEET` enables it; declaration produces a replay-checkable adopted theorem from cursor prefixes.
9. Exit and disposal remove both canvases, all workspace/front listeners, active palettes/previews, and the animation owner.
10. Production contains no fixed-side toggle, fixed-side companion path, prototype import, duplicate session, duplicate history, or per-front global animation loop.

Only focused semantic/unit tests, type checking, and relevant production browser tests are required. Physics sources and physics-heavy tests are excluded.
