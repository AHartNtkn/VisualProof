# History and Chrome Integration Design

**Status:** Approved  
**Date:** 2026-07-10

## Outcome

Production proof tracks and fixed-side fronts use the approved linear cursor history. The real application—not a lab iframe wrapper—presents that history through the Compass Aperture temporal rail while preserving Indexed Ledger, Porcelain surfaces, and Basalt typography.

## Authoritative timeline

Every mutable proof front owns exactly one timeline:

```ts
type ProofTimeline = {
  readonly states: readonly Diagram[]
  readonly steps: readonly ProofStep[]
  readonly cursor: number
}
```

The invariants are:

- `states.length === steps.length + 1`;
- `0 <= cursor < states.length`;
- the visible/current diagram is `states[cursor]`;
- step `i` transforms `states[i]` into `states[i + 1]` in that front's orientation;
- states and steps after the cursor are retained future, not a branch.

Applying a new step truncates `states` after `cursor` and `steps` at `cursor`, applies the step to `states[cursor]` through the existing orientation-aware kernel/session route, appends one state and step, and advances to the new final index. Moving the cursor never mutates either array. No separate `current` or past-only `history` field exists.

## Track and fixed-side sessions

A one-origin `TrackSession` owns one timeline. A fixed-side `ProofSession` owns independent forward and backward timelines. Shared timeline operations implement application and cursor movement; orientation-specific wrappers only select the kernel orientation and statement-boundary validation.

Undo moves the focused cursor by `-1`; redo moves it by `+1`. At either end, the existing pointer-local refusal reports that no movement is available. `Ctrl+Z` and `Ctrl+Shift+Z` invoke these same operations.

Track declaration uses `states[cursor]` and `steps.slice(0, cursor)`. Forward declaration records those as forward steps; backward declaration records them as backward steps. Fixed-side meet compares the two cursor states. Assembly slices each side's steps at its own cursor. A rewound future can never leak into a declared theorem.

## Temporal rail

The production temporal rail is a disposable component consuming a narrow interface:

```ts
type TimelineView = {
  readonly states: readonly Diagram[]
  readonly steps: readonly ProofStep[]
  readonly cursor: number
  readonly boundary: readonly WireId[]
  moveTo(cursor: number): void
}
```

It appears only when a proof track or fixed-side front is active. It contains:

- one inset rail spanning every state;
- a distinct current tick;
- solid past ticks and dashed future ticks;
- Undo and Redo controls using the same cursor authority;
- concise `current / final · step label` copy;
- declaration and exit actions in the lifecycle surface, not duplicated inside the rail.

Dragging anywhere on the rail continuously moves the real cursor to the nearest tick. Hovering anywhere resolves the nearest tick—there are no dead zones—and displays that transition's preview. Leaving or starting a drag closes the preview. Mode exit and disposal remove every listener and preview.

## Zoom-to-change previews

Preview focus is derived from the semantic before/after pair:

- new or structurally changed nodes focus their rendered bodies;
- new or structurally changed wires focus their rendered wire-owned bodies;
- surviving nodes incident to removed wires or adjacent to removed nodes provide focus for removals;
- if no surviving focus exists, render the authoritative state as a whole-diagram fallback.

The preview uses the same production renderer and theme contract. It is cached by immutable before/after diagram identity and theme. It never mutates a diagram, proof timeline, camera, or physics state.

## Theorem replay

Verified theorem replay remains a read-only `Replay` with its own cursor in the shell. It uses the same temporal rail presentation and nearest-tick interaction, but its interface has no mutation, undo truncation, redo branching, or declaration. Replay navigation and proof history therefore share visual vocabulary without sharing semantic ownership.

## Compass Aperture production chrome

The real shell owns the selected Compass Aperture layout:

- A compact north lifecycle capsule is the only mode identity and opens backward, forward, fixed-side, declaration, exit, and mode-appropriate help.
- Backward from the current diagram is the primary ordinary proof entry; forward is secondary; only fixed-side proving exposes explicit LHS/RHS capture.
- Indexed Ledger opens as the approved overlay Library surface without resizing the canvas or changing its camera.
- View/session utilities are disclosed separately and contain theme, companion/view controls, save/load operations, and the keyboard map.
- The temporal rail occupies the south edge only outside Edit mode.
- Contextual proof and construction palettes remain pointer-local and are not moved into chrome.

The permanent generic `editRow`, `goalRow`, and `proveRow` strips are deleted. The lab `layout-frame` iframe compositor is not imported or retained as a production adapter.

## Fixed-side presentation boundary

This task migrates both fixed-side histories to the shared cursor model and routes the temporal rail to the visibly focused front. It must preserve independent side cursors and current diagrams.

The already-approved adjustable side-by-side viewport remains the target fixed-side presentation. If productionizing its two live canvases materially exceeds the history/chrome boundary, that viewport composition is recorded as the next integration slice; Task 4 must not preserve or promote the existing toggle-plus-companion layout as if it satisfied the approved dual-front design.

## Ownership and teardown

- `session.ts` owns timeline invariants, cursor movement, orientation-aware application, declaration slicing, and meet/assembly inputs.
- The scrubber owns temporal DOM and pointer-to-cursor mapping only.
- Preview code owns semantic change focus and cached rendering only.
- The shell owns active/focused front selection, theorem replay cursor, lifecycle commands, and Compass composition.
- Indexed Ledger owns Library navigation and source management.

Every timer, animation frame, DOM listener, observer, preview, and overlay is removed by the owning component's `dispose()`.

## Validation

Automated validation must prove:

1. Timeline invariants on start, apply, undo, redo, rewind, and truncate-on-new-step.
2. Forward and backward tracks use the same timeline operations with correct kernel orientation.
3. Fixed-side fronts retain independent cursors; meet and assembly use cursor states and sliced steps.
4. Declaration at a rewound cursor excludes future steps and produces a replay-checkable theorem.
5. Scrubber coordinate mapping, tick status, continuous dragging, shortcut equivalence, hover cleanup, and disposal.
6. Change-focus derivation for additions, modifications, removals, and fallback.
7. Theorem replay uses the temporal presentation without acquiring editable history semantics.
8. Production Compass owns mode, Library, utilities, and temporal surfaces; generic rows and iframe mirroring are absent.
9. Canvas bounds and camera remain unchanged when Library or lifecycle overlays open.
10. No success feedback, duplicate history representation, or physics mutation is introduced.

Only focused semantic/unit tests, type checking, and relevant UI browser tests are required. Physics source and physics-heavy tests are excluded.
