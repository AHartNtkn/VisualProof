# Anonymous Comprehension Editor — Production Integration Design

**Date:** 2026-07-11  
**Status:** User-approved design; written-spec review pending  
**Scope:** Production integration of the approved anonymous relation-construction editor

## Outcome

An applicable relation bubble can be instantiated with either a matching named
folded relation or a newly constructed anonymous relation. Choosing the latter
opens the approved draggable, resizable mini-EDIT canvas beside the invocation
point. The user constructs a checked relation, connects its formal boundary and
external proof identities through direct wire gestures, then either cancels
without changing the proof or commits exactly one `comprehensionInstantiate`
proof step.

The editor is available in ordinary forward/backward proving and in either
fixed-side proof front. It is one production component, not separate shell and
split-view implementations.

## Controlling Interaction Decisions

- The editor opens beside the right-click invocation point, clamped to the
  visible viewport. It can be moved by its title and resized from its corner.
- The proof stays visible behind it. The editor does not move the user's eye to
  a permanent side panel or replace the selected bubble with an editing surface.
- The editor uses the established construction language: brush selection,
  contextual spawn, W/Shift+W wrapping, Delete, joining, severing, semantic
  reparenting, Ctrl-drag physics, and cursor-relative bounded zoom.
- The formal boundary is a stable visual frame. Diagram content rescales inside
  it as the draft grows. Maximum zoom-out is the full-boundary fit.
- Boundary position 0 receives the prominent orientation dot. Other formal
  positions receive only ordinary existential marks when semantically present.
  The editor never overlays “Arg 1” or other invented port names.
- A wire gesture may begin in the draft or proof and end on an eligible wire in
  the other surface or in the draft. Boundary positions may be connected to one
  another.
- Established host/draft identity is communicated by synchronized blue
  highlighting and glow. Legal source/targets use the normal green interaction
  color. No persistent line connects the proof diagram to the editor window.
- Reusing one host wire fuses the new draft source with its existing imported
  representative. It does not create another external binding or phantom port.
- Host-to-host connection is refused because the proof is read-only while the
  draft is open.
- Draft-node dragging runs the same live production physics as the main app;
  connected unheld nodes and wires respond during the drag rather than snapping
  only on release.
- Success is visible and silent. Failures use the production pointer-local
  refusal surface with the semantic message.

## Responsibility Model

### `ComprehensionDraft`: semantic authority

`src/app/comprehension-draft.ts` remains the only draft semantic model. It owns:

- the immutable original host diagram and selected bubble;
- the bubble arity and ordered formal boundary positions;
- immutable draft snapshots and the current cursor;
- normalized draft-wire ↔ host-wire external bindings;
- prospective connection planning and complete kernel validation;
- materialization into a diagram-with-boundary plus ordered attachments;
- exact cancel and checked commit.

The module gains one validated whole-diagram replacement operation for ordinary
production edit commands. Replacement preserves the formal boundary positions,
removes bindings only when their draft identity genuinely disappears, normalizes
the remaining binding ledger, and runs the same full prospective instantiation
validation before appending history. It cannot delete a formal position, retain
a binding to a missing/non-root wire, or commit an invalid comprehension.

No DOM, engine, camera, pointer, physics, or proof-session state enters this
module.

### `ComprehensionEditor`: transaction and compositor

A new `src/app/comprehension-editor.ts` owns one open editor window. Its host
contract supplies:

- current host diagram, boundary, engine, canvas, view, context, and theme;
- current proof orientation and fuel;
- a prepared `ProofStep` application sink;
- pointer-local refusal;
- a callback when editor-open state changes;
- a callback requesting the host redraw/chrome refresh.

The editor owns:

- one `ComprehensionDraft` value;
- window DOM, title drag, resize handle, buttons, and prompt/menu containment;
- one editor canvas/engine/view;
- one production `InteractiveViewport` for editor selection, zoom, capture,
  Ctrl-drag physics, and passive live relaxation;
- one configured production `ConstructController` for ordinary draft edit
  mechanics;
- one configured production `SpawnCascade` over the live proof context;
- one cross-surface connection coordinator;
- editor-local history controls and transient paint overlays.

It does not install an animation loop. The owning shell frame or proof-front
frame calls `frame(now)`. It does not copy the host diagram, own proof history,
or apply kernel rules directly outside `ComprehensionDraft` validation.

### Host proof viewports

`ProofMoveController` adds an anonymous entry under the existing “Instantiate
with” section before matching named relations. Selecting it closes the proof
menu and calls `openComprehension(bubble, invocationClient)`; named relations
continue to emit one folded-reference step exactly as they do now.

The main shell and each `ProofFrontViewport` each own at most one editor. They
route, in priority order while it is open:

1. editor host-wire connection claims;
2. editor keyboard commands;
3. no ordinary proof/history/mode mutation.

They append editor host overlays to their normal paint, call the editor frame
from the existing application frame, and cancel/dispose the editor with their
own lifecycle. The host canvas remains read-only except for selection/hover and
cross-surface reference gestures.

`FixedSideWorkspace` reports editor activity across both fronts. If either front
owns an editor, both proof controllers and shared temporal history are blocked;
both fronts continue passive rendering. The owning editor may still submit its
prepared step. Commit reconciles only the changed front through the existing
single `ProofSession` authority.

## Editor Construction Vocabulary

The editor configures existing production components rather than maintaining a
parallel vocabulary:

- `InteractiveViewport` owns brush selection, pointer capture/cancellation,
  cursor-relative zoom, fit, Ctrl-drag physics, pins, and live relaxation.
- `ConstructController` owns node placement/reparenting, W/Shift+W,
  Delete, join/sever, and construction prompts.
- `SpawnCascade` reads the live proof context and can spawn λ terms, named
  relation references, and predicates bound by bubbles inside the draft.
- The draft replacement command validates every diagram result before it enters
  draft history.

Cross-surface wire connection takes precedence over the ordinary wire-join
claim because it subsumes draft-local joins and can continue onto the host.
Right-drag severing remains draft-only. Formal boundary identities are protected
by validation even if a generic edit command attempts to remove them.

Draft Undo/Redo uses the draft cursor and is exposed by title-bar buttons and
Ctrl/Meta+Z with Shift for redo. It never moves the proof timeline. Escape
cancels the editor; Ctrl+Enter instantiates. Text inputs retain ordinary typing
and consume their own Escape/Enter.

## Connection State Machine

A connection gesture stores:

- pointer id;
- source surface and wire identity;
- source draft snapshot identity;
- initial and current client positions;
- whether movement crossed the click threshold.

Hovering a wire without an active gesture previews all eligible targets. Target
sets are derived by applying `planComprehensionConnection` to every draft and
host wire. There is no separate hand-written start/stop permission table.

On release:

- a still gesture remains an ordinary selection click;
- release on no eligible target cancels with pointer-local feedback;
- release on a refused target surfaces the planner message;
- release on an accepted target appends exactly the planner-approved snapshot;
- any intervening draft snapshot change cancels the stale gesture;
- pointer cancellation/lost capture mutates nothing.

The active drag alone may draw a dotted pointer-following segment. Once committed,
the segment disappears and synchronized edge highlighting is the complete visual
representation.

## Boundary and Camera Law

The materialized boundary contains the fixed formal positions followed by one
position for each normalized external binding. Repeated formal positions may
share one wire identity after fusion; repeated host use produces one external
binding and therefore one imported boundary occurrence.

The engine's proof frame is the editor's fit authority. `MIN_USER_ZOOM` displays
the entire frame at its stable shape and screen-relative size. Outward wheel
input at that limit is inert. Adding content rebuilds and carries over the editor
engine, then lets production framing/projecting scale content inside the same
boundary. The editor never stores a second body-scale authority.

Boundary rendering uses the established ordered-slot convention. Position 0
gets the prominent orientation dot; port identification is clockwise from that
mark. No textual positional labels obscure nodes or wires.

## Commit, Cancel, and Failure

Opening the editor does not mutate proof state. Cancel returns the original host
diagram object, closes all menus/prompts, releases captures, clears overlays,
and leaves proof history/cursor unchanged.

Instantiate validates the current snapshot, materializes its relation and
attachments, and creates:

```ts
{
  rule: 'comprehensionInstantiate',
  bubble,
  comp: materialized.relation,
  attachments: materialized.attachments,
  binders: {},
}
```

The owning proof viewport prepares and commits that step through its existing
orientation-aware session/motion path. The editor closes only after preparation
succeeds. A failure leaves the editor and draft open and reports the exact error
beside the attempted pointer/button.

## Styling and Accessibility

The window uses the production Porcelain theme variables and dark-theme rules.
It has a dialog label naming the substituted predicate and arity, accessible
Undo/Redo/Cancel/Instantiate controls, a labelled editor canvas, and a keyboard-
reachable resize/move affordance where practical. Disabled history controls
reflect cursor endpoints. Focus enters the editor when opened and returns to the
host canvas on close.

The window begins at up to 660×560 CSS pixels, clamps within the viewport, and
does not cover the invocation point when space exists to its right. Minimum size
is 420×340; narrow screens clamp to the available viewport rather than creating
an unreachable surface.

## Prohibited Competing Paths

- No import from the archived comprehension prototype or lab CSS.
- No fixture diagram, bundled fixture theory, or standalone demo root.
- No private `requestAnimationFrame` loop.
- No duplicate pointer/selection/zoom/physics implementation.
- No separate main-versus-fixed editor implementations.
- No window-edge connector for established external references.
- No semantic “parent” memory or second body-scale authority.
- No success toast/status event stream.
- No named-relation auto-expansion.
- No compatibility alias retaining the prototype API.

## Validation

Focused unit tests prove:

1. validated whole-diagram replacement and fixed formal positions;
2. canonical external binding materialization and host reuse;
3. two-direction connection targets and stale/cancelled gestures;
4. synchronized external-reference presentation;
5. window placement/resize clamping and boundary position-0 metadata;
6. exact cancel and one prepared commit;
7. main/fixed workspace admission and disposal.

Production Playwright proves:

1. entry through the real proof menu in ordinary proving;
2. formula spawn, selection, wrap/delete/join/sever, and draft Undo/Redo;
3. formal-port fusion;
4. host→draft and draft→host drawing;
5. repeated host use without another imported port;
6. synchronized host/draft glow without a window connector;
7. live connected physics during draft node drag;
8. fixed boundary/full-fit zoom behavior;
9. cancel leaves proof and view unchanged;
10. instantiate advances exactly one proof step;
11. backward and fixed-side use the same component and guard shared mutation;
12. teardown removes window, prompts, captures, overlays, and listeners.

Architecture searches prove the prohibited paths absent. TypeScript and the
focused non-physics test/browser suites must pass. Physics sources and dedicated
physics suites remain untouched.
