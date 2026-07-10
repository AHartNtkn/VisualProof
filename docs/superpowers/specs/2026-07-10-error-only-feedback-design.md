# Error-Only Feedback Design

**Date:** 2026-07-10  
**Status:** Approved for implementation planning

## Outcome

The application gives additional feedback only when an attempted interaction fails or an editable value remains invalid. Successful state changes, selection, mode, history, and active tools communicate through their own authoritative visual state rather than messages about that state.

This design replaces the Round 17 Field Signals, Focus Ribbon, and Chronicle Margin comparison. It does not select a generic notification surface because the application does not need one.

## Ownership model

### Diagram selection

The diagram renderer owns selection. Every selected node, region, and wire is highlighted directly in the established orange interaction color. Unselected objects retain their normal rendering even when geometrically surrounded by selected objects.

Selection has no aggregate outline, oval, pulse, halo, callout, prose description, or live-region announcement. Changing selection does not expose actions by itself.

### Contextual actions

An explicit right-click owns one action invocation and its pointer position. It opens the applicable action palette beside that pointer. The palette is absent before invocation and closes after an action is chosen, Escape is pressed, or the user clicks elsewhere.

The palette is the sole home for instructions required by the invoked action. If an action opens a dedicated editor, subsequent instructions and validation belong to that editor. No instruction is placed in a bottom strip or generic toast.

The palette and its subpanels remain adjacent to the invocation point while open. Near a viewport edge, they clamp or flip into the viewport without moving to an unrelated screen location.

### Successful operations

The resulting authoritative state is the complete success indication. Successful diagram edits, pins, proof steps, saves, mode changes, replay movement, and relation operations emit no toast, callout, ribbon entry, Chronicle entry, status prose, or assistive announcement.

This silence is intentional. A success message that repeats a visible state change is noise and must not be retained for logging or later presentation by the feedback system.

### Transient refusals

A failed attempt produces one temporary red refusal beside the current mouse pointer, because that is where the user is most likely looking. The refusal preserves the authoritative error text verbatim.

The refusal is visually compact, does not move or outline diagram objects, and does not accumulate into history. A new refusal replaces the prior transient refusal. It disappears after its readable lifetime or when a new interaction makes it irrelevant.

Pointer placement is based on the pointer position at failure time, not the selection centroid, attempted geometry centroid, diagram center, or control center. It clamps into the viewport while remaining adjacent to the pointer.

The same refusal text is announced once through an assertive live region. Expiry is not announced.

### Persistent editable problems

An invalid value that remains editable is not a transient refusal. The owning field displays one persistent inline problem adjacent to itself, marks its invalid state accessibly, and retains the problem until the value is corrected or the editor is cancelled.

Correction clears both the inline problem and its accessibility state immediately. Persistent problems do not also produce a pointer toast, issue counter, Chronicle row, or generic notification.

### Mode and history

Mode remains visible only in the existing mode control. Replay position and proof history remain visible only in the existing timeline and its controls.

There is no Chronicle, recent-events rail, success log, or feedback representation of mode/history state.

## State model

The feedback authority has only two semantic responsibilities:

1. One optional transient refusal containing exact text, sequence identity, pointer position, and expiry policy.
2. Persistent field problems keyed by stable field/problem identity and owned by the relevant editor field.

The authority does not represent ambient messages, guidance, success, mode, history, selection, action availability, physics state, or completed events. Those concepts remain with their actual owners.

The action palette has its own explicit invocation state: open/closed, invocation pointer, applicable actions, and active action step where needed. It does not depend on feedback state.

## Presentation

- Selection uses the existing Light/Dark orange interaction colors and exact object geometry.
- Refusals use the existing red refusal color and appear beside the pointer.
- Field problems use the same refusal color inline at the field.
- No feedback presentation draws diagram geometry.
- No success styling or animation exists.
- No generic feedback container is mounted when there is no refusal.
- The action palette appears only on right-click and is visually distinct from a refusal.

## Lifecycle examples

### Successful relation definition

1. The user selects diagram objects; only those objects turn orange.
2. The user right-clicks; the action palette opens beside the pointer.
3. The user chooses **Define relation**; the relation editor opens at that locus.
4. The user commits a valid relation.
5. The relation appears in its authoritative destination and the editor closes. No success message appears.

### Refused action

1. The user invokes or attempts an action at the pointer.
2. The authoritative operation refuses it.
3. One red message containing the exact refusal appears beside the current pointer and is announced once.
4. The diagram and history remain unchanged.

### Invalid relation field

1. The user enters an invalid value in the invoked editor.
2. The field displays the problem inline and remains marked invalid.
3. No pointer toast or issue counter duplicates it.
4. Correcting the value clears the problem immediately.

## Removed model

Implementation removes rather than hides or aliases:

- Round 17 Chronicle Margin and its retained event list;
- Focus Ribbon and generic Field Signal callouts;
- success, guidance, ambient, mode, and history feedback kinds and emitters;
- aggregate feedback pulse/oval geometry;
- selection narration;
- automatic selection-driven action-strip visibility;
- the bottom-centered action strip;
- selection-, target-, or viewport-centered refusal placement;
- issue counters that duplicate inline field problems;
- prose parsing or latest-message compatibility paths.

No adapter, deprecated path, fallback toast, or parallel feedback authority remains.

## Validation

Authoritative browser tests must prove:

1. Selecting a mixed set highlights each selected node, region, and wire orange using its exact geometry; a nearby unselected object remains unchanged.
2. Selection alone leaves the action palette absent.
3. Right-click opens the palette beside that pointer; Escape and outside click close it; edge invocation remains on-screen.
4. Successful diagram edits, pinning, relation definition, proof steps, mode transitions, saves, and replay movement produce no visible feedback message and no live-region announcement.
5. A real kernel or parser refusal appears beside the current pointer with verbatim text, replaces an earlier refusal, expires, and leaves history unchanged.
6. A persistent invalid field problem appears only inline at its field, remains while invalid, clears immediately when corrected, and is not duplicated elsewhere.
7. Mode and replay position remain authoritative in their existing controls.
8. No Chronicle, feedback ribbon, aggregate pulse, issue counter, bottom action strip, or removed feedback kind is present.

Typechecking, focused unit tests for refusal/problem lifetime, and the established application, interaction, construction, layout, aesthetic, Library, and feedback browser suites must pass after their obsolete assertions are replaced with this ownership model.
