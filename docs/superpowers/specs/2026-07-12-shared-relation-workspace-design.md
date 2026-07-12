# Shared relation workspace, abstraction matching, and contextual copy

## Outcome

Substitution and comprehension abstraction use one relation-authoring window and one set of construction interactions. Proof-mode wrapping opens an uncommitted abstraction transaction, automatically finds every exact occurrence of the authored relation inside the wrapped content, and lets the player cycle and edit complete maximal non-overlapping replacement sets before finalizing.

Selected graphical content can be dragged into the relation workspace as a structural copy. The same selected-pattern drag copies content elsewhere whenever either genuine iteration or a tactic of existing contextual proof moves can construct the attachment-preserving result. No arbitrary graphical-insertion or copy-pattern kernel rule is introduced.

Proof history, undo, save/load, and replay use the same action units the player experienced, even when one gesture verifies by replaying several kernel steps.

## Responsibility model

### RelationWorkspace

`RelationWorkspace` is the only relation-pattern window. It owns:

- the draft diagram and its gesture-level undo/redo history;
- selection, spawning, local connection, fission, and placement;
- the spatial ordered boundary-port strip;
- host-wire references and their presentation;
- host-to-workspace structural copy;
- window layout, rendering, focus, and lifecycle cleanup.

It does not decide proof polarity, choose a comprehension rule, search host occurrences, or commit proof history.

The current substitution-specific `ComprehensionEditor` and fixed-boundary draft authority are replaced, not wrapped. Existing renderer, viewport, connection, spawning, and draft-history primitives may be retained only behind the shared workspace.

### Transactions

Two thin transactions configure the workspace:

- `SubstituteTransaction` targets an existing bubble, supplies its forced argument ports, owns optional parameter bindings, and finalizes through `comprehensionInstantiate`.
- `AbstractTransaction` owns the source proof snapshot, wrap selection, provisional bubble presentation, occurrence matching, exclusions, empty occurrence, and finalizes through `comprehensionAbstract`.

All diagram-changing input belongs to the open workspace. A mode/side switch, global undo/redo, other fixed-front mutation, theory replacement, return to Edit, or session reset first cancels the transaction and then performs the requested lifecycle action. A source fingerprint and live-ID check remain as defensive guards; stale finalization refuses without mutating either source or draft.

### Existing kernel authorities

`applyComprehensionInstantiate` and `applyComprehensionAbstract` remain the semantic authorities. The exact occurrence matcher and occurrence-to-selection conversion remain matching primitives. The UI may preview and organize candidates, but the final kernel application rechecks polarity, scope, boundaries, fingerprints, overlap, and all other rule gates.

## Shared workspace boundary

The boundary is a visible strip of spatially ordered ports.

A port records:

- its draft wire;
- whether it is forced or optional;
- its position in the strip;
- for substitution parameters, its optional host-wire binding.

Dragging a draft wire onto an empty strip position creates an optional port there. Dragging an optional port along the strip reorders it. Selecting an optional port and pressing Delete removes it; if it carries a host binding, that pending edge is removed in the same workspace history action.

Substitution begins with the target bubble's argument positions as a locked ordered block. Those ports cannot be deleted or reordered. Optional parameter ports follow the forced block and may be reordered among themselves. A host-to-draft connection may create and bind the required optional parameter port directly; an unbound optional parameter port disables Finalize until it is bound or deleted.

Abstraction begins with no ports. Every port is optional. Submitted spatial order defines relation argument order, and submitted count defines the new bubble's arity. Arity is therefore not selected before authoring and can change throughout the transaction.

## Proof-mode abstraction transaction

### Opening and cancellation

Invoking wrap in Proof mode on selected content opens `AbstractTransaction` immediately. The proof session remains on its untouched source diagram. The canvas renders a provisional bubble around the selected content from transaction view state; no `ProofAction` or `ProofStep` has been recorded.

Cancel, window close, Escape at the transaction level, or any lifecycle transition removes the provisional presentation and returns to the exact source diagram and proof cursor. There is no inverse cleanup step because no proof mutation occurred.

Edit-mode wrapping remains ordinary statement construction and does not open abstraction.

### Live exact matching

Every draft or boundary change starts an exact, boundary-pinned occurrence search restricted to the provisional wrap contents. Matches outside the wrap are never candidates. Each candidate carries the exact `SubgraphSelection`, ordered argument wires, canonical identity key, and the nodes, internal wires, and regions used for overlap checks.

The search is fuel-bounded. Fuel exhaustion is distinct from an exhaustive zero-match result. Either state preserves draft work and disables Finalize with a specific message.

### Maximal non-overlapping sets

Candidate overlap is defined exactly as the kernel rule defines it: shared selected nodes, selected regions, or internal wires. A maximal set is a disjoint set to which no remaining allowed candidate can be added.

A pure solver lazily enumerates deterministic maximal sets. Sets are ordered by:

1. descending occurrence count;
2. then the lexicographic sequence of canonical occurrence keys.

The first set therefore replaces the most occurrences. Tab and Shift+Tab cycle complete sets. Every displayed set is immediately admissible by the overlap gate; the UI never highlights an internally contradictory partial choice.

Clicking a highlighted occurrence excludes its canonical identity and recomputes maximal sets under the exclusion. Clicking an excluded occurrence restores it. Draft changes retain exclusions only when the same canonical occurrence identity still exists; stale exclusions disappear.

The active set uses the existing green complete-group highlight. Competing candidates are normally rendered. During keyboard cycling the next complete set previews, then becomes active.

A nonempty draft cannot finalize unless the active set contains at least one occurrence.

### Empty pattern

An actually empty draft has one empty-occurrence marker rather than infinitely many empty matches. The marker is a floating bubble inside the provisional wrap:

- its containing region is the semantic anchor of the nullary occurrence;
- its screen position is the placement hint for the resulting bound atom;
- it is draggable among valid regions inside the wrap;
- it is selected by default and may be deselected.

Finalizing with the marker selected creates one nullary bound atom at that anchor. Finalizing with it deselected creates the trivial/vacuous wrap. This is the only zero-selected-match finalization; a nonempty unmatched pattern remains blocked.

### Finalization

Finalize snapshots the source diagram, wrap selection, submitted relation diagram and boundary order, active occurrence set, ordered argument wires, and any empty-marker anchor/placement.

The real kernel applier runs against the untouched source diagram. On success, the workspace closes and one `comprehensionAbstract` action is committed. On refusal, the workspace remains open with its draft, ports, exclusions, active set, and marker unchanged.

Substitution follows the same transaction discipline around `comprehensionInstantiate`.

## Shared copy interaction

### CopyPlanner

One pure `CopyPlanner` accepts:

- the source diagram and complete selected subgraph;
- destination diagram/region or relation workspace;
- mode and proof orientation;
- scope and binder context;
- attachment policy.

It returns either a complete immutable plan or a refusal. Planning never mutates a diagram.

For a same-diagram Proof destination, the planner:

1. uses genuine `iteration` when its existing gate applies;
2. otherwise compiles the copy into currently valid ordinary spawn, wrap, join, and related construction steps;
3. replays the complete candidate step sequence on a scratch diagram;
4. offers the target only when the replay constructs the full copy with every crossing attachment identity preserved.

There is no partial plan and no general copy/pattern `ProofStep`. If an attachment cannot be reproduced through valid moves, that destination is not a target.

Edit uses the same structural extraction, ID mapping, and attachment plan without proof gates. The relation workspace uses the same extraction and clone mapping with a deliberate boundary policy: every wire crossing from the host selection becomes a loose draft wire. It does not automatically create a boundary port or a host parameter reference.

### Gesture and feedback

Plain-dragging any item in a selected pattern begins copy targeting. Connection dragging has priority on wires, internal-subterm fission has priority inside term anatomy, and whole-selection copying owns the remaining selected-pattern surface. Ctrl remains physics-only and never begins copy.

Every valid destination uses the existing green copy preview. The player is not shown whether the backend selected iteration or a construction tactic because the experienced operation is the same. Drop revalidates the immutable plan against live state before committing. Refusal leaves no partial nodes, wires, regions, history entries, ports, or highlights.

Dragging a host selection across the workspace boundary uses the same preview and creates one draft-history action. The copied content is placed at the drop point.

## Durable user actions

The proof model's visible and serialized unit becomes:

```ts
type ProofAction = {
  readonly label: string
  readonly steps: readonly ProofStep[]
  readonly placements: readonly PlacementHint[]
}
```

Ordinary moves produce one-step actions. A synthesized copy produces one action containing its verified constituent steps. Undo, redo, cursor counts, scrubber stops, fixed-front ownership, theorem replay, and saved files all operate on `ProofAction`s.

Kernel verification and proof composition flatten action steps in order and continue to apply the existing trusted appliers. ID composition maps every constituent step and retains its enclosing action. Placement hints affect presentation only and are checked against nodes introduced by the action.

The theorem JSON format stores action groups directly. Bundled derivations, examples, tests, and persistence migrate to the action format, normally with one existing step per action. The displaced flat-step theorem/history format is not retained through an alias, sidecar, or compatibility decoder; malformed or obsolete flat proof JSON is rejected.

## Error and lifecycle behavior

- Invalid draft construction preserves the previous valid snapshot and reports the refusal.
- Port deletion atomically removes its optional binding.
- A source selection invalidated before drop cancels the copy preview.
- A destination invalidated before drop refuses the whole plan.
- A host proof change first cancels the workspace; an unexpected stale fingerprint blocks Finalize defensively.
- Matcher exhaustion, zero matches, overlap-set exhaustion, invalid ports, unbound parameters, and kernel refusal have distinct messages.
- Window disposal clears host/draft highlights, empty markers, copy previews, pointer claims, and provisional bubble state.

## Validation

Pure tests cover:

- port creation, spatial insertion, reorder, forced-port refusal, optional deletion, and binding cleanup;
- substitution and abstraction transactions over the same workspace state machine;
- bounded exact matching, wrap restriction, diagonal argument order, deterministic maximal sets, cycling, exclusions, restoration, and draft invalidation;
- nonempty zero-match refusal and selected/deselected empty markers in nested regions;
- copy extraction, iteration selection, construction-tactic fallback, attachment preservation, cross-window loosening, scratch replay, and atomic refusal;
- proof-action flattening, composition, undo/redo, save/load, obsolete flat-JSON rejection, replay grouping, and placement hints.

Browser demonstrations cover ordinary and both fixed Proof fronts in both orientations:

- Proof wrap opening the provisional workspace and exact cancellation;
- substitution and abstraction using the same DOM/window implementation;
- editable ports and visible argument order;
- host-to-window selected-pattern copying;
- live match highlights, maximal-set Tab cycling, click exclusion/restoration, and Finalize;
- selected and deselected empty-pattern outcomes;
- genuine iteration and constructible fallback copy with identical green feedback;
- Ctrl physics non-interference;
- one gesture, one timeline action, one undo, durable save/load, and grouped replay;
- stale lifecycle cancellation and owning-front isolation.

Architecture checks require exactly one relation workspace, one boundary-port model, one copy planner/controller, and durable action-group proof history. Searches must find no duplicate abstraction editor, substitution-only window authority, UI-only grouping sidecar, or arbitrary graphical insertion/copy rule.

Typecheck, generated artifacts, all ordinary tests, and all browser tests must pass. The opt-in physics suite runs only if physics implementation changes; using existing Ctrl routing does not itself require it.
