# Proof Interaction Integration Design

**Status:** Approved  
**Date:** 2026-07-10

## Outcome

Production proving uses the approved direct-manipulation vocabulary in both forward and backward reasoning. Orientation changes semantic polarity gates and citation direction; it does not select a separate UI implementation.

## One interaction authority

A focused proof-move coordinator owns proof-mode action discovery, gesture state, step construction, and transient overlays. It consumes the current diagram, selection, proof context, orientation, pointer position, and a sink that applies an ordinary `ProofStep` or displays a refusal.

The coordinator does not own proof sessions or mutate diagrams. The shell's existing track and dual-front session paths remain the sole step-history authorities. Both call the same coordinator and pass orientation as data.

The following production paths are removed rather than wrapped:

- `BackwardEntry`, `backwardEntries`, and `commitBackward`;
- manual citation and un-citation boundary-wire picking;
- menu-triggered click-a-region iteration;
- relation-name entry through the λ-term field for instantiation;
- any backward-only action label or hidden alternate gesture;
- any duplicate memory box or success feedback.

## Discovery and contextual palette

The action palette appears only after an explicit still right-click. It opens beside that pointer.

- Right-clicking a selected object uses the absorb-normalized selection and shows only actions legal for that selection and orientation.
- Right-clicking a prove-mode region without a selection may show closed theorems insertable at that region.
- Ordinary selection never opens or updates the palette by itself.
- Escape, a new pointer press outside, mode exit, or coordinator disposal closes the palette and cancels citation ambiguity.

Applicability is derived from the same action and matcher inputs used to build a commit. Kernel appliers remain authoritative and their refusal text is displayed verbatim beside the current pointer.

## Dedicated mechanics

### Contextual Delete

Delete or Backspace interprets the absorb-normalized selection in this precedence:

1. eliminate a selected double cut;
2. dissolve a selected vacuous bubble;
3. erase content when polarity permits;
4. deiterate when a justifying occurrence permits.

Erasure adds same-region wires that would otherwise become endpointless because every endpoint node is erased. Deiteration does not add those rider wires because they are part of occurrence matching. An unavailable deletion refuses with `nothing here reads as a deletion` beside the pointer.

### Wraps

`W` emits double-cut introduction for the absorb-normalized selection. `Shift+W` asks for arity at the pointer-local palette and emits vacuous-bubble introduction. These are proof steps, not construction edits.

### Drag-to-iterate

Pressing a selected node without Shift may begin an iteration candidate. Pointer movement beyond the established gesture threshold turns it into iteration; a stationary click retains ordinary toggle-off selection behavior.

During the drag, every semantically legal target region glows green and the region under the pointer strengthens. Releasing in a legal region emits one iteration step. Releasing elsewhere refuses beside that pointer. Shift always preserves selection-only behavior and cannot begin iteration.

### Conversion

Double-clicking a term node in prove mode performs quick normalization through the existing certificate-producing tactics. The contextual palette also offers head normalization and a custom βη-equal target. Every path emits the ordinary checked conversion step; no conversion-specific semantic authority exists in the coordinator.

## Infer-first citation

For each theorem, direction is derived from selection/invocation polarity XOR proof orientation. The coordinator chooses the theorem side implied by that direction and searches the current diagram with the authoritative occurrence matcher.

- A non-closed theorem appears only when at least one occurrence contains every selected item.
- Boundary attachments and the complete kernel selection come from the occurrence; the user never picks argument wires.
- One occurrence commits immediately.
- Several occurrences enter one ambiguity state. The current occurrence is highlighted; `Tab` or a click cycles, `Enter` applies, and `Escape` cancels. Cycling emits no message.
- A closed theorem appears separately and commits as an empty selection at the right-clicked region with no arguments.

Forward and backward citation use this exact flow; only the derived direction differs.

## Folded instantiation and relation folding

When a selected bubble can be instantiated, the palette lists only loaded relations of matching arity. Selecting a relation constructs a one-reference diagram-with-boundary and emits `comprehensionInstantiate`. It never submits the stored definition body or expands the relation automatically.

Relation unfolding remains immediate. Relation folding derives boundary arguments with the existing matcher-backed `inferFoldArgs`; it never asks the user to order wires manually.

Anonymous comprehension construction remains a separately approved later integration item and is not invented here.

## Feedback and history boundaries

Successful proof steps produce no toast, banner, or announcement. Their result is visible in the diagram and proof history.

One refusal may appear beside the pointer with the kernel's text unchanged. Selection remains renderer-owned orange geometry. Citation candidates and legal iteration targets use transient overlays only.

The approved proof-history surface is the sole undo/redo representation. This integration adds no memory box, chronicle, or secondary step display. Cursor-based history and scrubber chrome remain Task 4.

## Ownership and teardown

- Kernel appliers own semantic legality and validation.
- `applicableActions` owns orientation-sensitive action gates.
- The occurrence matcher owns citation occurrences and boundary attachments.
- Tactics own conversion certificates.
- The proof-move coordinator owns gesture-to-step translation and transient proof overlays.
- Track/dual sessions own step application and history.
- The shell owns DOM placement, current pointer, and mode routing.

The coordinator installs no global lifecycle that the shell cannot dispose. Proof mode exit clears its palette, drag, prompt, and citation-cycle state.

## Validation

Automated tests must prove:

1. Contextual Delete precedence, absorb normalization, and erasure-only orphan riders.
2. Identical forward/backward action vocabulary with only polarity/direction differences.
3. Drag-only iteration, exact legal targets, overlay state, invalid-release refusal, and Shift purity.
4. Double-click quick normalization and checked head/custom conversion steps.
5. Citation filtering by occurrence and selection, inferred attachments, immediate unique commit, ambiguity cycling, closed insertion, and orientation-derived direction.
6. Folded instantiation creates a reference comprehension of matching arity and never expands the stored relation body.
7. Explicit right-click is the only palette trigger; success feedback remains absent and refusals remain pointer-local and verbatim.
8. The displaced backward builder, manual citation-wire pending states, click-target iteration state, and duplicate feedback paths are absent from production.
9. Forward and backward tracks accept the same direct gestures and produce replay-checkable declarations.

Only focused application/unit tests, type checking, and relevant proof-interaction browser tests are required. Physics source and physics-heavy tests are excluded.
