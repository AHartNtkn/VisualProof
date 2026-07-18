# Passive In-Puzzle Guidance

**Date:** 2026-07-18
**Branch:** `game/cursebreaker-domain`
**Status:** behavior approved; visual treatment remains unselected

## Outcome

Every authored in-puzzle intervention appears as a passive note at the workspace
edge. An intervention contains one or more concise paragraph pages; longer
tutorials advance only when the player chooses Next. Guidance never stops play,
captures focus, blocks an input surface, requires acknowledgement, or takes Escape
precedence. A player who does not want help can continue solving without
interacting with the note.

This replaces the modal opening-instruction design and the closeable
recognized-state commentary design. It does not add generic hints, timed hints,
or stalled-play detection. New copy is limited to the required first-puzzle
interaction tutorial.

## Ownership and state

The game controller owns guidance as non-transient puzzle presentation state.
Guidance is not represented in the input-owning transient slot shared by pause and
the construction editor. The controller evaluates authored semantic triggers in
the same transition that selects a puzzle or commits a proof-state change.

Controller state contains:

- the currently relevant passive guidance note and current page, or no note; and
- puzzle-qualified identities for once-only guidance already delivered.

Selecting a puzzle can deliver its authored opening note atomically. Committing a
legal proof step clears an opening note and can atomically replace it with an
authored recognized-unwinnable note when the resulting diagram exactly matches
the intervention state. Moving the timeline clears a recognized-state note when
the selected state no longer matches and can restore only an applicable
repeatable note. Advancing guidance changes only its page and saves immediately;
it never changes the proof. Leaving puzzle mode clears current guidance. Once-only
delivery is recorded when the note is presented, not through a later player
action. The current note and page persist so startup resumes the exact page.

There are no open-guidance, acknowledge-guidance, or close-guidance actions. One
`advanceGuidancePage` action exists solely for optional page turning. The old modal
teacher transient, manual acknowledgement lifecycle, and runtime follow-up
dispatch are deleted rather than retained behind aliases or adapters.

## Presentation and input

One presenter renders the exact authored text in a restrained note along the
outer workspace edge. At desktop sizes it sits outside the proof aperture,
timeline track, folio records, and record-drag path. At compact sizes it moves to
the available edge without covering the centered lens, folio drawer handle,
timeline handle, or construction-loupe terminal.

The note has:

- no backdrop or scrim;
- no title, portrait, speaker name, close affordance, or acknowledgement;
- no automatic focus movement, focus trap, or global keyboard listener;
- no pointer surface over game controls;
- no dialog or automatic live-region semantics; and
- no effect on proof, timeline, folio, editor, pause, or Escape input.

A one-page note has no action. A multi-page note shows one restrained Next action
only while another page remains. Clicking it replaces the current paragraph in
place and preserves normal focus behavior; it is not an acknowledgement and is
never required. The final page has no Next action.

Pause and the construction editor visually supersede the note while they are
open. Closing them reveals the note again only if it remains semantically current.
Escape therefore opens pause directly when no input-owning transient is open; it
never closes guidance.

## Lifecycle by intervention type

### Opening guidance

An authored opening note appears after the puzzle composition has loaded. It
remains peripheral and passive. The first legal proof-state change removes it.
Changing only interface settings does not remove it. Leaving the puzzle removes
it. A once-only opening note is not delivered again after restoration or later
selection once its delivery identity has been saved.

The first puzzle is the deliberate multi-page exception. Its pages teach the
actual production interaction in this order:

1. moving over a proof mark reveals its interactive highlight;
2. clicking a highlighted mark selects it and the persistent selection treatment
   distinguishes it from hover;
3. clicking a selected mark again removes it from the selection, while clicking
   the empty field clears the selection;
4. only on the final page, selecting the paired boundary and either choosing the
   discovered elimination action or using its contextual Delete/Backspace command
   to perform the completing proof move.

These pages are practical interface instruction, not added lore. The player can
perform the finishing move on any page; doing so completes the puzzle normally.

### Recognized unwinnable guidance

An authored unwinnable-state note appears only after a legal move reaches the
exact catalog-validated diagram. It replaces an opening note if one remains. It
explains how to recognize the state and use the timeline to recover. Rewinding or
otherwise leaving that exact state removes it immediately. The note never disables
the timeline it recommends.

### Completion response

Authored completion commentary remains inside the dedicated completion screen.
It contains exactly one page, does not create a passive in-puzzle note, and does
not add a second acknowledgement step.

## Motion and accessibility

Normal motion uses one restrained edge-local material settle. It does not cross
the proof, delay input, or move game geometry. Reduced motion replaces travel with
a short opacity/depth change. Interface text-size settings scale the note while
the layout continues to avoid all interactive surfaces.

The note is ordinary readable aside text and is discoverable through document
navigation without unsolicited screen-reader announcement. Its contrast is
validated against the actual desk and lens-edge materials. Hiding beneath pause
or editor presentation does not mutate delivery state.

## Visual review boundary

The behavior above is final. A later focused visual gate may compare edge-note
materials, typography, attachment, restrained settle motion, and the unobtrusive
Next treatment using the real runtime projection. Every candidate must use the
same passive geometry and input contract. No candidate may reintroduce a centered
panel, scrim, dialog, acknowledgement, close action, automatic focus behavior, or
input ownership. Review-only candidate selection and rejected CSS are deleted
after selection and are never committed as production authority.

## Decisive validation

Controller and real-browser tests must prove:

1. selecting a puzzle atomically presents and records a once-only opening note;
2. every page is one nonempty paragraph, single-page notes have no action, and
   multi-page notes expose exactly one Next action only before the final page;
3. advancing replaces only the paragraph, saves the page, and restores that exact
   page on startup without changing proof state or moving focus automatically;
4. the note renders exact authored copy without a dialog, backdrop, title,
   acknowledgement, close action, pointer obstruction, or keyboard ownership;
5. proof gestures, theorem drops, folio controls, the timeline, undo/redo, and
   Escape-to-pause remain immediately usable while guidance is visible;
6. the first legal proof-state change clears opening guidance from any page;
7. the first puzzle pins the approved basic-interaction sequence and reserves the
   completing proof move for its final page;
8. an exact recognized-unwinnable state presents its authored recovery note and
   rewinding away clears it;
9. once-only delivery and active-note restoration follow saved semantic state;
10. pause and editor layering, all text sizes, reduced motion, compact layout, and
   disposal preserve the passive contract;
11. completion commentary appears only on the completion surface;
12. generic, timed, and stalled hint behavior remains absent; and
13. modal teacher intents, teacher transients, open/acknowledge/close actions,
    acknowledgement buttons, modal candidate CSS, and tests asserting those
    structures no longer exist.

Validation uses focused unit, save, type, real-browser, asset-consumption, and
production-build checks. Headless capture may be used for the later visual gate.
The desktop app is not opened during automated work, and unchanged physics tests
remain excluded.
