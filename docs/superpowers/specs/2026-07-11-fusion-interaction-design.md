# Fusion Interaction Design

**Status:** Approved  
**Date:** 2026-07-11

## Outcome

The main proof assistant exposes the kernel's existing fusion rule as a direct
user interaction. The same implementation can subsequently enter the game;
the game does not define its own fusion interaction.

## Interaction

Fusion has exactly two entrances:

1. Double-click a wire to submit `{ rule: 'fusion', wire }` for that wire.
2. Select exactly one wire and press `F` to submit the same step.

Both entrances use `ProofMoveController`'s existing commit path. The kernel
remains the sole authority for whether the submitted fusion step is valid.

## Scope boundary

This feature adds no context-menu item and changes none of the following:

- wire or node hover behavior;
- selection behavior;
- refusal presentation or wording;
- undo, redo, proof history, or timeline scrubbing;
- proof-step semantics;
- term-node double-click conversion;
- physics or motion;
- any other keyboard binding.

The implementation is confined to gesture-to-step dispatch and focused tests
of that dispatch.

## Ownership and branch order

The proof interaction is implemented and validated on a branch cut from
`main`, then merged to `main`. Only afterward is that main change integrated
into the game branch. No game-specific fusion gesture or command is permitted.

## Validation

Focused tests prove that wire double-click and selected-wire `F` each submit
exactly one `{ rule: 'fusion', wire }` step through the ordinary commit path.
They also pin that term-node double-click remains conversion, non-wire or
multi-item selection does not claim `F`, and no fusion context-menu action is
introduced. Type checking and the relevant non-physics application tests must
pass. Physics tests are not run because physics is untouched.
