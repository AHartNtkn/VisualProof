# Teacher Presentation Visual Gate

**Date:** 2026-07-18
**Branch:** `game/cursebreaker-domain`
**Status:** approved option-set design; production treatment remains unselected

## Outcome

Create a focused in-app review scene containing three high-fidelity teacher
presentation treatments. The scene must let the user compare the same authored
modal instruction and recognized-unwinnable commentary in each treatment at
desktop and compact sizes, with saved text-size and reduced-motion behavior.
It must not select a production treatment, style pause/settings or completion,
introduce a teacher identity, add character art, or invent lore.

The review scene is design evidence, not a competing game mode. After the user
selects one treatment, the selected presentation becomes the only production
teacher view and the review-only variant switch and rejected treatments are
deleted.

## Shared semantic contract

All three treatments consume the existing `CursebreakerPresentationProjection`
through one teacher presentation component. They render only existing authored
intervention text and the existing presentation intent:

- `modalInstruction` blocks proof, timeline, folio, and drawer input. It exposes
  one clear acknowledgement action and supports the controller's Escape
  precedence. Acknowledgement dispatches the existing
  `acknowledgeTeacher` action; merely closing through Escape follows the
  controller's existing close semantics.
- `nonblockingCommentary` never takes proof or timeline ownership. It remains
  visually associated with the timeline because its only current recovery is
  `timeline`, and it renders the authored explanation that identifies the
  recognized state and tells the player to rewind.
- `completionCommentary` is not styled in this gate. Its authored text remains
  data for the later completion-screen gate.

No treatment may add generic hints, timing, stalled-state detection, assistant
chat behavior, a portrait, a speaker name, a dialogue history, or alternate
instruction copy.

## Option A — Field Annotation (recommended)

The teacher appears as an archaeological annotation placed on the desk beside
the examination lens. Its material language is a dark, thin field card with
restrained paper grain, indigo-black ink, hairline registration marks, and a
small warm edge reflection derived with CSS rather than a new image asset.

For modal instruction, the card unfolds toward the center without covering the
entire lens. The proof remains visible through a quiet dark scrim so the words
can refer to geometry already on screen. The acknowledgement affordance is part
of the card's lower registration edge rather than a software-style button bar.

For nonblocking commentary, the card remains collapsed at the lower-right edge
of the lens, just above and to the right of the timeline. It never overlaps the
lever's interactive track. This option makes modal versus nonblocking ownership
most legible while staying compatible with the desk and folio materials.

## Option B — Lens Whisper

The teacher text is treated as an optical annotation within the lens assembly.
A narrow translucent band follows the inner gasket edge, with cool lettering
and a restrained radial falloff that echoes the proof palette without copying
proof geometry.

For modal instruction, the band widens into an inset circular reading field and
the rest of the proof dims. For nonblocking commentary, only a short arc and
compact text panel remain near the timeline side of the gasket. Decorative
edge shimmer stops under reduced motion and never distorts pointer mapping.

This option is the most diegetic and keeps the desk clear, but it has the
highest risk of competing with neon proof marks. The review scene must prove
that its text and optical edge remain visually distinct from legal-move and
selection colors.

## Option C — Desk Memorandum

The teacher appears as a translucent physical memorandum laid on the desk,
using a pale desaturated sheet, dark archival type, and a single clipped corner.
It is material but deliberately distinct from the excavation folio, so it
cannot be mistaken for an artifact record.

For modal instruction, the memorandum lifts and settles over the lower portion
of the lens while leaving the current proof visible above it. For nonblocking
commentary, it remains pinned outside the lens near the lever end. Reduced
motion replaces lift and settle with a short opacity/depth change.

This option has the strongest tactile presence and clearest text field. It also
consumes the most desk area and therefore requires the strongest compact-layout
proof.

## Review-scene ownership

A dedicated visual-gate entry selected by an explicit development/review query
mounts the real desk, lens, gasket, substrate, proof canvas, timeline, and
teacher presentation component. The gate owns only:

- the A/B/C review selector;
- switching between the real authored opening instruction and the real authored
  recognized-unwinnable commentary;
- viewport presets for desktop and compact comparison.

The review selector is visibly separated from the game composition and is not
compiled as an in-world control. It supplies a projection fixture to the same
presentation component used by production; it does not create another game
controller, save model, teacher trigger, or presentation authority. Production
startup continues to mount `CursebreakerRuntime` normally unless the explicit
visual-gate query is present.

## Responsive and accessibility behavior

- Interface text size scales the rendered teacher text and acknowledgement
  affordance without clipping at small, medium, or large settings.
- At compact widths, every option keeps the lens centered and the folio drawer
  edge usable. Modal text fits without horizontal scrolling; nonblocking text
  does not cover the timeline track or construction-loupe terminal.
- Modal instruction uses a semantic dialog with initial focus inside it, a
  visible focus treatment, one acknowledgement action, and restored focus on
  close. Nonblocking commentary uses a non-modal status/aside treatment and
  never moves focus.
- Full motion is restrained material or optical settling. Reduced motion
  removes travel and substitutes a short opacity/depth transition with no input
  delay. The saved game preference remains authoritative over OS media state.
- All text meets readable contrast against the actual desk, substrate, and
  proof colors. No option communicates modality or recovery by color alone.

## Failure and lifecycle behavior

If the projection has no teacher transient, the component renders nothing and
owns no focus or pointer surface. Unsupported teacher intent fails during
development rather than silently choosing a fallback treatment. Updating from
one intervention to another replaces the previous presentation atomically.
Disposal removes dialog/status nodes, listeners, focus ownership, and pending
decorative animation. Rejected variants leave no aliases, compatibility mode,
or production CSS after selection.

## Decisive validation

Focused unit and real-browser checks must prove:

1. all three variants render the exact authored opening and unwinnable text;
2. modal instruction blocks the lower game surfaces, acknowledges once, obeys
   Escape precedence, and restores focus;
3. nonblocking commentary does not move focus or block proof/timeline input;
4. no stalled, timed, generic-hint, portrait, speaker-name, dialogue-history,
   pause, or completion presentation appears;
5. desktop and compact geometry avoid the timeline track, folio handle, lens
   critical area, and loupe terminal;
6. saved reduced motion and all three text sizes change computed presentation,
   not just state attributes;
7. variant/intervention switching and disposal leave no stale nodes, listeners,
   focus traps, or animation work;
8. the ordinary production entry remains unchanged when the explicit review
   query is absent.

The user reviews the three treatments in the running app. Selection of A, B, or
C is the authoritative visual decision. No teacher production styling is final
before that selection.
