# Approved Presentation Reconstruction

## Outcome

Cursebreaker production renders the approved excavation-folio composition rather
than a visual reinterpretation. The approved folio scale, physical layers,
two-column record density, full-height central lens, dark substrate, Dark (Slate)
neon proof marks, and authored motion all survive. Real game state replaces only
the review demo's simulated progression and keyboard controls.

## Authority

Commit `c556eaed2b6f574436519e1d266c3a349c58ef2b` is the recoverable presentation
reference. These parts are promoted into production ownership:

- the workspace and full-height lens geometry from `base.css`;
- the physical folio DOM and layout from `main.ts` and `folio.css`;
- all five motion channels and their CSS timelines from `motion.ts` and
  `motion.css`;
- interruption completion ownership from `ownership.ts`; and
- the approved PNG pixels actually consumed by those layers.

The review `model.ts`, progression shortcuts, capture-only state, and standalone
review entry point are not promoted. No runtime path imports from `review/`.

## Workspace geometry

At non-compact widths, the lens diameter is exactly the viewport height. Its
center is `max(50vw, 100vw - 50vh)`. The aperture uses the approved asymmetric
inset `7.57% 13.62% 19.65%`, and the substrate extends eight percent beyond that
aperture before deterministic crop, restrained tint, rotation, and scale are
applied. The folio workspace ends at the lesser of the lens aperture's left edge
and the timeline's left edge. The folio never causes the lens to shrink or become
recentered in a residual column.

At compact widths, the same folio retracts into the left drawer and the lens uses
the largest viewport-height-bounded square that remains usable. Entering compact
mode closes the drawer; leaving it restores the open folio. The compact exception
does not alter desktop geometry.

## Folio structure and real-state boundary

One production folio root owns:

- lower board;
- culture dossier underlays;
- guard leaf;
- one active dossier;
- physical culture tabs;
- one continuous scrolling sheet containing the stable catalog records;
- folio cover and usable spine;
- record lift/return stage; and
- restricted-packet guard, tie, and fastener layers.

The real `FolioProjection` supplies cultures, stable record order, saved scroll,
status, and affordance. It also identifies a newly released restricted packet.
Archive clicks retain their real game behavior. During puzzles, completed records
remain theorem sources and follow the pointer; return motion remounts the record
after success or refusal. Locked records use the approved resistance treatment.

The cover is a presentation-owned physical interface. A newly mounted archive
opens it using the approved cover timeline; the visible spine can close and reopen
it without changing logical game state. Puzzle restoration mounts it open so the
active proof is immediately usable.

## Motion ownership

One `FolioMotion` instance owns `cover`, `dossier`, `record`, `restriction`, and
`packet` channels. Each active channel has exactly one class, target, kind, and
duration descriptor. Replacing a channel captures the currently painted pose for
cover and record motion, cancels the old owner, and gives cleanup authority only
to the replacement. Full durations remain 380, 260, 340, 320, and 480 ms.

Reduced motion runs one 90 ms non-spatial depth treatment for every channel. It
does not disable lifecycle ownership. Disposal settles all channels and removes
every transient descriptor.

## Proof presentation

The proof canvas remains transparent so the approved substrate is visible. Game
proof painting uses the existing Dark (Slate) theme: cyan glowing wires, dark
disc/paper fills, light labels, and dark negative wells. Production must not expose
the Light (Manuscript) theme or paint an opaque light canvas. Tests inspect painted
pixels and computed theme colors; importing a constant named `DARK` is not proof.

## Assets

Restore the approved `guard-leaf.png`, `mount-rubbing.png`,
`mount-tracing.png`, and `priority-band.png` blobs from the reference commit.
Register them as production assets with semantic dimension, alpha, geometry, and
runtime-consumption validation. Preserve all other approved production PNG bytes.
Do not restore review screenshots, Blender scenes, generators, manifests, demo
entry points, or exact-byte reproduction authority.

## Validation

Production browser tests are the presentation authority. At 1600x1000 they compare
the lens, aperture, folio, active dossier, tabs, and six visible records against
reference geometry with explicit tolerances. At 1920x1080 and wider viewports they
prove the lens remains one viewport-height square and the folio does not displace
it. Compact tests prove drawer retraction and lens usability.

Motion tests sample browser-computed frames for all five channels, prove multiple
distinct painted states, current-pose interruption continuity, and newest-owner
cleanup. Runtime tests retain archive selection, scrolling, puzzle theorem drops,
refusal, reduced motion, and controller persistence. A puzzle render test probes
the actual canvas for the dark field and luminous cyan proof marks.

Completion requires focused unit and browser tests, semantic asset validation,
TypeScript validation, desktop build, and a real Electron smoke run. The dedicated
physics battery remains disabled because proof physics is unchanged.
