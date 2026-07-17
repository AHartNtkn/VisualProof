# Continuous Folio Motion Design

## Purpose

The excavation folio must behave as one coherent physical interface. The open
cover must close through its visible edge, culture changes must read as rigid
paper replacement, record inspection must expand smoothly without intermediate
rests, and every graphic must be contained by the physical object that owns it.

This replaces the folio's multi-phase animation system. It does not add controls,
change puzzle behavior, alter the central lens, or modify physics.

## Controlling Runtime Evidence

Served Chromium measurements established the following causes:

- The visible open-cover edge occupies roughly 49 pixels, but only a 21.6-pixel
  internal strip accepts the closing click.
- Record entry is four independently eased 135 ms transitions. Its first phase
  explicitly disables transition and remains stationary, and later phase
  boundaries repeatedly approach zero velocity.
- Culture replacement is four independently eased 145 ms transitions. The
  outgoing sheet changes direction, a tab rotates, and an underlay scales.
- The released Myratic guard remains 13.1 pixels inside its record at 82% opacity;
  its tie also remains visible.
- The record itself uses `overflow: hidden`, so a status tab intended to protrude
  past the paper edge is cut off.

The problem is therefore responsibility and representation, not insufficient
animation tuning.

## Physical Motion Contract

Every folio action has:

1. one physical subject;
2. one interaction authority;
3. one uninterrupted timeline;
4. one completion owner; and
5. one settled rendering owner.

JavaScript owns lifecycle only: start, cancellation, duration, and cleanup. CSS
owns the visual trajectory. An action cannot be represented as a sequence of
named semantic phases or independently eased transitions.

Each active channel exposes:

- an `is-motion-<channel>` class;
- `data-motion-<channel>-target` when the channel has a semantic target;
- `data-motion-<channel>-kind` when the channel has directional variants; and
- `--motion-<channel>-duration`, written from the same duration used by the
  coordinator's completion clock.

No `data-<channel>-phase` attributes, phase arrays, phase duration loops, or phase
selectors remain.

Full motion uses one timeline. Reduced motion uses one 90 ms non-spatial emphasis
timeline. Paused motion commits the settled semantic state without transient
classes or timers. Replacing or resetting an active channel aborts its previous
completion owner and leaves cleanup authority with the newest motion.

## Channel Behavior

### Cover

The existing `data-cover-control` button remains the sole interaction authority.
Its transformed `.cover-surface` remains visual-only. When closed, the whole cover
button opens it. When open, the descendant spine hit region covers the complete
visible physical edge rather than a narrow internal strip; clicks still bubble to
the same button handler.

Opening and closing each use one transform animation between the exact closed and
open poses. The trajectory never approaches an edge-on projection. The fixed spine
remains visible while closing until the cover surface occupies the same region.

Target full-motion duration: 380 ms.

### Culture dossier

The outgoing sheet clone retains the prior culture and remains stationary beneath
the incoming sheet. The active incoming dossier begins slightly displaced to the
right and above the settled position with a lifted shadow, then translates directly
to the settled position.

The sheet and everything printed or attached to it are one rigid body. No scale,
skew, perspective depth, direction reversal, tab-specific rotation, underlay
compression, or outgoing-sheet deformation is permitted.

Target full-motion duration: 260 ms.

### Record inspection and return

Existing source geometry and physical-status capture remain authoritative. Before
entry begins, the inspection projection is synchronously staged at the clicked
record's exact pose and the mounted source is hidden. A single animation then
interpolates translation, two-axis scale, rotation, shadow, and filter to the
inspection pose.

Return performs the inverse continuous trajectory using the retained source
geometry and retained status. The mounted record becomes visible only when the
moving projection relinquishes ownership. Superseded return cleanup remains
generation-safe.

There is no stationary release interval, lift phase, travel phase, or settle
phase. Consecutive rendered frames must make progress toward the destination for
the active spatial portion of the timeline, with no intermediate velocity collapse.

Target full-motion duration: 340 ms for entry and return.

### Restricted-record refusal

The sleeve pull, resistance, and rebound are synchronized keyframes in one
timeline. Direction reversal is allowed because it communicates physical
resistance, but there are no independent transition rests or semantic phase
changes. The record and sleeve return to their exact settled poses when complete.

Target full-motion duration: 320 ms.

### Myratic packet release

Fastener, tie, sleeve, and contents use synchronized keyframes in one timeline.
The settled available record contains no visible guard, tie, or fastener residue.
Paused motion immediately produces that settled released state. Reduced motion
uses only the shared non-spatial emphasis before cleanup.

Target full-motion duration: 480 ms.

## Clipping and Layer Ownership

The record button permits overflow so status markers that physically protrude can
remain visible. Internal clipping is assigned narrowly:

- `.record-face` contains record-face graphics;
- `.evidence-mount` contains specimen imagery;
- `.record-guard` contains its sleeve and fastening graphics; and
- the dossier sheet contains its printed records.

Available tabs and gateway/clearance bands remain owned by the record and may
extend beyond its paper edge. They cannot be clipped by the record button.

A released Myratic guard may travel outside the record during its release
animation because it is the physical moving subject. At settled completion it and
its fastening are fully transparent and non-interactive; no cropped remnant may
remain at either edge.

## State and Data Flow

1. The action dispatcher captures any required source geometry and physical status.
2. The state transition commits the semantic target.
3. `syncView` renders the target and any retained transient owner.
4. The motion coordinator cancels the channel's prior owner, writes its one
   timeline descriptor and duration, and starts one completion wait.
5. CSS animates from the physical source pose to the semantic settled pose.
6. The current completion owner removes transient descriptor data and invokes
   generation-checked projection cleanup.

Changing reduced/paused preference during an active full animation does not
restart, jump, or remove the current timeline. The new preference applies to the
next action. Reset cancels every channel and projects the reset state.

## Validation

Unit validation proves coordinator representation and ownership:

- each full or reduced action schedules exactly one wait;
- no phase dataset is created;
- motion kind, target, duration, and class are installed and removed once;
- paused actions schedule no wait;
- replacement and reset preserve newest-owner cleanup semantics.

Served-browser validation proves behavior directly:

- real clicks across the complete visible open spine close the cover;
- record entry and return begin at exact source/destination geometry;
- consecutive active frames progress monotonically without stationary intervals
  or intermediate velocity collapses;
- culture sheets use translation-only transforms and never reverse direction;
- outgoing and incoming sheets retain correct stacking and rigid contents;
- reduced and paused motion preserve lifecycle ownership;
- released Myratic guard, tie, and fastener have no settled visible pixels;
- available tabs protrude without clipping;
- face, mount, and guard contents remain contained;
- responsive 1600, 1920, 2560, and 3440 pixel layouts remain valid; and
- TypeScript, production build, canonical screenshots, and motion trace pass.

The evidence trace records timeline start, representative rendered frames, and
settled completion. It does not record obsolete semantic phases.

Physics tests remain disabled because no physics behavior changes.

## Scope Boundaries

This reconstruction changes only excavation-folio motion, hit ownership, clipping,
its tests, and its generated runtime evidence. It does not redesign folio assets,
invent new controls, change level selection semantics, alter the lens, modify
feedback behavior, or touch proof-diagram physics.
