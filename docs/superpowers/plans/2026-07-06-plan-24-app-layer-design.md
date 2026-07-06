# Plan 24 — The app-scale layer, designed as one coherent spec

**Status**: DESIGN DOCUMENT for the user's ruling BEFORE implementation (mandate
2026-07-06, corpus `wire-physics-aesthetics-corpus.md`). No code changes here.
**Governing corpus**: `wire-physics-aesthetics-corpus.md` — every decision below is
checked against ALL of it, including the RESET RULING and the MANDATE.
**Prerequisite reading**: plan 22 (elastica promotion) and plan 23 (strict total
descent) "Decisions" sections — the negative knowledge this design must not relitigate.

The wire MODEL is settled and untouched: a wire leg is the massless
minimum-energy θ-quadratic of its live boundary data (`elastica.ts`, plan 22),
kinks/loops/wraps unrepresentable (tangent range ≤ π). The dynamics MODEL is
settled and untouched: ONE total energy, ONE mover — a strictly E-gated per-DOF
coordinate step (`relax.ts`, plan 23); the system does not change unless the
change lowers energy. This plan designs the layer that was never designed, only
accreted during promotions: the **frame**, the **boundary attachment**, the
**junction's identity over time**, the **motion policy** that couples them, and
the **transition** behavior. It is the layer the RESET RULING rejected wholesale.

The design has one organizing principle, taken directly from the reset ruling:
**the app scale adds a frame and fixed boundary targets, and NOTHING about that
frame or those targets may move the content except through contact and wires.**
Every defect the reset named is an instance of the frame or a boundary target
reaching into the content's motion. The fix is to make the frame and its slots
INERT anchors that content reacts to locally, never global operators that push
content around.

---

## Subsystem 1 — THE FRAME

### What it is and what determines it

The frame is the rounded rectangle that draws the statement boundary (the sheet
edge). Today it is `sheet.radius + FRAME_MARGIN`, where `sheet.radius` is the
minimal-enclosing-circle of ALL content, **recomputed every tick** (`frameBounds`
reads `e.regions.get(e.d.root)`). So it breathes with every body that moves — the
reset ruling's first named defect: "the rounded square shrinks to fit them. Insane."

**Design: the frame is fixed state, set by a discrete event, never a function of
per-tick motion.** The engine gains a stored frame `{ center, halfW, halfH }`. It
is established ONCE, when a diagram is first displayed (a seed or a rewrite — the
same discrete events that rebuild the engine), sized from the content's bounding
box AFTER the leading construction projection has made the seed legal, plus a
fixed margin. Between those events it is a constant. Settling, dragging, and free
relaxation never change it.

- **Why a box from the bounding box, not the enclosing circle + margin as now?**
  The content is not a disc; a circle-derived frame wastes the corners and forces
  the slots onto a perimeter whose size tracks a radius. A box sized to the actual
  content extent is tighter (corpus: "way too fucking spaced out" is rejected) and
  its four straight edges are where boundary slots naturally live.
- **What the frame must NEVER respond to**: the position of any individual body
  during motion; the centroid of the content; the settling process; a drag. These
  are exactly the couplings the reset banned. It responds ONLY to the discrete
  re-seed/rewrite event.
- **Position**: fixed in world space at establishment. It does not re-center on
  the content as the content settles (re-centering IS centroid coupling).

### Content staying inside a fixed frame

A fixed frame raises the question the current breathing frame dodged: what keeps
content in? Two mechanisms, both already required by the corpus and neither a new
hack:

1. **The extent limit** (corpus: "Diagram extent limited (~110% of starting
   size)"). This is currently UNIMPLEMENTED (grep confirms no extent term exists).
   It becomes a soft energy term: content bodies past a radius are pulled back, so
   free relaxation cannot inflate the layout past the frame it was sized to. This
   is content reacting to a field, not the frame chasing content.
2. **HARD SEMANTIC CONTAINMENT already clamps drags** (`clampDragToFeasible`), and
   the frame is sized to the settled content, so a drag that pushes a node toward
   the edge meets the extent field before the frame. If the user drags hard enough
   to genuinely need more room, the frame does NOT grow mid-drag (that is the
   banned behavior); the content is held by the extent field instead.

The frame is a fixed proscenium the content settles WITHIN, not a shrink-wrap.

### Camera consequence (a free win)

The camera today fits to `sheet.radius`, which breathes every frame, so the whole
view jitters even at rest. With a fixed frame, the camera fits to the FIXED frame
→ the viewport is rock-steady while content settles inside it. No separate fix
needed; it falls out of the frame being inert.

**DELETED**: `frameBounds`'s per-call derivation from the sheet circle; the
frame's dependence on `FRAME_MARGIN`-plus-radius. The camera's fit target changes
from the sheet circle to the stored frame.

---

## Subsystem 2 — THE BOUNDARY ATTACHMENT

### What exists at a boundary attachment

Today EVERY boundary wire — even one interior port going to one slot — is given a
junction body `e:<wid>` that is drawn as a visible dot, plus an EXTERIOR connector
running from that body OUTSIDE the frame to the slot. Two reset defects at once:
"there's an edge node for some reason" (the dot on a simple wire) and boundary
wires connecting to the outside of the frame.

**Design: a boundary slot is a FIXED ANCHOR POINT on the INSIDE of the frame — a
terminal, not a body.** It has a fixed position (on the inner edge of the frame
stroke) and a fixed arrival tangent (the inward frame normal). It behaves exactly
like a port anchor that happens to belong to the frame instead of a node. It
carries no disc, no dot, no DOF.

- **A simple boundary wire (one interior port + one slot)** is ONE elastica leg,
  from the node's rim (perpendicular exit by construction) to the slot (arriving
  along the inward normal). No hub, no junction body, no dot, no exterior
  connector. It is a single smooth curve that starts on the node and ends on the
  inside of the frame edge. This is the exact shape a simple port-to-port interior
  wire already has; the slot is just a fixed second endpoint.
- **A multi-endpoint boundary wire (k ≥ 2 interior ports that share one line of
  identity which also crosses the boundary)** is a genuine k-ary junction: the k
  port legs converge into a trunk, and the trunk's far end is the slot. Here a
  junction DOES exist because the wire genuinely branches — but it is the SAME
  junction structure as an interior branch (Subsystem 3), with one of its arms
  pinned to the fixed slot instead of a node. The trunk reaches the frame; the
  tributaries merge into it. No separate exit body, no exterior connector.

The distinction is structural and honest: a body appears at a boundary attachment
exactly when the wire actually branches there (k ≥ 2), never for a plain 2-point
wire. That is precisely what the reset demanded.

### Slot placement on the fixed frame

Slots are placed on the fixed frame perimeter in canonical boundary order,
clockwise from the pip at the top-edge midpoint, spaced by arc length (the current
`frameSlots` algorithm is correct and kept — but it now runs against the FIXED
frame, so slots are fixed, not chasing a breathing perimeter). Canonical order is
preserved and slots cannot slip past each other (corpus: lhs/rhs must stay
distinguishable) because their order is the boundary index, structurally.

**DELETED**: the `e:<wid>` exit-hub body for the simple case; `boundaryExits`'s
exterior hub→slot connector and frame tick; `exitAttractE` / `WIREP.exitPull` /
`boundaryExitE` (there is no exit hub to attract — the slot is a fixed leg
endpoint the elastica closes to directly, the same way it closes to a port); the
junction-dot draw for `e:` bodies in `paintWires`; the region-circle / projection
/ scope-ring exclusions that exist only to special-case `e:` bodies.

---

## Subsystem 3 — JUNCTION IDENTITY OVER TIME

This is the subsystem the reset was angriest about: "it doesn't look like the
branching stuff was ever implemented — everything is just going to a single point,"
and "the trunk-pair SWAP redraws legs on new trajectories" = snapping. Two distinct
failures: (A) the look is a spoke-hub, not a trunk with tributaries; (B) the
identity of the branch structure is re-derived from geometry each evaluation, so it
jumps.

### Failure A — why it reads as "a single point"

Today all k legs of a junction terminate at ONE hub point, each arriving along its
own `hubAngle`. Even with perfect trunk-alignment of the arrival ANGLES, every leg
still ends at the same coordinate, so it draws as k curves meeting at a dot — a
spoke hub. The corpus TRUNK-PAIR look is different in KIND: the two most-opposite
legs must form ONE continuous curve (antiparallel tangents, flowing straight
THROUGH the junction), and the side legs must merge into that curve TANGENTIALLY at
points DISTRIBUTED ALONG it — a river with tributaries, not spokes on a hub.

**Design: a junction is a TRUNK CURVE with tributary merge points spread along it,
not a point.** The junction owns:

- a **trunk**: one elastica curve whose two ends are the two trunk legs' ports, so
  it passes through the junction region as a single smooth line (antiparallel
  tangents at the middle — the "continuous trunk" look, by construction, because it
  IS one curve);
- for each remaining (tributary) leg, a **merge parameter** t ∈ (0,1) locating
  where along the trunk it joins, and the tributary leg is an elastica from its
  port to that point on the trunk, arriving TANGENT to the trunk there (a free-end
  well aligned to the trunk's local tangent).

The tributaries land at DIFFERENT points along the trunk, so the drawing is a
trunk with branches — never a single point. A 2-leg junction degenerates correctly
to just the trunk (one through-curve), which is why a simple interior wire and a
simple boundary wire need no junction body at all.

### Failure B — identity must be carried state, changed only continuously

The reset's "swap redraws legs on new trajectories" is the fatal one. The current
code picks trunk-vs-tributary roles implicitly from geometry every evaluation
(`trunkTarget` branches on `|phi − dir| ≤ π/2`, and which legs are "most opposite"
is re-read from positions). When bodies move enough that a different pair is most
opposite, the roles re-assign and every leg jumps to a new trajectory. **Any
argmax / nearest / most-opposite re-derivation per frame is banned by the no-
snapping law.**

**Design: the branch structure is PERSISTENT STATE, and it can only change by
continuous sliding, never by re-assignment.** Concretely:

- The junction stores its **trunk-end identities** (which two ports are the trunk)
  and each tributary's **merge parameter** as STATE, seeded once and carried across
  rebuilds by `carryOver` (by bind signature, as DOF already are).
- These evolve by the SAME strictly-gated descent as every other DOF: the merge
  parameters are DOF; the trunk axis is a DOF with inertia (travel-capped, so it
  cannot flip frame-to-frame).
- A genuine trunk-pair swap (geometry evolves so a tributary is now more in-line
  than a trunk end) happens as a CONTINUOUS event: the tributary's merge parameter
  slides to the trunk END (t → 1), the two curves become tangent there, and the
  roles exchange THROUGH that tangency — the picture passes smoothly through the
  configuration where three legs are momentarily colinear, and no curve is ever
  redrawn on a discontinuous new path. This is the identity-preserving blend the
  mandate asked for, made precise: identity lives in state, and the state only ever
  slides.

The guarantee is structural: because there is no per-frame role re-derivation and
every governing quantity is a gated DOF or an inertial axis, a discontinuous jump
is impossible by the same theorem that makes limit cycles impossible (plan 23) — a
move happens only if it lowers energy and only within the per-visit travel cap.

**DELETED / REPLACED**: the single-hub-point model (`WireHub` as a point all legs
share); `trunkTarget`'s discrete `axisSide` branch and the per-leg-angle-to-a-
shared-point scheme; `trunkAlignE` in its current spoke form. Replaced by the
trunk-curve + merge-parameter model above. `phi` (trunk axis, inertial DOF) and
the nematic anchoring survive in spirit as the trunk axis, but drive a trunk CURVE,
not a spoke fan.

---

## Subsystem 4 — MOTION POLICY

### No centering / centroid coupling of any kind

The reset: "moves purely based on the position of other things rather than actually
coming into contact — action at a distance is banned; only contact/wire-mediated
interaction." The offender is `globalRotationDof`: it rotates ALL content rigidly
about the CONTENT CENTROID to face boundary ports at their slots. That is a global
operator keyed on a computed centroid — the definition of action at a distance.

**Design: delete `globalRotationDof` entirely. Port-to-slot alignment happens
through each node's OWN rotation DOF responding to its OWN boundary leg's tension.**
A boundary leg pulls its node's port to face the slot exactly as any wire's arrival
well torques its node; this is wire-mediated and local — allowed. There is no
global rotation, no centroid, no rigid whole-scene spin. Every interaction in the
system is now local: a node moves because another body contacts it (the sibling
barrier) or its wire pulls it (leg tension / arrival well); nothing moves because
of where a distant thing is.

This is strictly more principled than the status quo AND removes the plan-22/23
fork that `globalRotationDof` created (it fixed some scenes and regressed others —
plan 22 "OPEN — scene-dependent trade"). The trade dies with the mechanism.

**Consequence to verify**: plan 22 found pure per-node rotation "stalls at +76°"
on the wrench ridge and needed the long-shot ladder to cross it. The per-node
rotation gate ALREADY has that ladder (`gatedStep`'s long-shot + expanding search),
so a single node CAN turn to face its slot without the global spin — this must be
re-measured on the framed scenes, not assumed. (Flagged, not hand-waved.)

### Fast settling WITH smooth animation — no global slowdown cap

The reset: edges settle at a "snail's pace"; the global `FRAME_CAP` slowdown was a
hack; "smoothness must come from small frequent updates, not slow motion." The
corpus sharpens it: the sliced/anytime descent that updates each DOF ~once per
second "reads as hard clicking between configurations; smooth animation requires
small frequent steps on ALL DOF per frame, not full-size steps at ring frequency."

Two distinct current mechanisms are BOTH wrong for this:

1. **Time-slicing one region of the DOF worklist per frame** (`descentCursor`,
   `settleStepBudget` deadline): a given DOF is visited once per full sweep, ~1s
   apart, so it lurches. This is the "hard clicking" the corpus named.
2. **`FRAME_CAP` capping every DOF's per-visit magnitude**: slows all motion
   globally to hide the lurch — the snail's-pace hack.

**Design: every frame runs a FULL sweep of SMALL gated steps over ALL DOF.** Each
DOF is touched every frame and moves a little (a bounded gated micro-step), so the
whole diagram eases toward rest together and smoothly. Smoothness comes from
frequency (all DOF, every frame), not from a magnitude cap; speed comes from every
DOF making progress every frame rather than once per second.

**DELETED**: `FRAME_CAP`; `descentCursor` and the sweep-slicing in `descentSweep` /
`settleStepBudget`; the whole "resume a sliced sweep across frames" apparatus.

**The load-bearing constraint this creates (honestly flagged)**: plan 23 measured
a full sweep at ~250–450 ms on a 16–32-node framed scene. A full sweep per frame
at 60 fps needs it near ~16 ms. This design REQUIRES the per-sweep cost to drop by
~15–25×, and the only principled place that cost lives is the energy evaluation
inside each gated step (dominated by the grid leg solve). This design does NOT
authorize a magnitude cap or slicing to fake smoothness; it requires the sweep to
become cheap enough to run whole. Whether that is reachable (cheaper localized
energy, fewer evals per gated step, coarser paint-vs-solve resolution split) is the
principal implementation risk and is called out in Open Questions — I am NOT
inventing the specific speedup, per the "never take algorithmic advice" law; I am
fixing the DESIGN (all DOF, every frame, no cap) and flagging that its feasibility
rests on evaluation cost.

### The blind-cone / near-circle wrap, designed away

The reset: "near-complete-circle edges wrapping the whole diagram (blind-cone
fallback arcs at app scale) are unacceptable and never appeared in the accepted
demos." A leg whose target sits in the ~84° cone directly behind its port needs a
> π turn, which the elastica family cannot represent, so `solveLeg` falls back to a
near-2π arc that wraps the diagram. At app scale the fixed slots create geometry
where a boundary port faces away from its slot, triggering it.

**Design: the wrap is eliminated at rest by free local rotation, and prevented
during transients by making rotation the cheap escape, not elongation.**

- **At rest**: with `globalRotationDof` gone and each node free to rotate via its
  own wire-driven torque, a boundary node turns its port to face its slot by the
  shortest path. At rest no port faces > π away from its wire's destination, so the
  blind cone is unoccupied and no wrap is drawn. (The frame is what makes this
  well-posed: the slot is a fixed target, so "face the slot" is a definite,
  reachable orientation.)
- **During a transient** (a fresh scene or a large drag, before rotation catches
  up): the energy must make ROTATING THE NODE to face the target overwhelmingly
  cheaper than GROWING the wire into the cone, so the node swings to face its
  destination within a few frames and the wire stays a short curve at the port the
  whole time. The wire when a port momentarily faces away is a stubby curve that
  rapidly shortens and swings around as the node turns — never a diagram-wrapping
  arc. This is NOT the rejected length-cap (which flattens the gradient and lets
  the leg REST in the cone — plan 22's dead-zone failure); the leg keeps its true
  steep repulsive fallback energy, but the node's rotation DOF has a stronger, gated
  path out, so the cone is exited by TURNING, not by the wire settling long.

The visible promise: you never see a wire wrap around the diagram, at rest or in
motion. If a port is briefly mis-facing, you see the NODE turn, not the WIRE loop.

---

## Subsystem 5 — TRANSITIONS

Corpus: "Rewrite transitions must seed new wires near their ports (no wild random
spawns), and the whole transition should morph continuously"; and the reset's
workflow note that app-scale layout must be coherent, not patched.

**Design: a diagram change (rewrite / proof step / replay step) is a discrete
event that establishes new fixed state, and everything the user watches morphs
continuously from the old state to the new.**

- **Surviving content glides**: `carryOver` keeps every surviving body's position
  and every surviving wire's DOF (now including the junction's trunk identities and
  merge parameters) by signature — already the discipline, extended to the new
  junction state.
- **New content seeds near its ports**: new bodies seed adjacent to their wire
  anchors (already done in `mkEngine`, `mkWireBody(near)`), never on the global
  spiral — no wild spawns.
- **The frame morphs, it does not snap**: the new frame is sized from the new
  content, but the DRAWN frame eases from the old dimensions/center to the new ones
  over the settle (a continuous interpolation of the stored frame state), so a
  rewrite does not pop the boundary box to a new size. Slots ride the morphing
  frame, so boundary attachments glide too.
- **The construction projection runs once** (discrete), off-screen before the first
  drawn frame of the new scene, to make the seed legal (plan 23's leading
  projection — load-bearing, kept). The user never sees the illegal seed or its
  projection; they see the legal start ease toward rest.

The whole transition: old content glides to its new home, new content grows in at
its ports, the frame eases to its new shape, all under the one strict descent — no
snap anywhere.

---

## WHAT YOU WILL SEE — the list for your ruling

1. **The frame (rounded boundary box) holds completely still while the diagram
   settles inside it.** It never shrinks, grows, or shifts in response to the
   pieces moving.
2. **The camera / viewport is steady** — no more background jitter while a scene
   relaxes, because the view fits the fixed frame, not the breathing content.
3. **The frame is a tight rounded rectangle sized to the content** (not a big
   circle-derived box), re-sized only when the diagram itself changes.
4. **A simple boundary wire is a single smooth curve from the node to the inside of
   the frame edge, with NOTHING at the frame end** — no dot, no little edge node,
   no line poking outside the frame.
5. **Boundary wires connect on the INSIDE of the frame**, meeting the edge
   perpendicular; nothing is ever drawn outside the frame.
6. **A dot appears at a boundary attachment ONLY when the wire genuinely branches
   there** (three or more things sharing one line that also exits) — never on a
   plain two-point wire.
7. **A branching wire looks like a river with tributaries**: two arms form one
   continuous line flowing straight through, and side arms merge into it smoothly at
   different points along it — NOT a bundle of lines all meeting at one dot.
8. **When a branch reorganizes, it morphs** — a side branch slides along the trunk
   and the shape flows through the change; branches never jump to a new position or
   get redrawn on a different path.
9. **Nothing moves "by itself at a distance."** Rotating or dragging one node never
   counter-moves another node that it isn't touching or wired to; things interact
   only by touching or by the wires between them.
10. **The whole diagram eases toward rest together and quickly** — every part
    inching a little every frame — instead of one part clicking to a new spot, then
    another, in slow lurches.
11. **You never see a wire loop around the diagram.** If a node's connection point
    is briefly pointing the wrong way, you see the NODE turn to face its wire, while
    the wire stays short — you never see the wire grow a big arc to reach around.
12. **On a rewrite / proof step, the picture morphs continuously**: the parts that
    survive glide to their new spots, new parts grow in right at their connection
    points, and the frame eases smoothly to its new size — no popping or snapping
    anywhere in the transition.
13. **A dragged node stays inside its own region and never crosses into a cut it
    isn't part of**, even for an instant, and the frame does not grow to chase it.

---

## OPEN QUESTIONS for the user

These are the few places the corpus is silent and the choice is visibly
consequential. I am not guessing them into the design.

- **A. Frame shape and proportions.** The corpus fixes "rounded square/rectangle"
  and "tight, not spaced out," but not the aspect ratio or margin. Should the frame
  hug the content's actual bounding box (so a wide proof gets a wide frame), or be
  a more regular near-square regardless of content shape? (Affects items 1, 3.)
- **B. Where a branch's trunk points.** For a three-or-more-way branch, the two
  "trunk" arms are the most in-line pair, but when several are near-equally in-line
  the initial choice is a visible aesthetic call. Do you have a preference for how
  the trunk orients when the branch is nearly symmetric (e.g., align to the longest
  arm, or to the boundary/slot direction if one arm is a boundary exit), or is any
  smooth choice acceptable so long as it never snaps thereafter? (Affects items 7, 8.)
- **C. Transient rotation you may briefly see.** Designing the wrap away means, on a
  fresh scene or a big drag, you may briefly watch a node SPIN to face its
  connection before the wire straightens. Is a visible short spin acceptable as the
  honest cost of never wrapping, or should the initial seed pre-orient ports so even
  that brief spin is rare? (Affects items 10, 11.)
- **D. What a hard drag against the frame does.** With a fixed frame and the extent
  limit, dragging a node hard toward the edge is resisted by the extent field rather
  than the frame growing. Should the node feel a soft wall as it nears the edge
  (held in), or should the frame be allowed to grow on a DELIBERATE drag (a discrete
  user action, not motion) while still never breathing during settling? (Affects
  items 1, 13.)
