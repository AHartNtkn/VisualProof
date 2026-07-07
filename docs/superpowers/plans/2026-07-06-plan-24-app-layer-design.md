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

**Design: the frame is fixed ABSOLUTE state, set by a discrete event, never a
function of per-tick motion** (USER RULING 2026-07-06, Q-A: "Sizes are absolute:
computed at spawn from contents, never grow/shrink from motion, recalculated only
at a rewrite. Boundary is a hard edge"). The engine gains a stored frame
`{ center, half }`. It is established ONCE, when a diagram is first displayed (a
spawn/seed or a rewrite — the same discrete events that rebuild the engine), sized
from the content's extent AFTER the leading construction projection has made the
seed legal, plus a fixed margin. Between those events it is a CONSTANT. Settling,
dragging, and free relaxation never change it — a resize is triggered ONLY by a
rewrite, never by motion.

- **Near-square** (USER RULING Q-A). The frame is a near-square rounded rectangle
  — the proof's FOOTPRINT, with all four boundaries on equal footing — not an
  aspect-ratio hug of the content's bounding box. Sized so the settled content
  fits (side = the larger content half-extent + margin, applied to both axes), so
  a wide proof gets a bigger square, never a wide letterbox. Tighter than the
  current circle-derived box (corpus: "way too fucking spaced out" is rejected),
  and its four equal straight edges are where boundary slots evenly live.
- **What the frame must NEVER respond to**: the position of any individual body
  during motion; the centroid of the content; the settling process; a drag. These
  are exactly the couplings the reset banned. It responds ONLY to the discrete
  spawn/rewrite event.
- **Position**: fixed in world space at establishment. It does not re-center on
  the content as the content settles (re-centering IS centroid coupling).

### Content staying inside a fixed frame — the frame is a HARD EDGE

A fixed frame raises the question the current breathing frame dodged: what keeps
content in? USER RULING Q-A/Q-D: **the boundary is a HARD EDGE with no
motion-triggered resize.** So containment is a hard legality constraint, exactly
like HARD SEMANTIC CONTAINMENT (a cut a node isn't in), not a soft preference:

1. **The frame edge is a hard wall on content bodies.** A content disc may not
   cross the inner frame edge — during settling (a gated trial that would put a
   disc past the edge is projected back, so it is never accepted) and during a drag
   (`clampDragToFeasible` gains the frame edge as one more surface the cursor
   target is projected onto, alongside the non-member region circles). This
   supersedes the corpus's older SOFT "~110% extent limit" idea: the ruling is a
   hard edge, so the wall is a projection, not a field.
2. **A drag against the edge does NOT grow the frame.** The frame resizes only at a
   rewrite (Q-A); a drag is motion, so the node meets the wall and stops — the
   frame never grows mid-drag (the banned behavior). Item 13's "the frame does not
   grow to chase it" is this ruling.

The frame is a fixed proscenium with hard walls the content lives WITHIN, not a
shrink-wrap and not a soft tether.

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
  identity which also crosses the boundary)** is a genuine k-ary junction with one
  arm pinned to the fixed slot instead of a node. It is the SAME junction structure
  as an interior branch (Subsystem 3): where the geometry gives a trunk, one arm of
  that trunk reaches the frame and the others merge into it; where it does not
  (a near-symmetric junction, Q-B), the legs simply meet and one continues to the
  slot — no trunk is forced. No separate exit body, no exterior connector.

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

**A trunk is EMERGENT, never enforced** (USER RULING 2026-07-06, Q-B: "trunks need
not exist; near-symmetric junctions may have no trunk; never enforce one — the
tributary reading emerges only where geometry gives it"). The trunk-pair look is
what the geometry PRODUCES when two legs happen to be near-antiparallel; it is not
a structure the junction is forced into. Mechanically this means the "trunk" is not
a distinguished stored pair at all — there is a single continuous quantity (the
trunk axis with its alignment weight `|cos(dir−axis)|`) that is STRONG only when a
near-in-line pair exists and FADES SMOOTHLY TO ZERO as the junction approaches
symmetry. At a symmetric junction (e.g. three legs at 120°) the weight is small for
every leg, no pair reads as a through-trunk, and the legs simply meet — which is
CORRECT here, because there is no trunk to see. The design must never contain a
step that picks a mandatory trunk pair; the through-line appears only as the
continuous consequence of two legs being aligned, and dissolves continuously when
they aren't. (This also guarantees Failure B's no-swap property in the symmetric
case: with no distinguished pair, there is nothing to swap.)

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

- The carried STATE is CONTINUOUS, never a discrete pair (per Q-B — there is no
  stored "which two are the trunk"): the junction stores its **trunk axis** (one
  angle, an inertial DOF) and each leg's **merge parameter** t (where along the
  through-line it joins). Both are seeded once and carried across rebuilds by
  `carryOver` (by bind signature, as DOF already are). Which legs "are the trunk"
  is never recorded — it is only ever the continuous readout `|cos(dir−axis)|` of
  the axis against each leg, which is exactly why it can fade to nothing at a
  symmetric junction.
- These evolve by the SAME strictly-gated descent as every other DOF: the merge
  parameters are DOF; the trunk axis is a DOF with inertia (travel-capped, so it
  cannot flip frame-to-frame).
- A genuine role change (geometry evolves so a different leg becomes the most
  in-line) happens as a CONTINUOUS event: the axis rotates slowly (inertial) and
  each leg's merge parameter slides, so a leg transitions trunk→tributary by its
  alignment weight fading through zero and its merge point sliding along the
  through-line — the picture passes smoothly through the momentary configuration,
  and no curve is ever redrawn on a discontinuous new path. This is the
  identity-preserving blend the mandate asked for, made precise: identity lives in
  continuous state, and the state only ever slides.

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

### Node rotation is FREE and UNLIMITED (USER RULING 2026-07-06)

Verbatim: **"Node angle is ARBITRARY. It encodes NO information and is FREE in the
physics."** This resolves a wrong assumption baked into the earlier draft (and into
the current code): that node rotation, like every DOF, should be smoothed by a
per-frame rate bound. It should NOT. **The no-snapping law governs WIRE SHAPES,
never node angles.** A node carries no orientation meaning (ports are found by the
pip, not by absolute angle — corpus: port names/order are not orientation), so a
node may spin as fast as the energy dictates, including whipping around most of a
turn in a single frame to shed wire tension. This is DESIRED behavior the user
complains about when it is MISSING (a node that should rotate to relieve a twisted
wire but instead sits stuck).

**Design consequence**: the node-rotation DOF has NO rate cap of any kind — not
`FRAME_CAP`, not the `rotCap(0.28, ·)` per-tick bound, not the small-step-per-frame
policy below. It descends its wire energy by the full gated step (long-shot ladder
+ expanding search) every frame, uncapped. The small-step smoothness policy applies
to LAYOUT DOF (body TRANSLATION, hub/tip positions, merge parameters, trunk axis) —
the things whose fast motion would read as the layout jumping — and explicitly NOT
to node angle, which is free to move as far as it wants. (The `~0.3 rad/frame`
class of bounds was the wrong assumption; it is deleted, not tuned.)

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

**Design: every frame runs a FULL sweep over ALL DOF; the LAYOUT DOF take small
gated steps, node angle is uncapped.** Every DOF is touched every frame so the
whole diagram eases toward rest together — but "small step" bounds only the layout
DOF (translation, hub/tip positions, merge parameters, trunk axis), whose fast
motion would read as the layout jumping. Node rotation is exempt and free (previous
subsection). Smoothness of the LAYOUT comes from frequency (all layout DOF, every
frame), not from a global magnitude cap; speed comes from every DOF making progress
every frame rather than once per second.

**DELETED**: `FRAME_CAP` (both the layout slowdown and its rotation cap);
`rotCap`'s per-tick 0.28 rotation bound; `descentCursor` and the sweep-slicing in
`descentSweep` / `settleStepBudget`; the whole "resume a sliced sweep across
frames" apparatus.

**The load-bearing constraint this creates (honestly flagged)**: plan 23 measured
a full sweep at ~250–450 ms on a 16–32-node framed scene. A full sweep per frame
at 60 fps needs it near ~16 ms. This design REQUIRES the per-sweep cost to drop by
~15–25×, and the only principled place that cost lives is the energy evaluation
inside each gated step (dominated by the grid leg solve). This design does NOT
authorize a magnitude cap or slicing to fake smoothness; it requires the sweep to
become cheap enough to run whole. Whether that is reachable (cheaper localized
energy, fewer evals per gated step, coarser paint-vs-solve resolution split) is the
principal implementation risk and is the whole of Task 6 in the implementation plan
below — I am NOT inventing the specific speedup, per the "never take algorithmic
advice" law; I am
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

> **USER RULING 2026-07-06 (SUPERSEDES the "recalculated at rewrite" wording
> below):** the border NEVER varies in size, EVER — one fixed frame size for the
> diagram's lifetime; rewrites do NOT resize it; CONTENTS adapt/reflow within the
> fixed border. Verbatim: "there's no benefit — it just creates ambiguity over
> what needs to change whenever things need to be resized." If a rewrite genuinely
> cannot fit inside the fixed border, that is a FORK to report, never a silent
> resize. Items 1/3/12 below are updated to this ruling; the region circles (CUTS)
> are held inside the border by the same hard wall as the discs (bug fixed).
>
> **Sizing (option a, team-lead-approved 2026-07-06):** a REPLAY's border is sized
> ONCE from the PROOF-WIDE MAX content extent — a replay's contents are ALL its
> steps, known at spawn, so one absolute size fits every step and never varies.
> Rationale (vs the alternatives): (b) size-to-final breaks growing proofs (a
> mid-proof step overflows); (c) rescale-to-fit would vary visible node sizes
> mid-proof, contradicting the absolute-node-size law. Each step's extent is measured
> on its CONSTRUCTION-PROJECTED seed (mkEngine → resolveOverlaps), not a full settle:
> the whole-proof scan is then ~150 ms (measured, plusComm 65 steps), and the
> projected extent SAFELY over-bounds the settled extent at the binding (largest)
> steps because settling COMPACTS them (measured plusComm step 42: proj 402.8 →
> settled 340.5); the only steps whose settled extent exceeds their projection are
> tiny ones far below the max, so max-proj-extent fits every step's RESTING content.
> `establishProofFrame` (relax.ts) does the scan; the shell's `enterReplay` calls it
> once; `carryOver` propagates the same frame to every step (byte-identical, tested).
> KNOWN transient: right after a rewrite the CARRIED+projected seed can spread past
> the border (measured ~58 wu at plusComm step 42) before settling compacts it in;
> `clampContentToFrame` pulls the seed's discs inside at construction and the cut
> barrier + wall contain the rest as it settles — a post-rewrite settling artifact,
> not a persistent violation (the resting state fits, verified).

1. **The frame (rounded boundary box) holds completely still — for the whole
   lifetime of the diagram.** It never shrinks, grows, or shifts — not while the
   pieces move, and not at a rewrite. Content settles and reflows INSIDE it.
2. **The camera / viewport is steady** — no more background jitter while a scene
   relaxes, because the view fits the fixed frame, not the breathing content.
3. **The frame is a tight, near-SQUARE rounded box** (not a big circle-derived box,
   not a wide letterbox), at an ABSOLUTE size fixed ONCE for the diagram's lifetime —
   never from motion AND never from a rewrite (USER RULING 2026-07-06). The CUTS
   (region circles) are held fully inside it by the same hard wall as the discs.
4. **A simple boundary wire is a single smooth curve from the node to the inside of
   the frame edge, with NOTHING at the frame end** — no dot, no little edge node,
   no line poking outside the frame.
5. **Boundary wires connect on the INSIDE of the frame**, meeting the edge
   perpendicular; nothing is ever drawn outside the frame.
6. **A dot appears at a boundary attachment ONLY when the wire genuinely branches
   there** (three or more things sharing one line that also exits) — never on a
   plain two-point wire.
7. **Where the geometry gives a trunk, a branching wire looks like a river with
   tributaries**: two near-opposite arms form one continuous line flowing straight
   through, and side arms merge into it smoothly at different points along it — NOT
   a bundle of lines all meeting at one dot. Where the branch is near-symmetric
   (e.g. three even arms) there is NO forced trunk — the arms simply meet; the
   through-line appears only when two arms actually line up.
8. **When a branch reorganizes, it morphs** — the through-line and its side arms
   slide, and the shape flows through the change; branches never jump to a new
   position or get redrawn on a different path.
9. **Nothing moves "by itself at a distance."** Rotating or dragging one node never
   counter-moves another node that it isn't touching or wired to; things interact
   only by touching or by the wires between them.
10. **The whole diagram eases toward rest together and quickly** — every part
    inching a little every frame — instead of one part clicking to a new spot, then
    another, in slow lurches.
11. **You never see a wire loop around the diagram — and nodes spin FREELY to
    prevent it.** A node whips around to face its wire and shed tension (as fast as
    it needs to, a whole turn in a moment if the energy calls for it — this is
    desired, an angle carries no meaning); the wire stays short. You see the NODE
    spin, never the WIRE grow a big arc to reach around.
12. **On a rewrite / proof step, the picture morphs continuously**: the parts that
    survive glide to their new spots and new parts grow in right at their connection
    points — all INSIDE the unchanged fixed border (the frame does NOT resize at a
    rewrite; content reflows within it — USER RULING 2026-07-06). No popping or
    snapping anywhere in the transition.
13. **A dragged node stays inside its own region and never crosses into a cut it
    isn't part of**, even for an instant, and the frame does not grow to chase it.

---

## RESOLVED — user rulings 2026-07-06

All four open questions were ruled on by the user (recorded in the corpus memory)
and folded into the design above. Recorded here so the executor treats them as
hard constraints, not choices:

- **1. Node angle is free and unlimited.** "Node angle is ARBITRARY. It encodes NO
  information and is FREE in the physics." No rotation-rate cap of any kind (the
  `~0.3 rad/frame` class of bounds was a wrong assumption); the no-snap law governs
  WIRE SHAPES, never node angles. A node spinning fast to shed wire tension is
  DESIRED behavior, complained about when missing. → Subsystem 4 "Node rotation is
  FREE"; item 11.
- **2. Q-A — Frame: near-square, absolute, hard edge.** Near-square (the proof
  footprint, boundaries on equal footing). Sizes are ABSOLUTE, computed at spawn
  from contents, never grow/shrink from motion, recalculated ONLY at a rewrite. The
  boundary is a HARD edge. → Subsystem 1; items 1, 3, 13.
- **3. Q-B — Trunks need not exist.** Near-symmetric junctions may have no trunk;
  never enforce one — the tributary reading emerges only where the geometry gives
  it. → Subsystem 3 "A trunk is EMERGENT, never enforced"; item 7.
- **4. Q-C and Q-D are answered by 1 and 2.** The transient spin (Q-C) is a FEATURE
  (rule 1: spin freely), not a cost to minimize. The hard-drag question (Q-D) is
  settled by rule 2: hard edge, no motion-triggered resize — a drag meets the wall,
  the frame never grows.

The ONE thing still not de-risked is not a preference but an engineering fact: item
10's "all layout DOF, every frame" needs the per-sweep cost to fall ~15–25× from
the plan-23 measurement (see Subsystem 4). It is called out in the implementation
plan's Task 6 as the gating risk, to be MEASURED, never faked with a cap.

---

## IMPLEMENTATION PLAN

Branch: continue on `plan-21-wire-physics`. **Acceptance is measured ONLY in the
user's live use of the app** (mandate: "acceptance measured ONLY in the user's live
use; no demo-loop resets"). Every task below carries a live-app gate — the change
is not done until it is verified in the running app, not just in a demo or a unit
test (corpus "APP PARITY IS PART OF EVERY FIX"). Tests pin the structural laws so
regressions are caught, but green tests are NOT acceptance.

### Task 0 — the deletion list (do this FIRST, as one demolition pass)

The accreted mechanisms the reset rejected are deleted BEFORE the new subsystems
land, so nothing is built on top of them and no "dual system" survives (CLAUDE.md:
no legacy, no compatibility layer). Delete, and fix the resulting type errors by
building the replacements:

- `globalRotationDof` (relax.ts) and every call — the centroid coupling (rule 9).
- `FRAME_CAP` (relax.ts) and `rotCap`; the `frameCap` parameter threaded through
  `descentDofs` / `descentSweep` / `settleStepBudget`; `e.descentCursor` and the
  sweep-slicing. (Motion policy — small-step is per-frame full sweep, not slicing.)
- The `e:<wid>` exit-hub body for boundary wires in `mkEngine`; `WireHub`'s use as
  the single shared hub point where all legs meet; `trunkTarget`'s discrete
  `axisSide` branch; `trunkAlignE` in its spoke form.
- `boundaryExits` (wires.ts) exterior connector + frame tick; `exitAttractE` /
  `WIREP.exitPull` / `boundaryExitE`; the `e:`-body special-cases scattered through
  `recomputeRegions` / `resolveOverlaps` / `projectBodyPos` / `clampDragToFeasible`
  / `contentEnergy`.
- The junction-dot draw for `e:` bodies in `paintWires`.
- `frameBounds`'s derivation from the sheet circle (replaced by stored frame state).

**Law**: after Task 0 the project compiles and every surviving test that does not
depend on a deleted mechanism passes; deleted-mechanism tests are removed with
their mechanism (not ported — corpus test-policy directive). **Live gate**: the app
still boots and renders a settled diagram (degraded — no frame/boundary rework yet).

### Task 1 — the fixed frame + hard edge (Subsystem 1)

Stored frame `{ center, half }` on the Engine, established at `mkEngine` /
`carryOver` from the projected content extent (near-square, absolute). `frameBounds`
returns it verbatim. Camera fits to it. Frame edge becomes a hard wall in
`projectBodyPos` (settling) and `clampDragToFeasible` (drag).

**Laws (tests)**: frame dimensions are byte-identical across 500 settle ticks on
every bundled scene (absolute, no breathing); every content disc is inside the frame
at rest on every scene; a scripted drag toward the edge never puts a disc past it and
never changes the frame size. **Live gate**: user sees the frame hold still while a
scene settles (items 1–3); the viewport does not jitter.

**BUG (USER 2026-07-06) — cuts escape the border:** the Task-1 wall clamped DISCS
but not REGION CIRCLES (cuts), so a cut's enclosing circle (members + `REGION_PAD`)
bulges past the frame. FIX: the hard wall applies to region circles identically —
every region circle stays fully inside the border, settled AND mid-drag. Added law
test (reproduced first): no region circle crosses the frame on any settled bundled
scene, nor during a scripted drag toward the edge.

### Task 2 — bodyless boundary attachment (Subsystem 2)

Slot = fixed anchor point on the inner frame edge with the inward-normal arrival
tangent. A 1-interior-port boundary wire is ONE elastica leg port→slot, no body. A
k≥2 boundary wire is an interior-style junction (Task 4) with one arm pinned to the
slot. Slots placed by the existing `frameSlots` on the fixed frame, canonical order.

**Laws**: a 1-port boundary wire produces exactly one leg and zero junction bodies;
its far end sits on the inner frame edge, tangent = inward normal, ≤ quadrature
residual, under violent motion; slot order = boundary index (cannot swap). **Live
gate**: user sees simple boundary wires as a single curve meeting the inside of the
frame with NO dot and nothing outside (items 4–6).

### Task 3 — free node rotation + local-only motion (Subsystem 4, part 1)

Node-rotation DOF uncapped (no rate bound; full gated step every frame). All motion
is local: node translation from contact (sibling barrier) + wire pull; rotation from
its own wires; no global operators. This is mostly a consequence of Task 0's
deletions plus removing the rotation cap.

**Laws**: on a framed scene at rest, no port faces >90° from its wire's first
segment (rotation reached facing); a scripted twist of one node relaxes with NO
other non-contacting, non-wired node moving (locality); node angular speed is
unbounded (a stuck-facing fixture that needed `globalRotationDof` now self-corrects
by local spin — re-measured, not assumed, per Subsystem 4's flagged consequence).
**Live gate**: user sees nodes spin freely to unwind wires (item 11); nothing
action-at-a-distance (item 9).

### Task 4 — trunk-as-emergent junction (Subsystem 3)

Replace the shared hub point with the trunk-curve + merge-parameter model: a
continuous trunk axis (inertial DOF) + per-leg merge parameter (DOF), carried by
`carryOver`. NO stored trunk pair, NO argmax; the through-line is the continuous
readout of the axis and fades to nothing at symmetry. Tributary legs are free-end
elastica arriving tangent at their merge point on the through-line.

**Laws**: zero per-frame role re-derivation (a fixture that slowly rotates a
junction's ports produces a drawn-polyline path with NO jump > 1 wu on any leg
across the whole rotation — the anti-snap law, the reset's core complaint); a
symmetric 3-way junction rests with all three merge weights small and no through-line
(trunk not enforced); a 2-leg "junction" is exactly the one through-curve.
**Live gate**: user sees the river-with-tributaries where arms align and a plain
meeting where they don't (item 7), and morphing (never jumping) on reorganization
(item 8).

### Task 5 — continuous transitions (Subsystem 5)

`carryOver` extended to the trunk axis + merge parameters (DONE, commit 699bac7).
New bodies seed near ports (already done — verify no regression). Leading
construction projection runs once off-screen.

**REVISED by USER RULING 2026-07-06 (border never resizes):** the frame-morph is
DELETED — there is no old→new frame interpolation because the frame does NOT change
size at a rewrite. The frame is established ONCE (first spawn) and is constant for
the diagram's lifetime; a rewrite carries over the SAME frame, and the new content
reflows INSIDE it. `establishFrame` must therefore run only when there is no prior
frame (or be carried by `carryOver`), NOT at every rewrite. If a rewrite's content
genuinely cannot fit the fixed border, that is a FORK to report to the user, not a
silent resize.

**Laws**: across a scripted rewrite, every surviving body's first drawn position is
within `carryOver` tolerance of its last (glide, no teleport); the frame `{center,
half}` is BYTE-IDENTICAL across the rewrite (never resizes); new wires' first drawn
samples start near their ports (no wild spawn). **Live gate**: user steps a
proof/replay and sees continuous morph inside the unchanged border (item 12).

### Task 6 — full-sweep-per-frame at 60 fps (Subsystem 4, part 2) — THE RISK

Replace the sliced budget with a full small-step sweep every frame. This REQUIRES
the per-sweep cost to fall ~15–25× (plan-23: 250–450 ms → ~16 ms). This task is
MEASUREMENT-FIRST: profile the sweep, attribute the cost (expected: the grid leg
solve inside every gated energy eval), and reduce it by PRINCIPLED means (cheaper
localized energy, fewer evals per gated step, a solve/paint resolution split) — NOT
by reinstating a magnitude cap or slicing (both deleted, both banned as the
snail's-pace / hard-click hacks). If the cost cannot be brought under budget
honestly, that is a FAILING, REPORTED state (a documented open problem), never a
green suite hiding a cap.

**Laws**: total E monotone non-increasing across every settleStep on every fixture
(the plan-23 theorem, preserved); measured per-frame sweep cost recorded per scene;
all previously-resting fixtures still rest. **Live gate (the acceptance gate for the
whole plan)**: the user drives the live app on the largest bundled proof and sees
the diagram ease to rest smoothly and quickly at interactive frame rate — no lurching
(item 10), no snail's pace. This is the gate the mandate names; nothing is "done"
until the user confirms it in live use.

**STATUS 2026-07-06 (measured, HELD pending Task-4 aesthetic verdict):** the sweep
cost was measured (20-tick-settle, comparable): baseline pc20 245 / ss24 187 / ss48
265 ms; AFTER Task 4's curved trunk pc20 459 / ss24 433 / ss48 493 ms (~1.85× — the
`phi`+`curv` DOF re-solve every hub leg per eval + `trunkCurveE` per probe). So the
gap is now ~26–30× the 16.7 ms budget. Task 6 is HELD (team-lead decision): the
aesthetic (Task 4) is validated FIRST, since a ~30× grind on a possibly-revisable
trunk is waste. Only design-INDEPENDENT prep that survives any trunk revision may
proceed (cached region circles, localized `contentEnergy`) — no gradient-machinery
work yet. **INTERIM VERIFICATION RECORD:** the settle-heavy `wirephys.test.ts` +
`relax.test.ts` battery (~2 h, and slower now under Task 4's cost) is DEFERRED until
after the perf work. The Task-4 laws were instead verified INDIVIDUALLY in node
(strict total-E descent E-rise 0.0/30 ticks; no NaN; distributed merges; anti-snap
0.30 wu/frame at slow rotation; the pre-existing blind-cone flip reduced 22.99→8.75
wu, reported not patched). Those individual node checks are the honest interim record;
the full battery must run (likely with reduced budgets) once perf is addressed.

**RESULTS 2026-07-07 (perf actually done; the trunk was reverted to the demo method,
so the ~1.85× trunk cost is gone). Profiled: the sweep is ~957 grid leg-solves, each
a ~17-`tryTau` memoryless global search × Newton; ≈300K trace-passes/sweep. Leg-solve
IS ~85% of the sweep. Levers, measured:**

- **Analytic Jacobian in the leg-solve Newton (`closeAt`) — LANDED, ~2.8×** (pc20 813→268
  ms/tick, measure-sweep gate). `closeAt` did 3 traces/iter (endpoint + 2 finite-diff
  perturbations); replaced by ONE pass computing endpoint + exact Jacobian (∂θ/∂c1 =
  t(1−t); ∂end/∂L = (end−p0)/L). Output-identical (same root), so all laws hold trivially.
- **Warm gradient probes in gatedStep — TRIED, REVERTED.** ~7% (within noise) but the
  warm gradient reached a DIFFERENT valid rest state that broke the drag-clamp cut-
  containment law (overshoot 1.3 vs 0.5 mid-drag). LESSON: "OUTPUT-pure" (monotone
  preserved) ≠ same rest; a different descent PATH → different basin → tuned law tests
  break. Verify the FULL suite before committing a gradient-direction change.
- **Branch-and-bound τ-scan pruning — TRIED, REVERTED (net ~0).** Tight joint bound
  (min over feasible L of tension·L + bend·τ²/L + exact well) + best-first order only
  pruned 29%: the 8 refinement candidates sit AT the argmin (lowest bound) and
  structurally cannot prune; the bound's cos+sqrt + sort offset the ~5 closeAt saved.
- **REFINEMENT cut (kept the full scan, cut 4 cold rounds → 3 WARM-seeded) — TRIED,
  REVERTED.** 29% fewer Newton iters/sweep (121,503→86,618, ~1.2×) and continuity-
  matched, BUT the coarser ±0.069 τ precision left a slower residual tail: the full
  battery flagged succShiftS@24 drifting 1.70 wu over 200 post-settle ticks vs the 1.5
  rest bound (E still monotone — a "settle and stay" regression, not a monotonicity
  break). Loosening the rest bound to keep it would mean content rests LESS precisely
  (the wrong direction for the user's jitter complaint), so reverted.

**KEY NEGATIVE FINDING — the τ-scan DENSITY is the no-snap law's floor, not just a
correctness knob.** The USER dropped output-identity 2026-07-07 ("I never saw what you
are trying to preserve"), authorizing a cheaper deterministic search returning
different-but-lawful curves. But a coarser candidate set tracks the argmin's basin
choice less smoothly through the energy landscape's phase transitions, adding
basin-flip SNAPS the shipped full 9-scan does not have — a TIME-CONTINUITY (no-snap)
violation. Measured max drawn-shape jump / port-motion over a slow boundary sweep,
counting jumps > 20× as snaps:

| welled leg th1 | full 9-scan (shipped) | narrow (arc+D0, 3-6 probes) | 5-pt uniform |
|---|---|---|---|
| 0.5  | 0 snaps | 0 | 0 |
| 1.5  | 0 snaps | **1 (new)** | 0 |
| 2.5  | 1 (inherent) | 1 | 1 |
| 3.0  | 1 (inherent) | 1 | 1 |
| −1.0 | 1 (inherent) | **4 (new)** | 1 |
| −2.5 | 1 (inherent) | 1 | 1 |

The 1-snap entries are INHERENT argmin phase transitions (present in the shipped
solver — accepted). The narrow set ADDS snaps (th1=1.5, −1.0); a 5-point uniform scan
recovers the shipped snap-count but its far-τ candidates fail `closeAt` fast (cheap),
so cutting them saves ~nothing. Conclusion: the whole-interval scan STAYS; and every
OUTPUT-CHANGING leg-solve lever tried (warm gradient, branch-and-bound, refinement cut)
either nets ~0 or shifts rest states into a law violation. The ONLY lawful gain is the
OUTPUT-IDENTICAL analytic Jacobian (2.8×). **Honest ceiling of lawful LOCAL optimization:
~2.8× from baseline (~6 fps), NOT 60 fps.** The lesson is sharp: the strict-descent laws
are tuned to the solver's exact output, so only output-identical changes are safe — the
next real gains must be EXACT (see the frontier).

**NAMED NEXT FRONTIER (architecture, not a lever): the GATE-EVAL COUNT.** Even after
the cuts the descent demands ~957 leg re-solves / ≈86K Newton iters per sweep, because
every gate's energy eval re-solves its touched legs from scratch (the strict gate's
honesty rests on consistent, non-stale energy evaluation — the warm-gradient revert is
the cautionary tale of stale-shape evals shifting rest states into law violations).
Breaking past ~7 fps means a DESCENT-ARCHITECTURE change (e.g. reusing a leg's solve
across evals within a sweep when its exact boundary tuple is unchanged, with an
explicit invalidation guarantee so the gate never accepts on a stale shape) — a
designed option with a guarantees analysis, to be weighed by the user against the
measured ~7 fps stakes, not a tuning lever to be slipped in.

**RESULTS 2026-07-07 (impl24d — the two authorized pure levers, measured on clean cores):**

- **EXACT CROSS-EVAL SOLVE REUSE (the frontier above) — LANDED, output-identical, commit
  4cf55de.** The leg memo was a SINGLE slot, so a gated step re-solved its base value
  after EVERY rejected trial (backtracking + long-shot return to base, slot overwritten
  by the intervening trial). Widened to a 16-entry FIFO ring keyed on the exact tuple so
  the base stays resident across a gate's probes. Reuse is by EXACT tuple equality —
  the exact-key match IS the invalidation (a changed tuple misses and solves fresh; a
  stale shape can never be returned), so output is BIT-IDENTICAL to the single-slot memo.
  Law (relax.test.ts): plusComm@20 settles bit-identically with the memo on vs off
  (`legCache.enabled`), maxDiff exactly 0. Measured real leg-solves/tick 1087→850 (pc20)
  / 842→660 (ss24) / 1060→835 (ss48) = ~22–25% fewer; paired ms/tick (same-process, same
  contention) 1.14× / 1.34× / 1.15×. **Honest fps: pc20 ~3, ss24 ~5** — reuse alone is
  far short of 20/60 fps. Diminishing returns past ring N=8 (measured N∈{1,2,4,8,16,32}:
  hit-rate 4.7%→9.8%→22.4%→23.4%→25.5%→25.9%); N=16 chosen. This is the frontier's
  exact-tuple ceiling: the residual ~850 solves are GENUINELY-DISTINCT probe tuples
  (every gradient/line-search trial moves the DOF, changing its legs' tuples), which no
  exact-reuse can serve.

- **ANALYTIC/ENVELOPE GATE GRADIENTS (2nd authorized lever) — TRIED, REVERTED (breaks a
  HARD law, reproduced).** The three grid-FD gate gradients that dominate the solve count
  (profiled pc20: hubPoint 33%, nodeRot 29%, hubAngle 25% — nodeXlate is only 13% because
  it ALREADY uses the warm gradient) were switched to the warm/envelope gradient (fixed
  base turning via `closeAt`, no grid scan) for the ±h probes only, accept still grid.
  Grid-solves dropped ~21% (pc20 850→672). But the warm gradient reaches a DIFFERENT
  valid rest state that VIOLATES HARD SEMANTIC CONTAINMENT: drag-clamp mid-drag cut
  overshoot 1.31 wu vs the 0.5 bound — an EXACT reproduction of the prior warm-gradient
  revert. A hard USER law (a cut crossing the border changes what the diagram MEANS)
  cannot be traded for a modest solve cut, so reverted. The only alternative — an EXACT
  analytic gradient of the FULL localE — is intractable in closed form (the clearance/
  separation terms are repulsion integrals over the traced polyline of a
  constraint-optimized elastica). **Conclusion: BOTH authorized pure levers are now
  spent. The lawful ceiling stands at the analytic-Jacobian × ring-reuse ≈ 3–4× (~3–5
  fps).** 20+ fps still requires the descent-architecture change beyond exact-tuple reuse
  (fewer PROBES per gate, or approximate-but-provably-safe evals) — a design the user
  must weigh, not a lever, and the warm-gradient reproduction is fresh evidence that any
  probe-value change shifts basins into law violations.
