# 3D Tree View — Design

**Status:** approved in discussion 2026-08-14; awaiting spec review.

The app gains a toggleable, view-only 3D presentation of the focused proof diagram. Each region — the sheet and every cut — is drawn as a straight line segment; the region tree becomes a literal 3D tree, nodes sit on their region's line, and wires span free space between branches as glowing curves. Nothing about the kernel, rules, or stored data changes: this is purely a second presentation of the same `Diagram`.

Decisions fixed during brainstorming, in order:

- **Scope:** view-only first. Camera control plus hover highlight; no selection, no proof actions. Proof actions stay in the 2D view.
- **Renderer:** three.js, added as the repository's first runtime dependency.
- **Content:** the focused diagram only (the active proof side/track's current state), not the whole workspace.
- **Layout:** deterministic analytic construction (approach A) — no annealing, no per-frame physics, no iteration beyond convex solves. Chosen over force relaxation explicitly to avoid rebuilding the 2D machinery's failure modes.
- **The hard problem is the wires, not the branches.** Keeping tree branches apart is easy; the requirement that matters is that the web of wire curves between nodes never touches — not each other and not the tree — and that the tree's sizing budgets room for wire content, not just node content.
- **Everything renders as lines**, not tessellated solids: the subjects are 1D curves embedded in 3D.

## Visual language

- **Sheet = trunk.** The root segment is the sheet region, outside any cut. The shallowest cuts branch directly off it. Every region's segment carries its own nodes; a region with more content is a longer line.
- **Branch points.** Where a child cut leaves its parent, a small bead marks the point. A cut whose only content is a single child cut continues collinearly — the bead alone distinguishes "cut inside cut" from one continuing line.
- **Identity nodes** are invisible as glyphs: their wire simply meets the region's line at the anchor point.
- **Atom and ref nodes** are circles (thin ring polylines) lying in the plane perpendicular to the branch line, which passes through the ring's center. Ports anchor at evenly spaced points on the rim. Rings carry no text; a ref node's name floats beside its ring as a billboard label (named definitions are their own nodes; text never appears inside term structure).
- **Wires** are 3D splines through free space, touching the tree only at node anchors. A wire with three or more ends is drawn as a branched network — junction vertices meeting its curves with the length-minimizing (120°-style) geometry, the 3D counterpart of the 2D routed-network wires.
- **Dark theme:** black background (`#0e1013`), white glowing branch lines and beads, wires in the existing per-relation hues with bloom. **Light theme:** the existing manuscript tan (`#e8e4d8`), near-black ink lines, darkened relation hues, no bloom. Both derive from the existing `Theme` object via its `mode`.

## Architecture

New module `src/view3d/`, beside `src/view/`. It consumes only the kernel diagram model (`Diagram` / `DiagramWithBoundary`) plus the app-level relation-hue assignment. It never reads the 2D `Engine`; the two views are independent presentations of the same kernel state.

| File | Role |
|---|---|
| `scene.ts` | Pure mapping `Diagram` → abstract scene description: segments, node anchors, wire network specs. Plain vectors, no three.js types. |
| `layout.ts` | The analytic layout (below). Pure, deterministic. |
| `render.ts` | The only file importing three.js. Builds/updates the scene graph, owns materials, bloom, and the render loop. |
| `camera.ts` | Orbit / pan / zoom controller. |
| `pick.ts` | Hover picking by raycast against the polylines, reporting kernel ids (`RegionId` / `NodeId` / `WireId`). |

**App integration:** a view-mode toggle in the shell chrome. When active, the 2D canvas hides and a WebGL canvas shows the focused diagram. On each proof-state change the shell hands the new `Diagram` to the 3D view, which recomputes layout and tweens the transition.

## Layout

### Tree skeleton

Every region is a straight segment carrying ONLY its nodes, placed along it in canonical diagram order (USER ruling 2026-08-15: sibling sub-cuts never compete for room along the parent's axis, so spreading branch points there only made the tree tall). A node's spacing grows with its port count (rim anchors need room); segment length is the sum of node spacings, plus a short bare tail only when the region has no children, so a childless line still reads as a line.

All child cuts fan out from the segment's **tip**. A single child continues collinearly (its bead alone marks the crossing); two or more leave at a shared tilt with the circle of azimuths partitioned into disjoint arcs proportional to each child's angular footprint **plus a term for the wires crossing between subtrees**, so heavily webbed regions get wider gaps for the web to pass through. Under azimuthal overflow the fan widens its tilt toward perpendicular first — heavy boughs spread flatter — and only lengthens lead-ins when even a flat fan cannot fit.

Each subtree is summarized bottom-up by its **capsule envelope**: its own corridor capsule (the segment inflated by a clearance radius that grows with the number of escaping wire curves — each needs its own tube of routing room) plus every descendant's capsules in their placed pose. A child's bare lead-in is the minimal stem at which its envelope clears the parent corridor by δ (a monotone bisection bracketed by a proven conservative bound), so lead-ins scale with what actually approaches the parent, never with subtree size. Sibling envelopes are disjoint by the azimuth partition; non-adjacent subtrees nest by induction. This budgets room; it is not the wire-separation mechanism.

### Wire layout — the separation guarantee

Two stages, both deterministic:

1. **Per-wire branching topology.** A wire with three or more ends takes the network minimizing total curve length over its terminals: enumerate the Steiner topologies exactly (arities are small), solve each fixed topology's junction positions by convex minimization (sum of Euclidean edge lengths is convex), take the least-total-length result. Junctions come out with the length-minimizing meeting geometry. Two-ended wires are a single spline.

2. **Sequential clearance routing.** Wires route one at a time in canonical order, each network edge as a spline around a frozen obstacle set: the tree's segments, rings, and beads inflated by clearance δ, **plus every previously routed wire curve inflated by δ**. A blocked chord escapes around an obstacle in a perpendicular plane — the third dimension makes this always possible. Each wire therefore ends at distance ≥ δ from the tree and from every earlier wire *at the moment its curve is created*; separation is enforced by construction, never hoped for afterward. Near shared anchors, wires on the same node are separated by rim-anchor spacing, which the ring radius budgets.

Anchors: identity wires meet the segment directly; atom/ref wires meet rim points with outward-normal boundary conditions. Each ring's free rotation about the branch axis is the circular mean of the directions toward its wire partners (closed form; shortens wires).

The entire layout is a pure function of the `Diagram`: no state, no frames of simulation, no tuning loops.

## Rendering

The full render inventory: polylines, point sprites, one bloom pass, one text billboard per ref node.

- All curves — branches, wires, rings — are polylines drawn with three.js's screen-space-width line material (`Line2`/`LineMaterial`; plain `THREE.Line` is 1px-limited on most platforms). No tubes, no tori.
- Width hierarchy: branches slightly wider than wires. Hover thickens/brightens by swapping material parameters, not geometry.
- Beads are point/disc sprites.
- Bloom (`UnrealBloomPass`) runs in dark mode only; it operates on the rendered image, so the line-based geometry needs nothing special.
- Hover: raycast with a distance threshold. A wire hit highlights that wire's whole network; a branch hit highlights its whole subtree line; a node hit highlights its ring plus incident wire anchors. Highlight tint is the theme's existing `interaction.hover` color.
- Camera: perspective, orbiting the bounding-sphere center; wheel zoom; right-drag pan; initial framing fits the bounding sphere.

## Animation and transitions

A proof step means: new diagram → new layout → tween. Kernel ids are largely stable across steps (the 2D `carryOver` already relies on this), so matching is by id. Matched entities interpolate position along an eased tween; entities only in the old state fade out; entities only in the new state fade in at their final position. The camera re-fits only if the new bounding sphere escapes the current framing. Tween duration is a single named constant.

Rendering is on demand: a frame draws only when the camera moves, hover changes, or a tween is active. Idle scenes cost nothing.

## Testing

Built alongside each part; all pure modules run under vitest without WebGL.

- **`layout.ts` invariants:** sibling cones pairwise disjoint; every subtree inside its declared cone; segment length = sum of content spacings; sampled wire–wire and wire–tree minimum distance ≥ δ; adding ports/wires widens the relevant spacing and arcs; identical output for identical input.
- **Steiner solver:** 3-terminal cases against the known Fermat-point geometry (curves meet at 120°); degenerate collinear terminals; topology enumeration on 4–5 terminals.
- **`scene.ts`:** every region, node, and wire of the input appears exactly once with its kernel id; identity anchors lie on their segment; lone-child cuts are collinear with a bead.
- **Transition planner:** pure function (old scene, new scene) → tween plan; id matching, fades, no orphaned entities.
- **`render.ts` / `pick.ts`:** kept thin; verified through the existing Playwright e2e setup with a screenshot smoke test and a hover-highlight assertion.

## Out of scope (this phase)

Selection, proof actions, drawing, and any 3D-native interaction redesign beyond hover; whole-workspace rendering; any change to kernel, rules, persistence, or the 2D view.
