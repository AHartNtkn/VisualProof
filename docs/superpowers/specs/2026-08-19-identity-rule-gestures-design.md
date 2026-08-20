# Identity-Rule Gestures — Ratified Design (2026-08-19)

Status: RATIFIED in conversation 2026-08-19. This document records the
approved design the implementation plan
(`docs/superpowers/plans/2026-08-19-identity-rule-gestures.md`) executes.

## Problem

The three identity rules (`vacuity`, `presentation`, `identification`,
src/kernel/rules/identity-rules.ts) exist as kernel steps but have almost no
interactive entry points. The only paths are two composites: `Q` (bare-wire
insert) and Delete on an all-pin wire (bare-wire deletion). Separately, the
right-button "drawing gesture" (`DrawGestureController`, src/app/interact/
draw.ts, introduced by commit b35f0830) was never ratified by the user,
violates the standing gesture law (every gesture is a single object or an
oriented drag between two specific objects), and is — user ruling — "so hard
to use that there's no way to use it accidentally". It is deleted outright.

## Standing user laws this design obeys

1. No menus for proof actions; the palette is an interaction of last resort,
   reserved for things impossible to specify by gesture (definitions).
2. Every gesture takes a single object or an oriented drag between two
   specific objects. No interaction depends on selection order.
3. Any operation available in both edit (construction) and proof mode must
   be accessed by the same gesture in both modes.
4. The kernel is the sole authority at commit; refusals surface verbatim as
   spring-back. Action enumerations only mirror gates, never enforce them.
5. Never encode editor intent as diagram or proof content.

## Key representational fact (established during design)

Wires are physical objects: one wire is one connected chain network touching
all its endpoints. Two wires terminating at an arity-2 identity dot draw as
two chains meeting at a dot **in** the path (`————●————`); one wire with an
arity-1 pin draws as one continuous chain with the pin hanging **off** it as
a branch tip. These are different drawings, so identification collapse and
exposure are visible operations and get gestures.

## The gesture table (mode-agnostic)

| Gesture | Operation | Proof-mode step | Edit-mode commit |
|---|---|---|---|
| Drag identity dot (disc interior) → open space | Identification **collapse**: dot's wires merge into one; dot survives as branch-hanging pin | `identification { kind: 'collapse' }` | same, via direct kernel apply |
| Drag identity dot rim → open space | Vacuity **stub grow**: fresh wire from the dot to a fresh far pin at the drop region | `vacuity insert { kind: 'stub' }` | same |
| Drag identity dot → another identity dot | Presentation **fuse**: one dot covering the union of both dots' ports | `presentation` | same |
| Drag a wire's end (atom/ref disc) or arg-port leg → an identity dot on that wire | Identification **expose**: that endpoint peels onto a fresh wire equated at the dot | `identification { kind: 'expose' }` | same |
| Drag wire `a`'s strand → wire `c`'s strand, where `a` and `c` meet at exactly one dot | Presentation **fission**: fresh dot takes `a` plus `c` (the target is the drawn bridge); the old dot keeps everything but `a`. Lines sharing no dot keep meaning join; sharing several dots refuses | `presentation` | same |
| Drag a wire's strand → a dot it is attached to | Presentation **duplicate**: the wire gains a second leg on that dot | `presentation` | same |
| Drag a dot → the strand of a wire holding two of its legs | Presentation **contract**: the two legs become one | `presentation` | same |
| `Q` over blank | Bare segment (point∘stub composite) at the region under the pointer; `Shift+Q` = nullary-relation sig | existing vacuity composite | `addRelationWire` |
| `Q` over a wire strand | Vacuity **pin insert** on that wire at the region under the pointer | `vacuity insert { kind: 'pin' }` | `applyVacuityInsert` |
| Delete with one identity node selected | Shape-determined vacuity delete: arity-0 → point delete; pin whose 2-end wire's other end is an identity node → stub retract; otherwise → pin detach | `vacuity delete` | existing `deleteHits` (edit deletes freely) |
| Right-drag straight line (**slash**) crossing wire legs | Sever the crossed endpoints | `wireSever` (one step per crossed wire; `scope` omitted → derived scope) | existing `severEndpoint` loop |
| Still right-click | Spawn palette / context surface (unchanged, both modes) | — | — |

AMENDMENT (2026-08-20, user-ordered): ports are not objects — "a wire+node is
all you need for any rule." The original fission/duplicate/contract rows
designated legs by identity-port index; those are banned as designations and
provably unhittable (identity ports all anchor at the dot's centre). The
rows above are the re-grounded versions: every designation is a wire or a
node. Any residual port-index choice is invisible (isomorphic results) and
resolved internally. The strand→strand drag means join ONLY for lines not
already meeting at a dot; for lines meeting at exactly one dot it means
fission (join's result there stays reachable by collapse-then-duplicate).

Precedence rulings:
- Dot-onto-dot always reads as **fuse**, even when the dragged dot is a pin
  (a pin is both an end and a dot); exposing a pin endpoint is reached by
  composition, not gesture.
- Collapse survivor selection is forced-or-invisible: the absorbed-wire
  condition (every non-dot endpoint at-or-under the dot's region) determines
  the survivor when exactly one wire violates it; when none violate, the
  lexicographically first wire survives (wire ids are not drawn, so the
  choice is invisible); when several violate, pick the lexicographically
  first violator and let the kernel refuse with its own message.
- Fission's bridge is the drop target: logic does not determine which wire
  is drawn spanning both dots, so the oriented drag does.
- Lone points need no insert gesture: `Q` then Delete on one pin (stub
  retract) leaves the arity-0 point. Revisit only if this proves annoying.

## Deletions and strandings

- `draw.ts` and its contact mechanism: deleted outright, with its tests.
- `identityInsert` UI surface (ActionDescriptor, `identityInsertionWires`,
  menu row): dead after draw.ts, deleted. The kernel rule stays (replay
  language). Interactive equating composes: join (strand→strand drag),
  `Q`-pin, expose.
- `abstractFormal`, `endsSpawn`, lasso `cutWrap`: lose their only entry
  points; left gestureless deliberately, flagged for a later session. The
  kernel rules stay.

## Mode asymmetry (accepted)

Same gesture, same meaning, different authority: proof-mode commits run the
gated/kernel-validated appliers and can spring back; edit mode authors
statements freely (its commits use the same kernel functions for the
ungated identity rules, and unrestricted constructions elsewhere). This is
the existing edit-join vs gated proof-join pattern.
