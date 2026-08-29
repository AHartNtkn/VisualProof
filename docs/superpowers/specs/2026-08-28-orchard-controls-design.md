# Orchard Shared Authority Design

## Goal

Make the orchard consume the proof assistant's existing 3D interaction and
semantic authorities, while retaining only the world-scale rendering,
persistence, and free-flight responsibilities that are specific to the game.

The orchard keeps its LOD,
batching, spatial index, fog, terrain, glow, and multi-tree scheduling.

## Authority Map

The final system has these owners:

- `src/view3d/scene.ts` owns typed 3D proof entities and their kernel identity.
- `src/view3d/entity-style.ts` owns the semantic entity-to-authored-color rule.
- `src/view3d/camera.ts` owns orbit camera operations, and
  `src/view3d/orbit-interaction.ts` owns orbit pose, drag, pan, zoom, semantic
  focus, and focus glide.
- `src/view3d/transition.ts` owns proof-tree transition timing, interruption,
  and sampling.
- `src/game/render/placement.ts` owns every orchard local/world transform.
- `GameSession` owns the current logical `GameTree` values.
- `GameWorldRenderer` owns render projections of those values, never a second
  logical tree model.
- `SaveWriter` owns asynchronous durable-write ordering and retry. Save state
  may lag live state while saving, but it may not describe a different queued
  tree.
- `game/input.ts` owns DOM input transport and transient samples. It reports
  engagement changes; it does not decide gameplay mode.
- The game navigation state owns free/orbit mode, the saved free pose, and
  whether free-flight input is active.

## Shared Proof-Entity Semantics

Every branch entity carries its `RegionId` directly, just as rings, labels,
pips, and strands already carry typed node or wire identity. Renderer keys
remain stable drawing identities, but application code never recovers kernel
identity by slicing a key string.

One pure color policy receives an entity, wire hues, and an authored palette.
Both renderers use it. Materials, line widths, textures, bloom, hover styling,
and batching remain renderer-specific presentation.

Orchard picking remains renderer-specific because it must work across batched,
culled, and tweening trees. Its semantic result carries the typed entity and a
world-space focus derived through the shared `focusPoint` rule. Picking does
not invent a second focus rule.

## Orchard Placement

`src/game/render/placement.ts` exposes the only local/world transform
operations for a placed tree:

```ts
localPointToWorld(point: Vec3, placement: TreePlacement): Vec3
worldPointToLocal(point: Vec3, placement: TreePlacement): Vec3
worldDirectionToLocal(direction: Vec3, placement: TreePlacement): Vec3
worldSphere(bounds: { center: Vec3; radius: number }, placement: TreePlacement): THREE.Sphere
applyPlacement(object: THREE.Object3D, placement: TreePlacement): void
```

Logical targeting, spatial bounds, analytic picking, rendered objects, and
orbit focus all consume these operations.

## Diagram and Tree State

A diagram and its canonical JSON are one nominal validated value. It is a
class with a private constructor and can be created only through its factories:

```ts
class DiagramSnapshot {
  readonly #brand = true

  private constructor(
    readonly diagram: Diagram,
    readonly json: string,
  ) {
    void this.#brand
    Object.freeze(this)
  }

  static fromDiagram(diagram: Diagram): DiagramSnapshot
  static fromJson(json: string): DiagramSnapshot
}
```

Construction either derives JSON from a diagram or parses and validates JSON.
The private `#brand` makes the value nominal, so a structurally matching object
cannot be supplied as a snapshot. The private constructor restricts creation
to the validating factories. `GameTree` contains one `snapshot` value.

Tree mutation is planned before it becomes live. A double cut produces one
immutable `TreeMutation` containing complete before and after `GameTree`
values. The session first validates the before value and prepares its next tree
map. The renderer then prepares all derived assets and target bounds without
changing live state. Once the save writer accepts the complete update, the
session publishes the after tree and the renderer performs its non-throwing
prepared commit.

If planning, session validation, renderer preparation, or save enqueue fails,
the live session and renderer remain on the before tree. The session discards
its unpublished prepared map, and the renderer disposes its unpublished
prepared resources. A later asynchronous save failure leaves one live tree and
one queued durable update; the existing retry state owns that lag. It does not
roll back gameplay.

Every committed tree update refreshes render geometry, runtime state, and
logical target bounds from the same prepared asset. `pickTree` therefore
cannot continue using bounds from an earlier diagram.

## Shared Tree Transitions

`src/view3d/transition.ts` owns one `SCENE_TWEEN_MS` and one reusable scene
tween track. The track plans from the currently displayed interrupted scene,
samples smooth progress, reports completion, and exposes the clean target.

The assistant retains its camera-pose tween. The orchard retains a map of
independent tracks and its runtime suspend/resume behavior. Neither consumer
implements transition restart or timing rules separately.

## Shared Orbit Interaction

`src/view3d/orbit-interaction.ts` is the reusable interaction controller. It
uses the shared `CamPose`, camera operations, semantic `focusPoint`, click
threshold, and focus glide. Both the assistant view and orchard instantiate
that controller.

The orchard supplies its current tree entities in local coordinates and the
placement authority converts the selected semantic focus into world
coordinates. The orchard does not define orbit rates, orbit geometry, focus
behavior, or another orbit state shape.

Free flight remains game-specific. Entering orbit stores the exact free pose.
Leaving orbit restores it. The free pose is the only camera pose sent to
persistence while orbiting.

The orchard's established secondary proof action is composed beside the
shared interaction. It is not part of orbit mechanics and never mutates the
camera.

## Input and Escape

Input engagement is reported to game navigation as an event; querying
`document.pointerLockElement` is not a gameplay-state decision.

Loading and creation request free-flight engagement during their existing user
interaction. Successful engagement activates free flight without another
click. Losing engagement, focus, or visibility deactivates free flight and
clears transient input without changing the saved pose or loaded world.

Escape while orbiting is handled by the game, restores the saved free pose,
requests free-flight engagement during the same physical key event, and
prevents that event from immediately cancelling the request. On success the
player can move and look immediately. On rejection, navigation becomes
inactive free flight and presents the ordinary engagement prompt.

Escape in free flight remains available to the browser's ordinary engagement
release behavior.

## Durable Documentation

`docs/orchard-game-design.md` is the durable product contract for orchard
navigation. It names the shared assistant orbit interaction, the game-owned
free-flight state, same-interaction Escape recovery, and the secondary proof
action composed beside orbit navigation.

This design document records the ownership boundaries. Its implementation
plan records delivery and validation steps. Behavioral tests enforce the
contracts at their consumer boundaries.

## Validation

Behavior evidence must prove:

- typed branch identity reaches the kernel operation without parsing a render
  key;
- both renderers obtain identical authored colors from one semantic rule;
- every placement consumer agrees for rotated, translated trees;
- mismatched diagram/JSON pairs are unrepresentable or rejected at creation;
- failed mutation preparation or enqueue leaves session and renderer unchanged;
- committed mutation refreshes geometry and logical target bounds together;
- interrupted assistant and orchard transitions sample the same shared track;
- the assistant and orchard exhibit the shared controller's orbit behavior;
- orchard orbit uses the same controller and semantic focus;
- Escape resumes free movement without another interaction;
- a proof action changes the tree and persistence while leaving orbit camera
  state unchanged.

The full unit suite, type check, native Tauri end-to-end scenario, and direct
application exercise are all required. Direct exercise must inspect the whole
state after orbit entry, component focus, proof action, Escape, and immediate
movement.

## Non-Goals

- Replacing the orchard renderer with the assistant renderer.
- Removing orchard LOD, batching, culling, spatial indexing, telemetry, fog,
  terrain, glow, or concurrent tree animation.
- Replacing the kernel proof rule or adding proof-history persistence.
- Adding a general action-map framework, settings, rebinding, gamepad, touch,
  collision, gravity, or new proof tools.
- Changing save-file format or introducing compatibility paths.
