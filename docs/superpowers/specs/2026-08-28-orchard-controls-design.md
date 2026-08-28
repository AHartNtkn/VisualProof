# Orchard Controls Design

## Goal

Add conventional browser-game navigation to the orchard without creating a
general input framework or duplicating camera authority.

The player moves through the orchard in free flight, aims from the center of
the view, and may temporarily orbit a tree. Browser cursor confinement is an
input transport detail. It is not a game mode, persisted state, or condition
for keeping the world open.

## Player Behavior

### Free flight

- Loading an orchard restores its saved free-flight pose.
- The world initially waits for a click before accepting free-flight input.
- That click engages cursorless relative mouse input. It does not move the
  camera or activate a world action.
- Mouse motion changes yaw and pitch. Pitch is clamped short of vertical.
- `W` and `S` move forward and backward in the horizontal view direction.
- `A` and `D` strafe left and right.
- `Space` rises, `Control` descends, and `Shift` triples movement speed.
- Movement is time-based, normalized across simultaneous axes, and has no
  acceleration, gravity, collision, or head bob.
- While engaged, the view center is the aim point and a small reticle is
  visible. There is no pointer.
- A primary click while a tree is under the aim point enters orbit. A click
  with no tree under the aim point does nothing.

### Orbit

- Orbit stores the exact free-flight pose that initiated it.
- Entering orbit releases cursorless input and restores the ordinary pointer.
- Mouse motion never changes the orbit camera.
- `A` and `D` rotate around the target.
- `W` and `S` change distance from the target.
- `Space` and `Control` raise and lower the orbit eye.
- `Shift` has no orbit meaning.
- The camera always looks at the target center.
- Orbit distance cannot pass inside the target's bounds.
- `Escape` leaves orbit and restores the stored free-flight pose exactly.
- Free flight remains disengaged after leaving orbit; the next world click
  re-engages cursorless input.

### Focus and interruption

- Losing cursorless browser input, window focus, or page visibility clears
  held keys and pending mouse motion.
- Such loss never changes camera mode, camera pose, loaded world, or save.
- In disengaged free flight, movement and mouse motion are ignored.
- Orbit keyboard controls remain available because orbit uses the ordinary
  pointer and does not require cursorless input.
- A secondary press has no camera effect. In engaged free flight it applies a
  double cut to the ordinary branch under the center reticle. In orbit it
  applies the same tool at the pointer and restricts targeting to the orbit
  target tree. Disengaged free flight does not apply a tool.

## Camera Authority

`src/game/camera.ts` is the only camera-state authority. Its state is a tagged
union:

```ts
export type CameraState =
  | { readonly mode: 'free'; readonly pose: CameraPose }
  | {
      readonly mode: 'orbit'
      readonly freePose: CameraPose
      readonly target: TreeTarget
      readonly azimuth: number
      readonly distance: number
      readonly height: number
    }
```

There are no parallel mode booleans and no camera state inside the renderer.
The camera module exposes pure operations to initialize, advance, enter orbit,
leave orbit, derive the displayed pose, and derive the pose written to the
save. The persisted pose is always the free-flight pose, including while the
display is orbiting.

The initial constants are intentionally few:

- mouse sensitivity: `0.002` radians per relative pixel;
- free-flight speed: `8` world units per second;
- sprint multiplier: `3`;
- orbit angular speed: `1.5` radians per second;
- orbit zoom speed: `12` world units per second;
- orbit vertical speed: `8` world units per second;
- minimum orbit distance: target radius plus `1` world unit;
- pitch range: `±(π/2 - 0.01)`.

These are direct constants, not settings infrastructure.

## Input Boundary

`game/input.ts` owns browser listeners and nothing else. It:

- tracks held movement keys;
- accumulates relative mouse deltas;
- converts held keys to a semantic per-frame motion record;
- delivers primary, secondary, and Escape callbacks synchronously;
- suppresses the browser context menu on the world;
- exposes whether the world currently has cursorless relative input;
- requests or releases that browser mechanism when the composition root asks;
- clears transient state on loss of engagement, blur, or hidden visibility;
- detaches every listener on disposal.

The input module never imports the renderer, changes camera state, targets a
tree, persists data, or treats synthetic and physical events differently.

## Tree Targeting

`src/game/render/world.ts` remains the sole renderer. It gains one query:

```ts
pickTree(ndcX: number, ndcY: number): TreeTarget | null
```

The query casts through the renderer's current camera and intersects the
logical world-space bounding sphere of every tree. It returns the nearest hit.
It does not inspect render LOD or individual tree parts. This keeps focus
stable even when a tree is represented as a marker or is waiting for render
residency.

`TreeTarget` is a small game-model value containing the tree ID, world-space
center, and radius. The camera copies this value when orbit begins; the
renderer never owns orbit state.

## Composition

`game/main.ts` is the composition root:

1. Load or create the world normally.
2. Initialize one `CameraState` from the saved `CameraPose`.
3. Attach one world-input instance.
4. On each animation frame, sample input once.
5. Advance orbit unconditionally, or advance free flight only while relative
   input is engaged.
6. Send `displayCameraPose(state)` to the renderer.
7. Send `cameraPoseForSave(state)` to the existing save writer.

Primary-down handling is synchronous:

- disengaged free mode: request relative input and consume the click;
- engaged free mode: query the center of the view and enter orbit on a hit;
- orbit mode: no camera action.

Escape exits orbit. In free mode it has no camera action; the browser's loss
of relative input clears held input through the ordinary engagement-change
path.

Secondary-down handling is synchronous and never changes camera state. The
composition root uses the engaged free-flight center ray or the orbit pointer
ray to query a branch. A hit mutates the game session, starts the renderer's
tree tween, and queues the existing tree save. A miss and tool error use the
existing feedback messages.

## Presentation

The loaded world has only two control affordances:

- a small center reticle while free flight is engaged;
- a short centered “Click to play” prompt while free flight is disengaged.

Both are derived presentation. Neither is an authority for control or camera
state. Orbit uses the ordinary pointer and displays neither affordance.

## Failure Behavior

- If requesting relative input is rejected, the world remains loaded in the
  same free pose and the “Click to play” prompt remains visible.
- A target miss is a no-op.
- All input is cleared when the world is disposed.
- No fallback gesture, drag-to-look mode, synthetic-event exception, or
  compatibility control path is provided.

## Validation

Pure camera tests prove literal positions and directions for free movement,
mouse look, combined-axis normalization, sprinting, orbit motion, distance
clamping, exact orbit exit, and free-pose persistence during orbit.

Input tests use real `EventTarget` dispatch to prove key mapping, delta
consumption, interruption clearing, synchronous action delivery, browser
engagement delegation, and complete listener cleanup. They assert sampled
behavior rather than source structure.

Renderer tests prove nearest logical tree targeting through the current camera,
branch targeting across render residency and LOD, and restriction to the orbit
target.

The native game scenario proves loading, free movement, orbit entry and exit,
camera persistence, interruption stability, and a secondary double cut that
persists while leaving orbit camera mode and pose unchanged.

Completion also requires direct in-app browser exercise with actual mouse and
keyboard controls. The full flow is inspected after each transition for camera
mode, focus, cursor presentation, loaded world, save state, and unintended
tree changes.

## Explicit Non-Goals

- rebinding, settings, gamepad, touch, accessibility alternatives, or an
  action-map framework;
- collision, gravity, terrain following, acceleration, animation, or sound;
- an orbit mouse-drag control;
- renderer-owned camera state;
- special test-only runtime behavior.
