# Orchard Pointer Input Design

## Purpose

Orchard has two mouse interaction modes. Free flight is a cursorless first-person
view controlled by relative mouse motion. Orbit is a cursor-based inspection view
in which mouse motion points at tree parts and never rotates the camera.

The implementation uses the webview's standard Pointer Lock API directly. Pointer
Lock already supplies unbounded `movementX` and `movementY`, removes the cursor
while active, and restores ordinary pointer behavior when released. Native cursor
positioning, cursor barriers, cursor-coordinate reconstruction, and a separate
input lifecycle are outside the design.

## Player-visible behavior

- The start menu has an ordinary cursor. Creating, listing, validating, and loading
  save slots do not depend on mouse-look state.
- A successfully opened world begins in free flight. Mouse movement changes yaw and
  pitch continuously; WASD, Space, Control, and Shift retain their current movement
  behavior.
- The free-flight reticle is the interaction target. Clicking when the reticle is
  over a reachable tree enters orbit around that tree. A miss changes nothing.
- Entering orbit restores the ordinary cursor. Mouse movement points at parts of the
  orbit target and does not change the camera.
- Escape leaves orbit, preserves the displayed camera pose, and resumes free-flight
  mouse-look.
- Right-click applies the current tool at the reticle in free flight and at the
  cursor position in orbit. Tool use never changes camera mode, camera pose, or the
  orbit target.

## Architecture

`game/main.ts` owns the small integration between browser input events and the pure
camera functions in `src/game/camera.ts`. The persistent `[data-world]` host is the
Pointer Lock target, so Create and Load can request it synchronously from their
click/submit activation before asynchronous save I/O begins:

- `requestPointerLock()` activates free-flight mouse-look on the world host.
- `document.exitPointerLock()` restores pointer interaction before orbit begins.
- World-host input handlers pass `movementX` and `movementY` to `lookCamera` only
  while the camera is in free mode and the host holds Pointer Lock. In orbit, the
  same handlers use ordinary canvas-relative coordinates.
- Orbit entry and exit update `CameraState` through `enterOrbit` and `exitOrbit`.
- Save loading remains owned by `StartLifecycle`; Pointer Lock does not add phases,
  queues, generations, overlays, retry objects, or parallel state.

Initial Pointer Lock uses the Create or Load activation. Orbit releases it through
`document.exitPointerLock()`, so the Pointer Lock contract permits re-entry without
another engagement gesture; Escape therefore resumes free look without relying on
Escape itself to create browser activation.

The supported webview contract is the current Promise-returning Pointer Lock API.
A rejected request is reported as a concrete world-entry or mode-transition
failure; it does not create a second gameplay mode or a resume UI.

## Transition proof

Two transitions require native-runtime evidence:

1. A Create or Load activation requests Pointer Lock before asynchronous save I/O,
   then opens the world with working free-flight relative mouse-look without
   another player action.
2. Escape from orbit restores working free-flight relative mouse-look while keeping
   the displayed eye and direction continuous.

The implementation is accepted only if both transitions work in the real Tauri
webview. If the webview rejects either transition, that result is an explicit
platform/product blocker. The implementation must not introduce an extra click,
overlay, drag gesture, native cursor path, or lifecycle framework as a fallback.

## Validation

Automated tests assert player behavior:

- Free-flight mouse motion changes the displayed camera.
- Clicking a reachable tree enters orbit; a miss does not.
- Mouse motion in orbit leaves the displayed camera unchanged while updating the
  pointed tree part.
- Escape returns to free flight with an equivalent displayed pose, after which
  mouse motion changes the camera again.
- Right-click targeting, reach, tweening, saving, and relaunch remain correct.
- Menu failure and retry behavior remain independent of world input.

Tests do not assert browser request ordering, listener counts, cursor coordinates,
window geometry, native calls, or a particular internal state machine. Native E2E
tests remain isolated from the user's desktop. Completion also requires a direct
playthrough of the changed flow in the running application.

## Non-goals

- No change to camera mathematics, movement speeds, interaction reach, orbit
  targeting, proof rules, save format, renderer, or tool semantics.
- No alternate browser-only game authority.
- No input abstraction, compatibility wrapper, native mouse service, or fallback
  interaction model.
