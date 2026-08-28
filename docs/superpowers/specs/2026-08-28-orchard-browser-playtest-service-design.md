# Orchard Browser Playtest Service Design

## Goal

Make the production Orchard frontend usable in an ordinary local browser for
direct playtesting while preserving the existing Rust `SaveStore` as the sole
persistence authority.

## Controlling decisions

- SQLite save files, their exact current structure, validation, transactions,
  diagram interning, fixture generation, and per-slot isolation remain owned by
  `src-tauri/src/save_store.rs`.
- Browser playtesting adds a transport to that authority. It does not add an
  in-memory, IndexedDB, local-storage, fixture, or fallback save implementation.
- Desktop builds select Tauri IPC. Browser-playtest builds select HTTP. The
  frontend never probes one transport and falls back to another.
- The browser service binds only to `127.0.0.1`, requires a per-launch token,
  permits only the configured Vite origin, and exposes no explicit filesystem
  destination or deletion operation.
- Player input and camera behavior do not gain an alternate path to accommodate
  a browser-control limitation. Relative input activates free-flight controls,
  but world opening, rendering, and persistence remain available when it is
  unavailable; the ordinary in-world resume cue explains how to retry it.

## Architecture

### Shared persistence authority

`SaveStore` continues to implement list, create, load, update-tree, and
update-camera. Tauri commands remain thin calls into those methods. A new Rust
playtest server exposes the same five operations and calls the same methods.
Neither transport validates or transforms save semantics beyond decoding its
wire request and encoding the store result.

The playtest server receives its save directory, port, permitted origin, and
token explicitly at launch. The repository playtest command supplies a
git-ignored save directory so browser testing does not modify desktop player
saves or tracked generated fixtures.

### Frontend transport selection

`src/game/save-client.ts` retains the single public `SaveClient` contract and
the single response-decoding path. It gains a narrow transport interface that
can perform the five wire operations.

The production desktop build constructs the transport from Tauri `invoke`.
The browser-playtest build constructs the transport from `fetch`, using build
configuration supplied by the playtest launcher. Unsupported or incomplete
configuration fails at startup with a concrete error. There is no runtime
capability detection and no retry through another transport.

### Local service boundary

The Rust server provides five JSON POST routes beneath
`/__orchard_playtest/save/`:

- `list`
- `create`
- `load`
- `update-tree`
- `update-camera`

Every request must include the per-launch token. CORS permits only the exact
configured Vite origin and the token/content-type headers. The server rejects
all other origins and credentials. It binds an explicit loopback socket and
never listens on a wildcard address.

The launcher owns both child processes. It generates the token, starts the
Rust service, starts Vite with the explicit browser transport configuration,
and terminates the service when Vite exits.

## Error behavior

- Store errors retain their current user-facing messages.
- Transport failures report that the browser playtest save service is
  unavailable; they do not invoke desktop IPC.
- Invalid tokens, origins, request bodies, and route parameters receive an
  HTTP error without touching the store.
- One invalid or corrupt slot remains listable with its per-slot load error;
  other slots remain usable through the existing `SaveStore::list` behavior.

## Validation

Rust tests exercise each HTTP route against a real `SaveStore` in a temporary
directory, including authentication rejection and persistence across a fresh
store instance. TypeScript tests prove that each frontend operation uses the
selected transport and retains the existing strict response decoding.

After automated validation, direct browser playtesting must create a slot,
load the world, use the tool, inspect camera mode and pose, enter and leave
orbit, reload the page, and load the persisted slot. Each observed defect is
repaired and the same interaction is repeated. If the available browser cannot
provide relative input, the world remains available with its resume cue; the game
does not gain alternate controls.
