# Task 12 implementation report

## Outcome

The native test suite now covers the approved opening controls, four-order lifecycle, complete tutorial progression, and developer order-content workflow. The scenarios use the native X11 window, keyboard and pointer controls, persistent SQLite saves, and the checked-in order-content command path. OS-level mouse motion drives look input and an OS-level Backquote keypress drives developer mode; no synthetic DOM events are used.

Two application defects surfaced in native execution and were repaired at their owning boundaries:

- The developer-mode indicator now has its own selector, so mirroring the indicator does not hide the game root.
- A ledger-open observation completes the Double Cut explanation only while that instruction is active, so an earlier tool-acquisition visit cannot skip the explanation.

The developer scenario verifies draft cancellation, published tile and centered accepted-pot visual changes, changed delivery validation, remembered formula text, create/reload/delete lifecycle behavior, and exact restoration of `game/content/orders.json`. Cropped image evidence is supplemental to the native interactions, persisted state, and delivery outcomes.

## Automated evidence

- `npm test` — PASS: 210 test files, 1,541 tests.
- `npm run typecheck` — PASS.
- `cargo test --manifest-path src-tauri/Cargo.toml` — PASS: 37 Rust tests plus empty main/doc-test targets.
- `npm run build:game` — PASS: 158 modules transformed and the production web game built.
- `./scripts/check-game-desktop.sh e2e` — PASS from a fresh build and private save roots:
  - controls: 1 passing;
  - order-loop play: 1 passing;
  - order-loop reload: 1 passing;
  - order-loop verify: 1 passing;
  - tutorial progression: 1 passing;
  - developer orders: 1 passing;
  - the developer content byte comparison passed.
- `git diff --check` — PASS.
- `git diff -- game/content/orders.json` — empty after the developer scenario.

## Remaining required evidence

The mandatory human-style direct exercise in the production desktop application remains pending for the root task owner, as assigned. This report does not treat the native scripts or their image assertions as a substitute for that pass. The exact remaining evidence is Task 12 step 6: create and reload a tutorials-enabled orchard in `npm run dev:game`, exercise the listed controls and adjacent states through the visible application, inspect the complete UI after each transition, and repeat any affected flow if a defect is found.
