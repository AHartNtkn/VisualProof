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

## Development-server persistence follow-up

The direct production-window exercise exposed a development-server lifecycle defect: persisting a developer-authored order changed `game/content/orders.json`, which is also the build-time `?raw` catalog input, so Vite reloaded the complete webview and returned the user to Main Menu. `game/vite.config.ts`, the configuration discovered for the `vite game` command root, now excludes that exact runtime-content path from the development watcher. The catalog remains a normal build dependency, and the runtime publication path remains responsible for making a successful persisted revision live in the active session.

The regression spawns the installed Vite CLI with the same `vite game --host ... --port ... --strictPort` root/config discovery path as `npm run game`, then opens its HMR client in Chromium. It proves that changing an imported temporary `game/content/orders.json` preserves the same page lifecycle and starting imported bytes, then changes an ordinary source module and proves that the watcher and full-reload control path remain active.

### Follow-up evidence

- Focused RED (`npx vitest run --config vitest.config.ts tests/game/vite-content-watch.test.ts`) — expected failure through the real CLI discovery path before the game-root watch rule: the lifecycle counter changed from `1` to `2` after the catalog write.
- Focused GREEN (same command) — PASS: 1 test; the catalog write preserved lifecycle `1`, and the ordinary source control change advanced it to `2`.
- `npm run typecheck` — PASS.
- `npm run build:game` — PASS: 158 modules transformed, including the current catalog starting bytes.
- `cargo test --manifest-path src-tauri/Cargo.toml` — PASS: 37 Rust tests plus empty main/doc-test targets.
- `npm test` — the new watcher regression passed, while 8 existing exact-opening-catalog assertions failed because the root-owned direct-app exercise currently has `direct-manual-order` persisted in `game/content/orders.json`. That live manual state and its `/tmp/orchard-orders-before-direct.json` capture were left untouched as required. A clean full-suite rerun requires the root owner to return the catalog to its starting state through the application.
- `./scripts/check-game-desktop.sh e2e` — not run against the root-owned manual catalog state because those scenarios consume the checked-in catalog and would not validate the required four-order starting condition. The same catalog-state unblock is required.

The mandatory direct production-window rerun remains assigned to the root task owner. Automated Vite/Chromium evidence supplements but does not replace that exercise.
