# Task 12 implementation report

## Outcome

The native test suite now covers the approved opening controls, four-order lifecycle, complete tutorial progression, and developer order-content workflow. The scenarios use the native X11 window, keyboard and pointer controls, persistent SQLite saves, and the checked-in order-content command path. OS-level mouse motion drives look input and an OS-level Backquote keypress drives developer mode; no synthetic DOM events are used.

Two application defects surfaced in native execution and were repaired at their owning boundaries:

- The developer-mode indicator now has its own selector, so mirroring the indicator does not hide the game root.
- A ledger-open observation completes the Double Cut explanation once `apply-double-cut` is complete and `double-cut-explained` is incomplete. That durable gate records the real action while tutorials are disabled without allowing an earlier ledger visit to skip the explanation.

The developer scenario verifies draft cancellation, published tile and centered accepted-pot visual changes, changed delivery validation, remembered formula text, create/reload/delete lifecycle behavior, and exact restoration of `game/content/orders.json`. Cropped image evidence is supplemental to the native interactions, persisted state, and delivery outcomes.

The native save-evidence reader now applies SQLite's five-second busy timeout to each read-only connection. This keeps direct persisted-state assertions authoritative while allowing an in-flight application transaction to finish instead of producing a transient lock failure.

## Automated evidence

- `npm test` — PASS: 211 test files, 1,542 tests.
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

## Direct production-window evidence

The root task owner completed the mandatory human-style exercise in the production `npm run dev:game` window through native controls. A saved formula edit remained in the active ledger for more than two seconds with no Vite reload, and reopening the editor showed the saved value. The content workflow also covered a second no-prerequisite order, accepting an authored and manual order from one pose, observing two Active tiles, abandoning the authored order, and confirming the Active list became empty after the manual-content lifecycle.

Adjacent state checks covered tutorial and developer-tool toggles, resuming the re-enabled tutorial at `Select the tree`, returning to Main Menu, and reloading the orchard. The tutorial state and all three acquired tools persisted across that reload. The exercise returned `game/content/orders.json` exactly to its repository bytes, and the worktree was clean before the final automated matrix.

## Development-server persistence follow-up

The direct production-window exercise exposed a development-server lifecycle defect: persisting a developer-authored order changed `game/content/orders.json`, which is also the build-time `?raw` catalog input, so Vite reloaded the complete webview and returned the user to Main Menu. `game/vite.config.ts`, the configuration discovered for the `vite game` command root, now excludes that exact runtime-content path from the development watcher. The catalog remains a normal build dependency, and the runtime publication path remains responsible for making a successful persisted revision live in the active session.

The regression spawns the installed Vite CLI with the same `vite game --host ... --port ... --strictPort` root/config discovery path as `npm run game`, then opens its HMR client in Chromium. It proves that changing an imported temporary `game/content/orders.json` preserves the same page lifecycle and starting imported bytes, then changes an ordinary source module and proves that the watcher and full-reload control path remain active.

### Follow-up evidence

- Focused RED (`npx vitest run --config vitest.config.ts tests/game/vite-content-watch.test.ts`) — expected failure through the real CLI discovery path before the game-root watch rule: the lifecycle counter changed from `1` to `2` after the catalog write.
- Focused GREEN (same command) — PASS: 1 test; the catalog write preserved lifecycle `1`, and the ordinary source control change advanced it to `2`.
- `npm run typecheck` — PASS.
- `npm run build:game` — PASS: 158 modules transformed, including the current catalog starting bytes.
- `cargo test --manifest-path src-tauri/Cargo.toml` — PASS: 37 Rust tests plus empty main/doc-test targets.
- `npm test` — PASS after the direct exercise restored the catalog: 211 test files, 1,542 tests, including the watcher regression and exact four-order assertions.
- `./scripts/check-game-desktop.sh e2e` — PASS after the read-only SQLite connection adopted the busy timeout: controls, all three order-loop phases, tutorial progression, developer orders, and exact content-byte comparison.
- Direct `npm run dev:game` rerun — PASS: the saved edit remained in the active ledger without a reload, and the terminal emitted no Vite page-reload event for the content write.

The automated Vite/Chromium evidence supplements the completed direct production-window exercise; it does not substitute for it.

## Disabled-tutorial ledger follow-up

The composed ledger input boundary now derives the `ledger-opened` tutorial observation from completed milestone state rather than the currently visible instruction. This preserves the rule that real actions performed while tutorials are disabled still record milestones.

The native regression completes and applies Double Cut, disables tutorials, opens the ledger through the production Tab input, closes it, and re-enables tutorials. It then verifies that `double-cut-explained` is persisted and that the visible flow advances to `Acquire Iteration from the ledger.` This is automated native evidence; no additional direct production-window exercise is claimed for this follow-up.

- Native RED (`./scripts/check-game-desktop.sh e2e`) — expected failure before the durable gate: after re-enabling tutorials, the composed scenario received the Double Cut explanation instead of Iteration acquisition.
- Native GREEN (same command) — PASS: controls, all three order-loop phases, the amended tutorial progression, developer orders, and exact content-byte restoration.
- `npm test` — PASS: 211 test files, 1,542 tests.
- `npm run typecheck` — PASS.
- `npm run build:game` — PASS: 158 modules transformed.
- `git diff -- game/content/orders.json` — empty after the native matrix.
