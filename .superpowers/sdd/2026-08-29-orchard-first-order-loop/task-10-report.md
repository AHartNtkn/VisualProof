# Task 10 report — native order loop, browser playtest, and durable contract

## Status

The repeatable production-native order-loop scenario and durable design contract
are implemented and the complete automated matrix passes. Direct native and
browser playtesting were performed through visible controls, but neither direct
surface could complete the entire loop in this environment. The exact blockers
are recorded below, so this task is not reported as fully complete.

No production defect was found and no production file was changed.

## Files

- `game/e2e/order-loop.e2e.ts` — two-process native play/reload scenario using
  WebDriver pointer and keyboard actions plus read-only durable-state assertions.
- `game/e2e/native.ts` — read-only order, reputation, and tree-ID inspection;
  shared database opening; canvas/tween evidence helpers.
- `game/wdio.conf.ts` — registered the `order-loop` native scenario on port 4550.
- `scripts/check-game-desktop.sh` — controls receives a private root; order-loop
  play and reload receive a second shared private root in separate processes.
- `docs/orchard-game-design.md` — current two-tool, iteration/citation,
  duplication, catalog, player-chosen pot, persistence, and future-deiteration
  contract.
- `.superpowers/sdd/2026-08-29-orchard-first-order-loop/task-10-report.md` — this
  evidence report.

Extra Task 10 production files: none.

## RED/GREEN record

1. The new scenario was written before its save helpers. `npm run typecheck`
   failed on missing `storedOrder`, `storedReputation`, and `storedTreeIds`.
   Adding read-only SQLite helpers made typecheck green.
2. Early native runs failed at real interaction boundaries: WebKit pointer-lock
   look, free-reticle versus pointer offsets, tween sampling, pot occlusion,
   pot-versus-ground targeting, and branch targeting. Each RED retained the
   production interaction; the scenario was corrected to move the free camera
   so the production reticle ray passes through the intended visible target.
3. Reordering the final scenario to the requested legal-same-tree then rejected
   cross-tree sequence produced RED at the grown tree's former centerline. The
   grown side-branch point is now transformed from branch-local coordinates by
   the duplicate's production placement facing, obtained from the displayed-view
   contract. No save value controls gameplay input.
4. A reload run exposed boundary sensitivity in test positioning. The reticle
   helper now stands seven horizontal units from a target while production reach
   remains authoritative.
5. Final GREEN: controls, order-loop play, and order-loop reload all pass in
   separate native processes; all seven stress scenarios pass.

No test-only gameplay control, injected DOM event, page evaluation, fallback
transport, proof history, load-time re-verification, or generated-save edit was
introduced.

## Native automated phases and evidence

The `play` process creates `Order Loop`, moves in free flight, enters orbit with
a primary pointer action, changes the orbit view, returns to free flight, opens
the catalog with `Tab`, and accepts from the player's captured view. Read-only
SQLite inspection proves the accepted pot is exactly six horizontal units ahead,
the only tree is `tree-0000`, and reputation is 0.

The separate `reload` process loads the same private root and proves the accepted
pot persisted. Through native controls it swaps with `1`, takes the source whole
tree, duplicates onto ground, proves a fresh ID and preserved source, applies
Double Cut, performs legal same-tree proper-subtree iteration, rejects the next
proper subtree against the original tree while retaining it, clears it with
`Escape`, rejects the mutated duplicate at the pot without changing order,
reputation, tree IDs, or source, grows the exact theorem on the separate original,
delivers a whole-tree citation, and proves Completed/reputation 1/null pot/source
preservation. It then inspects the Completed catalog and reloads once more in the
same process to prove the durable outcome. The script-level play and reload runs
are separate native application processes sharing one private data root.

Final wrapper result:

```text
controls.e2e.ts: 1 passing (5.8s)
order-loop play: 1 passing (1.4s)
order-loop reload: 1 passing (12s)
Spec Files: 1 passed in each process; wrapper exit 0
```

## Direct native observations

`npm run dev:game` ran in a visible 1280×720 native X11 window against
`/tmp/orchard-task10-native.hgsjRc`. All actions used actual `xdotool`
pointer/keyboard input; screenshots inspected the complete visible HUD, world,
catalog, focus/engagement boundary, and feedback after each primary transition.

Observed directly:

- create, free movement/look, orbit, `Escape`, `Tab`, accept, visible pot, stop,
  restart, load, and persistent accepted pot;
- catalog abandonment and re-acceptance from a distinct player-chosen view;
- `1` tool swap, whole-tree pickup, free ground duplication with a fresh tree,
  source retained, Double Cut on the duplicate, and proper-subtree pickup;
- rejected cross-tree proper-subtree iteration with the cutting retained;
- `Escape` clearing, legal same-tree iteration with visible growth;
- whole mutated duplicate delivery mismatch with accepted pot, reputation 0, and
  held cutting retained;
- separate original source grown to the exact Double Cut shape;
- delivery rejecting a proper subtree with `delivery requires a whole tree
  cutting`, leaving the order accepted and reputation 0.

Direct-native blocker: WebKitGTK pointer lock recenters OS-injected pointer motion
after it is observed. That made repeated `xdotool` aiming alternate around the
very narrow root/proper-subtree distinction and prevented a stable final
whole-root pickup and completion. The run therefore did not directly observe
Completed/reputation 1/reload. This limitation is specific to the direct OS-level
input surface; the native WebDriver production scenario performs those same
pointer/keyboard interactions successfully.

Read-only inspection of the final direct-native save recorded the incomplete
state rather than a success-shaped result: order `accepted`, reputation 0, pot
present, original `tree-0000` at diagram 2, and two manually created duplicates.

## Direct HTTP browser playtest

`npm run playtest:game` ran with a private save root and its production script
provided `VITE_ORCHARD_SAVE_TRANSPORT=playtest-http`, service URL, and bearer
token. The in-app Browser opened `http://127.0.0.1:1420/`; no fallback transport
was used.

Visible Browser actions created `Browser Direct`, opened the catalog, accepted,
abandoned, re-accepted, reloaded, selected the saved slot, and reopened the
catalog. The accepted order and reputation 0 persisted across reload. Read-only
SQLite evidence after the run was:

```text
slot: f3a6108a-9f63-4e3f-aef7-617d15b1827b (Browser Direct)
order: accepted; pot: (0, 2), yaw 0
reputation: 0
trees: tree-0000 only
```

Browser blocker: every visible click intended to engage the world returned the
Chromium UI error `Could not begin play: If you see this error we have a bug.
Please report this bug to chromium.` The in-app Browser visibility capability
also returned `IAB visibility is not supported in a subagent thread`. Therefore
direct browser duplication and completion were unavailable and are not claimed.

The initial sandboxed HTTP launch also failed to bind `127.0.0.1:1421` with
`Operation not permitted`; the approved unsandboxed production playtest launch
then served successfully.

## Full automated validation matrix

All requested commands exit 0 on the task worktree:

```text
npm test
  194 test files passed; 1432 tests passed; duration 108.31s

npm run typecheck
  tsc --noEmit; exit 0

npm run build:game
  133 modules transformed; production game bundle built in 1.38s
  largest bundle 738.31 kB (size warning only)

cargo test --manifest-path src-tauri/Cargo.toml
  library: 26 passed, 0 failed; main/doc targets: 0 tests; exit 0

npm run emit:game-saves
  emitted 8 ordinary saves

git diff --exit-code -- game/generated-saves
  no output; exit 0

./scripts/check-game-desktop.sh e2e
  controls 1/1; order-loop play 1/1; order-loop reload 1/1; exit 0

./scripts/check-game-desktop.sh stress
  10:    visible 10,  full 6,  reduced 4,   marker 0,  culled 0,    p95 18ms
  50:    visible 37,  full 15, reduced 22,  marker 0,  culled 13,   p95 18ms
  100:   visible 54,  full 15, reduced 39,  marker 0,  culled 46,   p95 18ms
  250:   visible 112, full 15, reduced 97,  marker 0,  culled 138,  p95 18ms
  500:   visible 193, full 15, reduced 178, marker 0,  culled 307,  p95 18ms
  1000:  visible 372, full 15, reduced 357, marker 0,  culled 628,  p95 18ms
  2000:  visible 489, full 15, reduced 394, marker 80, culled 1511, p95 18ms
  all seven spec files passed; exit 0
```

The stress-10 and stress-2000 raw comparison samples were also emitted:
10 raw p95 18ms/build 14ms/draw calls 752/geometries 667; 2000 raw p95
291ms/build 1290ms/draw calls 48673/geometries 44003.

Final `git diff --check` and the generated-save diff check both exit 0.

## Durable contract audit

The current design document now states:

- exactly two tools, swapped by `1`;
- Double Cut as a one-stage secondary action and Iteration as a two-stage action;
- ordinary proper-subtree iteration only within the same tree;
- whole-tree trusted library citation at permitted polarity without proof replay;
- free whole-tree ground duplication with a fresh ID and preserved source;
- `Tab` catalog with one starter order and free abandonment;
- a player-chosen pot exactly six horizontal units ahead of the captured view;
- load trusting the standing library without re-verification or proof histories;
- deiteration as a separate future tool.

## Self-review and concerns

- The diff is confined to the five task-owned implementation/documentation files
  plus this required report. No production module or generated save changed.
- Read-only SQLite helpers validate durable state but never select or authorize a
  gameplay action. Native actions use only WebDriver pointer/keyboard input and
  the existing visible/root data contract.
- The scenario inspects camera mode, engagement, item, cutting, catalog, order,
  reputation, feedback, tree identity/diagram, pot, save idle state, and error
  state around every primary and adjacent transition.
- The automated deliverable is green. Completion of the direct native and direct
  browser requirements remains blocked by the two environment limitations above.
