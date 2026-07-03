# Plan 17: The PiP companion — seeing where you are going

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A second, view-only viewport that shows the diagram you are working TOWARD, so proving is navigation instead of memory. In PROVE·forward it renders the backward side's current diagram (the meet target); in PROVE·backward, the forward side's; in REPLAY, the theorem's final state (rhs); in EDIT it is hidden. A toggle cycles hidden → PiP (corner inset) → split (half-width side by side).

**Design constraints:**
- The companion is REUSE, not new rendering machinery: its own `mkEngine` + `settleStep` + fit camera + `paint` + `drawShapes` on a second canvas, exactly the pipeline the main view uses. View-only: no hit-testing, no drags, no selection on the companion (clicks on it do nothing in this iteration).
- The companion's engine rebuilds only when its DIAGRAM identity changes (same `carryOver` warm-start discipline as replay stepping), never per frame.
- The INTERFACE OVERHAUL is queued right after this plan (user ruling: the chrome will be redone wholesale). Build the companion so the overhaul only touches placement/styling: one pure function decides WHAT it shows; one component owns the second canvas; zero coupling into the action menus.
- Boundary honesty carries over: the companion renders with the proper boundary for the side it shows (session sides and theorem rhs have boundaries — use them, exactly as the main view does).

### Task 1: Companion selection logic (headless)

**Files:** `src/app/companion.ts`: `companionFor(state) → { diagram, boundary, label } | null` where state carries mode/session/side/replay — pure, total, tested for every mode×side×presence combination (no session → null; replay → rhs + "goal" label; prove-forward → backward current + label "meeting: backward side"; etc.).
**Test:** `tests/app/companion.test.ts` — the full decision table, including the degenerate cases (replay at the last step: companion equals the displayed diagram — still shown, the label says so; backward side with a fresh session).

- [x] Logic + tests green; suite + tsc green. Commit.

**Findings (Task 1):** `companionFor` is one pure total function over `CompanionState = {mode, session, side, replay}`. Decision: EDIT→null; PROVE·forward→backward.current + rhs boundary, label `meeting: backward side`; PROVE·backward→forward.current + lhs boundary, label `meeting: forward side`; PROVE no-session→null; REPLAY→`diagramAt(stepCount)` (final rhs) + replay boundary, label `goal: final state`, independent of k so the last-step diagram IS the companion (still shown); REPLAY no-replay→null. Boundaries come from `sideBoundary`/`replay.boundary` verbatim — no new boundary logic. Tests assert diagram/boundary by object identity (airtight side selection) plus the exact label strings. 9 tests, suite 875 green, tsc clean.

### Task 2: The pane + e2e

**Files:** `src/app/shell.ts` — a second canvas (`#companion-canvas`) with its own engine/camera/rAF-coupled settle (share the main rAF: one `frame()` drives both paints); rebuild-on-identity-change with carryOver; the cycle toggle button (hidden → PiP → split; PiP = fixed-fraction corner inset, split = half width, plain CSS — the overhaul restyles later); a small text label from companionFor. Debug seam: `companion(): { visible, label, bodies } | null` for e2e.
**Test:** e2e — enter PROVE with goals: companion appears showing the OTHER side (seam: label + bodies > 0); apply a forward step: the main view changes, the companion doesn't rebuild (identity unchanged); toggle to split and back to hidden; REPLAY: companion shows the rhs while stepping.

- [ ] Pane + e2e green; full suite + tsc green. Commit.

### Task 3: Review + close

- [ ] Independent adversarial review: companionFor decision-table probes; the companion NEVER receives interaction (a click on it changes no state — pinned); engine-rebuild discipline (a step that keeps the companion diagram identical must not reseed its layout — pin via seam positions); replay sentinel.
- [ ] Plan-doc + memory sync; close. Next: the interface overhaul.
