# Plan 13: Rendering Integration (the converged lab engine into production)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the old view layer wholesale with the design-converged renderer: the round-8 lab engine (bodies + junction bodies + satellite constants, rotation relaxation, minimal enclosing circles, hard containment projection, Hobby-spline wires with junction trunk tangents, sheet frame with boundary exits) and the two first-class themes (Light/Manuscript, Dark/Slate). User verdict: "good to integrate."

**Authority:** The executable spec is `docs/superpowers/plans/2026-07-02-render-lab-final/render-lab8.ts` (engine + painter + both theme objects, converged over 8 user-judged rounds). The design laws are in the memory file `rendering-laws.md` — every law becomes a test in this plan. NO DUAL SYSTEMS: `src/view/physics.ts`, `scene.ts`, `display.ts`, and the parts of `canvas.ts`/`bend.ts` the new engine supersedes are DELETED, and every consumer (shell, hittest, actions/session hover paths, e2e debug seam) moves to the new engine. The lab pages (`render-lab*.ts/html`, `render-thm.*`, `shot-*.mjs` at repo root) are deleted at the end — the preserved spec copy stays in docs.

**The laws as tests (Task 1's battery, referenced throughout):**
1. Containment: after settle+projection, no two region circles intersect (property-checked over every bundled theorem side and relation body).
2. No text on λ: the display list contains label items ONLY for named discs (refs, satellite constants) — never positioned over term anatomy; term structure emits zero text.
3. Boundary honesty: every boundary wire of a rendered side produces exactly one frame exit; no internal loose end is drawn for boundary wires; genuine singleton internal wires get the ∃ stub.
4. Refs/atoms: exactly one leg per port; no vestigial exitLine for non-term nodes (fix `atomGeometry` at the source — it currently emits one).
5. Linework coherence: wires and term anatomy share stroke color/width per theme (single source in the theme object; test by inspecting emitted styles).
6. Color codes binder identity only: atom strokes and bubble rings derive from the per-bubble hue map; in Dark, bubble rings AND atoms glow in their hue (the round-8 correction).
7. Junctions: every ≥3-endpoint wire yields one junction body; unary nodes never show two legs.

---

### Task 1: The engine (`src/view` replacement, kernel-side pure)

**Files:** Create `src/view/engine.ts` (model: Body/Junction/Satellite, mkEngine from Diagram+boundary), `src/view/relax.ts` (forces, rotation, cohesion, minimal-circle regions, overlap projection; exports both `settleStep` (incremental, for live app use) and `settle` (budgeted loop)), `src/view/wires.ts` (computeLegs with junction trunk tangents, Hobby velocity + leg geometry, boundary exits, ∃ stubs — geometry only, returns paths), `src/view/paint.ts` (display list from engine state + Theme; Theme type + the two theme objects), `src/view/canvas.ts` (extend drawShapes for the new shape kinds: bezier path, gradient-filled circle, glow attributes). Delete `src/view/physics.ts`, `src/view/scene.ts`, `src/view/display.ts`; `bend.ts`/`tromp.ts` stay (term anatomy geometry) but `atomGeometry` stops emitting `exitLine` (law 4) — with its knock-on fix at every consumer the compiler surfaces.
**Test:** `tests/view/engine.test.ts`, `relax.test.ts` (laws 1, 7 as properties over the bundled theory), `wires.test.ts` (Hobby control arms, junction tangent continuity: the two trunk tangents at a junction differ by π), `paint.test.ts` (laws 2, 3, 5, 6 by display-list inspection under both themes). Port the lab code faithfully — behavior changes only where the plan says (exitLine fix); the lab file is the reference implementation.

- [ ] Law battery written first and observed failing (module absence / old-renderer behavior), engine ported, battery green; full suite + tsc green (old-module deletion fallout resolved at every consumer — no wrappers). Commit.

### Task 2: App integration

**Files:** `src/app/shell.ts` (render loop drives `settleStep` live; pan/zoom against the new view transform; theme toggle UI persisted in the session; drag = pin body + relax around it), `src/app/hittest.ts` (rebuilt over engine geometry: node discs, satellites, junction dots, region rings, frame exits), hover behavior (binder-hue tether replaced by the standing law-compatible equivalent: hovering an atom or bubble highlights the WHOLE binder group — same hue family, brighter), `src/app/actions.ts`/`session.ts` untouched semantically (selection model unchanged — ids are ids).
**Test:** hittest tests over engine geometry; a shell contract test (theme toggle changes emitted styles; drag pins). `npm run e2e` updated where the debug seam changed.

- [ ] Failing tests → integrate → green; e2e 3/3. Commit.

### Task 3: Cleanup + review + merge

- [ ] Delete the repo-root lab/harness scratch (`render-lab*.{ts,html}`, `render-thm.*`, `shot-*.mjs`); the docs spec copy is the only survivor. Suite + tsc + e2e green.
- [ ] Independent adversarial review: mutation probes on each law test (e.g., re-enable atom exitLine — law-4 test fails; leak text into term anatomy — law-2 fails; skip overlap projection — law-1 fails; desync anatomy stroke from wire stroke — law-5 fails; un-glow the bubble in Dark — law-6 fails); hunt for hit-test/geometry drift (a hit target must exist wherever something is painted); confirm live `settleStep` determinism (same diagram, same seed → same layout).
- [ ] Plan-doc sync; merge to main (branch `plan-13-render`); delete branch. The FEEL round (interaction/motion iteration with the user) starts after merge, in-app.
