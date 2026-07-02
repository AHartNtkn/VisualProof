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

- [x] Delete the repo-root lab/harness scratch (`render-lab*.{ts,html}`, `render-thm.*`, `shot-*.mjs`); the docs spec copy is the only survivor. Suite + tsc + e2e green.
- [x] Independent adversarial review: mutation probes on each law test (e.g., re-enable atom exitLine — law-4 test fails; leak text into term anatomy — law-2 fails; skip overlap projection — law-1 fails; desync anatomy stroke from wire stroke — law-5 fails; un-glow the bubble in Dark — law-6 fails); hunt for hit-test/geometry drift (a hit target must exist wherever something is painted); confirm live `settleStep` determinism (same diagram, same seed → same layout).
- [ ] Plan-doc sync; merge to main (branch `plan-13-render`); delete branch. The FEEL round (interaction/motion iteration with the user) starts after merge, in-app.

---

### Task 3 execution record (independent adversarial review)

Reviewer wrote none of the code under review (commits `1a97d0d`, `0564def`). Baseline before review: 689/689 suite, tsc clean, e2e 3/3.

**Part A — law-mutation probes** (each: mutate src → run → observe result → revert):

| # | Mutation | Expected | Result | Catching test |
|---|----------|----------|--------|---------------|
| 1 | Re-enable `exitLine` in `atomGeometry` | law-4 fails | FAILED as expected | `bend.test.ts` "emits no exit line (law 4)" |
| 2 | Emit a label at each term glyph position in `paint` | law-2 fails | FAILED as expected | `paint.test.ts` "law 2 — no text on lambda" |
| 3 | Skip the final overlap projection in `settle` | law-1 fails | **DID NOT FAIL** (finding below) | — |
| 4 | Hardcode anatomy arc width ≠ `wireW` | law-5 fails | FAILED as expected | `paint.test.ts` "law 5 — linework coherence" |
| 5 | Un-glow the Dark bubble ring | law-6 fails | FAILED as expected | `paint.test.ts` "law 6 — Dark glows the bubble ring" |
| 6 | Junction threshold `>=3` → `>=4` | law-7 fails | FAILED as expected | `wires.test.ts` junction trunk tangents + `hittest.test.ts` junction click (the bundled-theorem count test did not catch it — see note) |
| 7 | `boundaryExits` returns `[]` | law-3 + boundary tests fail | FAILED as expected | `paint.test.ts` "law 3" + `hittest.test.ts` frame-exit click |
| — | Inject `Math.random()*1e-9` into `settleStep` position | determinism test fails | FAILED as expected | `relax.test.ts` "deterministic incremental relaxation" (a raw seed-constant change would NOT fail it, and correctly so: same construction ⇒ same seed ⇒ same layout is still determinism; the test pins run-to-run reproducibility, which is the correct scope) |

Probe 6 note: the `relax.test.ts` law-7 count test derives its `expected` from the same `>=3` formula and runs only over the bundled theorems, which contain no exactly-3-endpoint wires — so the threshold change slipped past it. The constant is anchored by `wires.test.ts` and `hittest.test.ts`, which build an explicit 3-endpoint wire; law-7 remains guarded.

**Finding (fixed): law-1 containment was not pinned to its mechanism.** With `resolveOverlaps` removed from BOTH call sites (periodic in `settleStep`, final in `settle`), the ENTIRE view+app suite (117 tests) still passed. The three bundled theorem sides are sparse enough that soft repulsion alone keeps their region circles legal within EPS=0.5; a dense-diagram experiment showed 6 sibling cuts already overlap at full settle without projection (10 cuts → 4 overlaps). Fix: added `relax.test.ts` "holds for a dense sheet of sibling cuts (requires overlap projection)" — 10 sibling cuts × 3 nodes; it fails without `resolveOverlaps` (observed: `expected true to be false`) and passes with it. The projection is not dead code: it is load-bearing for dense sheets and for live drag/pin, which the sparse static cases did not exercise.

**Part B — independent hunt:**
- *Faithfulness to the reference (`render-lab8.ts`):* Hobby math (`hobbyRho`/`hobbyBezier`), junction trunk-tangent selection (`computeLegs`), minimal-circle subgradient descent (`recomputeRegions`), and overlap projection (`resolveOverlaps`) are line-for-line faithful. The lab's monolithic `relax(ticks)` loop was split into `settleStep` (one tick, `e.tick % 10` projection cadence — matches the lab's `t % 10`) + `settle` (budget then final projection); the `exitLine` law-4 fix is the only intended behavior change. No silent divergence found.
- *Hit/paint parity:* every painted target with an action is hittable — node discs, satellite discs (→ node), junction dots (→ wire), leg splines, frame exits (→ wire), region rings, and the ∃ stub. The ∃ stub was painted but had no hit test; added `hittest.test.ts` "a click on an existential stub resolves to its internal wire". The sheet frame is background (no action) — correctly not hittable.
- *Determinism:* verified the test pins reproducibility (injected 1e-9 noise → fails).
- *Live-loop safety:* added `relax.test.ts` "live-loop safety (bounded, non-diverging energy)" — per-frame `settleStep` with a pinned body stays finite and per-window movement decays (no NaN, no sustained oscillation).
- *Theme completeness:* every color/width in `paint.ts` comes from the `Theme` object; the only hex/rgba literals are inside the `LIGHT`/`DARK` definitions themselves. `canvas.ts` holds only device-pixel primitives (glow blur, tick length). No stray literals.
- *e2e:* the 3 specs drive the new pipeline through the live shell (`settleStep`/`paint`/`drawShapes`, `__vpaDebug` from the same module) — boots, term entry, end-to-end prove. 3/3 green.

**Result:** battery additions committed (`plan 13 task 3: review battery additions`). Final: 692/692 suite, tsc clean, e2e 3/3. Verdict: ISSUES-FIXED-APPROVED. Merge/branch-delete left to the team lead.
