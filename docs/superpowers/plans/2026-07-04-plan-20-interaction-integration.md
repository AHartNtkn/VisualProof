# Plan 20: Interaction Integration (the converged plan-19 vocabulary into production)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the shell's interaction layer wholesale with the verdict-converged vocabulary from plan 19's seven demo rounds: brush selection, direct construction gestures, the spawn cascade, dedicated rule mechanics, infer-first citation, derive-then-declare tracks, the scrubber-as-undo/redo, minimal chrome, and the view-only motion layers. Every round has a user verdict; nothing here is open design.

**Authority:** The reference implementations are the lab modules — `ui-lab/shared.ts` (brush, LabCtx, physics handles), `composite.ts` (EDIT gestures), `spawn.ts` (cascade), `verdict.ts` (PROVE moves + citation), `session5.ts` (cursor-based TrackLab), `chrome.ts` (mode machine + minimal chrome), `history.ts` (scrubber + zoom thumbnails), `round7.ts` (motion layers), plus `src/view/morph.ts` (already production). The verdict record is `2026-07-03-plan-19-interface-overhaul.md`; standing laws live in the memory files (`port-names-are-not-semantic`, `rendering-laws`, `loose-ends-are-bodies`, `backward-is-flipped-polarity`, `named-defs-never-inside-terms`). NO DUAL SYSTEMS: the shell's current interaction surface (button rows, click-wire-click-wire join, the two-phase target pickers, the un\* backward remnants if any resurface, the goal-snapshot buttons) is DELETED as each task lands — the lab vocabulary is not an alternate mode.

**Kernel/back-end status (already production, NOT in scope):** dual-replay theorems + orientation-gated appliers (backward redesign), `occurrenceSelection`, folded-comp instantiation acceptance, zero-endpoint wire bodies, orphaned-wire auto-delete semantics at the selection layer, `mkGridMorph`/`bendMaps`. This plan is the interaction/UI layer only.

**The laws as tests (Task 1's battery, referenced throughout).** Each law is pinned either as a vitest unit (pure logic: selection arithmetic, gesture-claim predicates, step construction) or as a Playwright e2e (pointer-driven gesture laws), whichever actually exercises it. A law without a test does not count as integrated.

*Selection & pointer (round 1 + later rulings):*
1. **Brush:** drag paints hit items into the selection (out of it when the stroke starts on a selected item); plain click toggles exactly one; void click clears; painting may START in the void.
2. **Hover never vanishes on selection:** unselected hover = the would-be-catch tint; selected hover = the selection tint darkens; wires included; readout appends "— selected".
3. **Ring band:** a MOVING brush claims a region only within ~1.5 world units of its ring; a stationary click claims the whole disc.
4. **Shift is selection-only:** with Shift held, no gesture (move, join, iterate, drag-anything) may claim the pointer.
5. **Ctrl+drag is physics-only:** repositions bodies in every mode, never touches the diagram, never emits a step.

*Construction, EDIT mode (rounds 2/2b + round-7 report):*
6. **Join:** drag a loose end onto another line joins them; J joins ALL selected lines (n-ary).
7. **Sever:** right-drag slash severs immediately (no second phase); double-click sever exists behind an options toggle, slash the default.
8. **Wraps:** W = one construction cut around the selection, Shift+W = bubble; selecting a cut plus its contents wraps the subtree ONCE (absorb-normalized); wholly-enclosed wires rescope INTO the new cut (the `edit.ts wrap()` fix — drawing a circle around a thing must mean the thing is inside). Proof-mode double-cut introduction remains a distinct rule mechanic.
9. **Delete (EDIT):** selected boundaries DISSOLVE (unselected contents propagate to the parent), selected contents die, multi-region selections work, and wires left with no endpoints are deleted along.
10. **Move:** dragging a selected node between regions reparents with wire-scope correction (wholly-owned wires travel; shared wires keep scope when valid, else tightest common ancestor); connected-wire physics continues live during placement while region boundaries retain their semantic membership.
11. **Spawn cascade:** right-STILL-click opens the cascade at the point (search row, λ-term entry, recents, namespace submenus); spawns land where clicked, inside cuts included; right-drag still slashes; the selection is untouched; Escape and any press outside close it without spawning.
11a. **Bound-predicate spawn:** the same contextual cascade exposes predicate atoms separately from named relation references whenever an existing bubble can bind them. The chosen binder is explicit when several enclosing bubbles are available; the atom's arity is derived from that binder, it is created inside the binder, and binder identity supplies its semantic color. No free arity field, invented relation name, or renderer-only color assignment is permitted.
12. **Disc labels:** a relation node's disc shows its name sans namespace (no arbitrary truncation of long defIds).

*Rule application, PROVE mode (rounds 3/4):*
13. **Dedicated mechanics, no consolidation:** Delete = contextual deletion — double-cut elim / vacuous dissolve / positive erasure / deiteration, chosen by the absorb-normalized selection; no "arbitrary secrets" (selecting both cuts of a double cut works).
14. **Drag-to-iterate:** dragging a selection toward legal regions glows them; release commits; MOVEMENT is required (a still click on a selected item toggles it off instead).
15. **Conversion:** double-click a term = quick normalize; head-normal and custom-target reachable from the same entry; the certificate plays as the connected grid morph (law 26).
16. **No duplicate move feedback:** a successful move is visible in the diagram and the authoritative history surface; no memory box, success message, chronicle, or second step display is added.
17. **Refusals:** kernel refusal text VERBATIM, beside the current pointer, auto-fading. The kernel's message is the UX copy — no paraphrase layer.
18. **Infer-first citation:** the citation menu lists ONLY theorems whose from-side occurs in the diagram AND whose occurrence contains the selection; a unique occurrence applies instantly (sel + args derived by the matcher); several = highlighted Tab/click cycling + Enter; argument wires are never hand-picked; closed theorems cite as empty-selection insertions; citation direction = region sign XOR track orientation.
19. **Instantiate:** named substitution stays FOLDED (the ref is spliced, never auto-expanded); only the relation is asked.

*Proof model (round 5 + backward redesign):*
20. **Derive-then-declare:** F/B start a forward/backward track from the current sheet; D declares (origin ⟹ here, or here ⟹ origin with the backward steps recorded as given); E exits to EDIT keeping the sheet; ONE ProofContext persists — a declared theorem is immediately citable.
21. **Backward is flipped polarity:** the backward track exposes the identical move vocabulary, flip-gated through the shared appliers; no backward-only code paths in the UI beyond the orientation boolean.
22. **Declare at the cursor:** declaring after a rewind uses the steps up to the cursor.

*History (round 6h):*
23. **Scrubber = undo/redo:** cursor-based; dragging time-travels the main view; the future is RETAINED (dashed ticks) and reachable by Ctrl+Shift+Z; a new move truncates it (linear model — the decided ruling); Ctrl+Z steps back.
24. **Zoom-to-change previews:** hovering anywhere on the bar pops the nearest tick's thumbnail, zoomed to the changed bodies (whole-diagram fallback for pure removals); no dead zones along the bar.

*Chrome (round 6):*
25. **Compass Aperture production chrome:** one compact north lifecycle capsule owns mode identity and entry; Indexed Ledger is an overlay that never resizes the canvas; view/session utilities are disclosed separately; the south temporal rail appears only outside Edit. Permanent generic button rows and the lab iframe compositor are not product chrome.

*Motion (round 7):*
26. **View-only, toggleable motion:** βη playback = `mkGridMorph` (the attachment invariant is already unit-pinned in `tests/view/morph.test.ts`; the pinned `mkGeomMorph` stays selectable per the user's instruction), input held during play, commit deferred to the final frame, speed 0.25–3×; transition ghosts (dying fade, born pulse); hover ease; each layer independently off-switchable; none of it ever touches diagram state (layer law).

---

### Task 1: The law battery + interaction core (brush, hover, physics handles)

**Files:** Create `src/app/interact/` — `brush.ts` (laws 1–5, ported from `ui-lab/shared.ts installBrush`: void-start painting, ring-band gate, shift purity, ctrl physics drag, hover-ease hook), `ctx.ts` (the InteractCtx seam the lab called LabCtx: mutate/undo-cursor/freeze/regionAt/legs/toast — backed by the real shell engine loop). Rebuild the shell's pointer routing on it; DELETE the shell's current click-selection code. `src/app/hittest.ts` gains the ring-band query (moving-brush hit ≠ click hit) — the disc-claims-everything behavior stays for CLICKS only.
**Test:** unit — selection arithmetic, ring-band predicate, shift/ctrl claim gates; e2e — laws 1, 2, 3, 4, 5 as pointer scripts (the plan-19 probe scripts are the reference; they become `tests/e2e` cases).

- [x] Battery written first and observed failing; core ported; battery green; suite + tsc + e2e green. Commit.

### Task 2: EDIT vocabulary (construction gestures, spawn cascade, real library)

**Files:** `src/app/interact/construct.ts` (laws 6–10 from `ui-lab/composite.ts` + `shared.ts deleteHits/orphanedWires`), `src/app/interact/spawn.ts` (laws 11/11a from `ui-lab/spawn.ts`, browsing the REAL loaded library and the invocation point's real enclosing binders — named relations and bound predicates remain distinct semantic entries); label rule (law 12) lands in paint's disc-label source. Fix `src/app/edit.ts wrap()` wire rescoping (law 8) — kernel-side edit helper, test-first. DELETE the shell's button-driven join/sever/wrap/delete UI.
**Test:** unit — wrap rescoping (the exact wholly-enclosed-wire case), deleteHits dissolve/orphan matrix, binder-option derivation and atom arity; e2e — slash sever, drag join, W/Shift+W, cascade open/spawn-in-cut/Escape/click-away, spawn a predicate bound to the only enclosing bubble, choose the intended binder when bubbles nest, and reparent drag.

- [x] **Bound-predicate spawn gap closed (2026-07-10):** the cascade derives every enclosing bubble innermost-first, keeps bound atoms distinct from named references, shows binder-hued circle entries, and highlights the exact bubble on hover with centralized cleanup. Accepted choices create a kernel atom carrying only region+binder, with arity-derived singleton wires, through ordinary edit history and click-local placement; invalid ancestry remains `mkDiagram`-rejected. Red/green receipts: focused Vitest + interaction ownership 41/41, TypeScript typecheck, and the actual-app construction suite 6/6 (unique and nested binders, distinct swatches, hover/leave/Escape cleanup, semantic binder identity, arity, and Undo). No physics source or physics test was touched.

### Task 3: PROVE vocabulary (dedicated mechanics, infer-first citation, tracks)

**Files:** `src/app/interact/moves.ts` (laws 13–17, 19 from `ui-lab/verdict.ts`, corrected by `docs/superpowers/specs/2026-07-10-proof-interaction-integration-design.md`: contextual Delete with orphan-riding erasure, drag-iterate, dbl-click normalize chain, pointer-local refusals, no duplicate feedback, folded instantiate — steps emitted through one orientation-aware sink over the real session), `src/app/interact/cite.ts` (law 18: occurrence matcher over the context's theorems, Tab-cycling). The existing `src/app/session.ts` track/dual application is retained as the sole step-history authority; the shell's two-phase proof pickers, `BackwardEntry`/`commitBackward`, manual citation-wire picking, click-target iteration, and any remaining directional special-casing are DELETED. Cursor-based history and declare-at-cursor remain Task 4.
**Test:** unit — contextual-Delete resolution matrix, citation context filter (occurs + contains-selection + direction), declare-at-cursor step slicing; e2e — the round-4 "exact failing gesture" (brush everything, cite, must apply), Tab-cycle ambiguity, a backward track using the same gestures, refusal copy verbatim on a gated move.

- [x] **Shared proving interaction integrated (2026-07-10):** one disposable `ProofMoveController` now owns explicit-right-click discovery, contextual Delete, proof wraps, drag-to-iterate targets, proof-mode normalization/conversion, matcher-filtered infer-first citation with inferred attachments and ambiguity cycling, folded named instantiation, relation folding, and transient overlays for both orientations. Deleted from production: `BackwardEntry`, `backwardEntries`, `commitBackward`, manual cite/un-cite wire pending states, click-target iteration pending state, and the shell's second proof palette builder. Existing track/dual session application remains the sole orientation-aware step/history authority. Fresh focused Vitest/architecture 27/27, TypeScript typecheck, and affected app Playwright 11/11 passed; the unrelated Ctrl-drag physics scenario and physics-heavy suites were deliberately excluded because no physics source changed.

### Task 4: Cursor history and Compass Aperture production chrome

**Files:** `src/app/session.ts` rebuilt around the single timeline model in `docs/superpowers/specs/2026-07-10-history-chrome-integration-design.md`; `src/app/interact/scrubber.ts` owns the disposable temporal rail; focused preview derivation/rendering moves into production; `src/app/shell.ts` composes the real Compass Aperture lifecycle, Indexed Ledger overlay, utilities, and temporal rail. Track and fixed-side front cursors are independent; theorem `replay.ts` remains read-only but uses compatible temporal presentation. DELETE destructive past-only histories, permanent generic rows, and any production dependency on the lab iframe compositor. The already-landed `mountShell.dispose()` migrates every new listener/preview owner.
**Test:** unit — timeline invariants, forward/backward application, independent fixed-side cursors, truncate-on-new-move, declare/assemble-at-cursor, scrubber mapping/disposal, change focus; e2e — full backward/forward/fixed lifecycle, scrubber drag + hover preview + redo reach + future truncation, replay coexistence, Compass mode/Library/utility ownership, stable canvas bounds.

- [x] **Cursor history and Compass production chrome integrated (2026-07-10):** tracks and both fixed-side fronts now own immutable `states + steps + cursor` timelines; Undo/Redo and rail dragging move the cursor without deleting future, new moves truncate at the cursor, and declaration/meet/assembly use cursor states and prefixes. A disposable production temporal rail presents proof and read-only replay history with past/current/future ticks, shortcut equivalence, nearest-tick dragging, and cached semantic zoom-to-change previews. The real shell now owns Compass lifecycle, Indexed Ledger overlay, utilities/help, theme-consistent Porcelain styling, and the south rail; permanent generic rows, replay navigation duplication, and iframe composition are absent. Focused non-physics validation passed: Vitest 28/28, TypeScript typecheck, and production Playwright 3/3 (ordinary lifecycle, stable overlay canvas bounds, cursor Undo/Redo/drag, preview cleanup, Library). The approved adjustable two-live-canvas fixed-side composition remains the next integration slice; this task preserves independent front cursors and labels the focused front without claiming the old toggle/companion fulfills it.

- [x] **Adjustable two-live-canvas fixed-side workspace integrated (2026-07-11):** one production `FixedSideWorkspace` now composes forward and backward `ProofFrontViewport`s over the single authoritative `ProofSession`. Both panes use the real `InteractiveViewport` and `ProofMoveController`, preserve independent engine/camera/zoom/selection/pin/cursor state, route pointer input by pane and keyboard/temporal input by visible focus, and share the 30–70% seam with double-click equalization. Canonical meet alone enables seam declaration; Compass/Indexed Ledger remain geometry-invariant overlays; sub-648px resize suspends locally until the window widens. Deleted from the product model: side-toggle controls, fixed-side companion behavior, companion-oriented tests, duplicated front history, and prototype/lab imports. The shell remains the single animation owner; theorem replay alone retains the companion. Focused non-physics validation covers pure geometry/routing, production move vocabulary, session/history, replay companion, type checking, and actual two-pane browser interaction.

### Task 5: Motion layers

**Files:** `src/app/interact/motion.ts` (law 26 from `ui-lab/round7.ts`: playConversion over mkGridMorph with the pinned-v1 toggle, ghosts via the engine mutate hook, hover ease through the brush's motionPrefs, the ⚙ panel). Input guard while playing; commit deferred.
**Test:** unit already pinned in `tests/view/morph.test.ts`; e2e — mid-play sampling (geometry interpolating, wires d=0, commit deferred, toggle works, speed slider).

- [ ] Failing e2e → port → green. Commit.

### Task 6: Teardown + adversarial review + merge

- [ ] Preserve the converged lab composite as the spec copy (`docs/superpowers/plans/2026-07-04-ui-lab-final/`: shared/composite/verdict/session5/chrome/spawn/history/round7 + the round pages' verdict index); then DELETE `ui-lab/` from the build and the repo-root probe scratch. Suite + tsc + e2e green after deletion (nothing in src may import ui-lab).
- [ ] Independent adversarial review: mutation probes per law (disable ring-band → law 3 e2e fails; let shift enter the move claim → law 4 fails; unfilter the citation menu → law 18 fails; paraphrase a refusal → law 17 fails; drop orphan-riding from erasure → law 9/13 fails; re-enable auto-expand instantiate → law 19 fails; make a motion layer mutate the diagram → law 26 fails); hit-target/paint drift check; determinism check on track replay.
- [ ] Plan-doc sync; merge (branch `plan-20-interaction`); delete branch.

---

**Queued design items (recorded, NOT in scope — each needs its own user round):**
- Anonymous-comprehension construction box: instantiate without a name via a miniaturized EDIT canvas (round-4 ruling).
- History-display placement refinements beyond the scrubber, if large proofs demand more than zoom-thumbs (round 6h left the door open).
