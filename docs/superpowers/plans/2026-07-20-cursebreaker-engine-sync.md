# Curse-Breaker Current-Main Engine Integration Plan

> **For Codex:** Execute this plan in the current session with test-first checkpoints. Do not merge the unrelated Lean/formalization tree or retire the game boundary.

**Goal:** Replace the curse-breaker worktree's obsolete TypeScript proof model with `origin/main` at `d0c3eae`, migrate the game and its durable witnesses to authenticated `ProofAction`s, and expose all 26 retained rules through real game interactions.

**Architecture:** The synchronized kernel is the sole proof-semantic authority. Product-neutral controllers translate geometry into preflighted `ProofAction`s; the game router owns arbitration and vocabulary. Sessions and saves retain action histories, and completed artifacts retain the certified backward actions from which authenticated theorem contexts are rebuilt.

**Tech stack:** TypeScript 5, Vitest, Vite, Electron, JSON Schema, deterministic graph canonicalization.

---

## Task 1: Import current-main kernel contracts under red tests

**Files:**

- Modify/add/delete: `tests/kernel/diagram/**`, `tests/kernel/term/**`, `tests/kernel/rules/**`, `tests/kernel/proof/**`
- Exclude: `tests/kernel/formal/**`
- Modify/add/delete: `src/kernel/diagram/**`, `src/kernel/term/**`, `src/kernel/rules/**`, `src/kernel/proof/**`, `src/theories/**`
- Carefully merge: `src/view/{bend,canvas,index,morph,tromp}.ts`

1. Mechanically synchronize the non-formal TypeScript kernel tests from `35c0b6e..d0c3eae` before source changes.
2. Run the focused new suites and record the expected compile/runtime failures for missing actions, authenticated contexts, anchored-wire rules, inconsistent-cut elimination, spawn rules, certified deiteration, and port correspondence.
3. Mechanically synchronize the complete entangled TypeScript kernel and theories from current main.
4. Merge the current-main view primitives with the curse-breaker canvas changes; preserve game rendering behavior while selecting current diagram contracts.
5. Run `npm run typecheck` and the complete non-formal kernel suite. Diagnose failures at their source; do not add compatibility aliases for `insertion`, `endpointTransport`, fuel deiteration, or mutable contexts.
6. Commit the authoritative kernel slice once green.

## Task 2: Make `ProofAction` the only game history unit

**Files:**

- Modify: `src/game/types.ts`
- Modify: `src/game/session.ts`
- Modify: `src/game/controller-state.ts`
- Modify: `src/game/controller.ts`
- Modify: `src/game/interface/{mount,proof-surface,game-presentation-view,folio-projection}.ts`
- Tests: `tests/game/{session,controller,controller-completion,controller-artifact-completion}.test.ts` and relevant presentation tests

1. Replace fixture expectations with action-level timelines: one diagram state, undo notch, and move count per `ProofAction`, even when an action contains multiple steps.
2. Run those tests and confirm they fail against `GameStep`, `GameSteps`, and `applyGameSteps`.
3. Replace the game types and session transition with `ProofAction` and kernel `applyAction`, preserving allocation reservation and placement metadata.
4. Replace controller `applySteps` with one `applyProofAction` action and migrate every call site.
5. Delete the step-level types and helpers rather than aliasing them.
6. Run focused session/controller/presentation tests and typecheck; commit when green.

## Task 3: Rebuild authenticated catalog and completed-artifact ownership

**Files:**

- Modify: `src/game/content-loader.ts`
- Modify: `src/game/controller-state.ts`
- Modify: `src/game/artifact-theorem.ts`
- Modify: `src/game/progress.ts`
- Modify: `src/game/unlock.ts`
- Modify: dependent projections and fixtures
- Tests: `tests/game/{content-loader,artifact-theorem,artifact-dependency-replay,controller-completion,progress,unlock}.test.ts`

1. Add tests proving plain/fabricated contexts are rejected, catalog relations extend an authenticated base context, a completion retains its actual backward actions, and dependency contexts register completed theorems in completion order.
2. Run the tests to establish failure under the completed-ID set and synthetic empty theorem history.
3. Introduce `CompletedArtifact { puzzle, actions }` ownership in one insertion-ordered map and derive completed IDs/unlocks/artifact availability from its keys.
4. Build the catalog context with `EMPTY_PROOF_CONTEXT` plus `extendRelations` in authored definition order.
5. On completion, verify retained actions replay the authored start to canonical blank, construct the backward theorem, and register it with `registerTheorem`. Rebuild later contexts by sequential registration.
6. Replace all game/test plain context objects with authenticated constructors. Do not pass an authenticated context through a snapshot helper that loses its brand.
7. Run focused tests and typecheck; commit when green.

## Task 4: Replace save version 5 with authenticated action persistence

**Files:**

- Modify: `src/game/save.ts`
- Modify: persistence call sites
- Tests: `tests/game/save.test.ts` and controller persistence tests

1. Write failing tests for action timeline round-trip, ordered completed-action round-trip, sequential dependency registration, invalid completion replay, unavailable prerequisite, and rejection of version-5 step/bare-ID data.
2. Bump the save version. Serialize actions with the kernel action codec and completions as an ordered array of puzzle/action records.
3. Decode by fingerprint-checking, unlock-checking each completion against the prior prefix, replaying it to blank, and registering its theorem before later records. Decode active/replay timelines through the same action path.
4. Remove legacy step and completed-ID decoding entirely.
5. Run save/controller tests and typecheck; commit when green.

## Task 5: Migrate build-only content witnesses without changing authored content

**Files:**

- Modify: `content/schemas/validation.schema.json`
- Modify: `content/validation/*.json`
- Modify: `scripts/validate-game-content.ts`
- Add: focused migration/replay helper only if needed under `scripts/`
- Modify: validation-reader tests

1. Capture pre-migration canonical results for all 1,039 legacy moves in a temporary test artifact outside the repository. Add tests requiring the new sidecars to preserve action count and each action's canonical post-state.
2. Change the schema and validator to action arrays; flatten constituent steps when deriving `expectedRules`.
3. Replay every old solution in its original state. Replace 276 deiterations with `findDeiterationEvidence` output, convert the one binder object to `[]`, and wrap unchanged logical moves as one-step actions.
4. Replace three local general insertions with atomic multi-step spawn/structure actions that preserve their captured result. Replace the grouped branch-construction witness as a whole with an ordinary current-rule proof preserving its start, blank result, and user-action count; do not reproduce obsolete insertion intermediates.
5. Walk progression with authenticated completed-action records so theorem citations are registered only after their prerequisite proofs; separately enforce `availableArtifacts` declarations.
6. Run `npm run content:validate` and assert 109 puzzles, 109 solutions, 0 recognized states, 1,039 actions, and blank final diagrams.
7. Prove no diff under `content/manifest.json`, `content/puzzles`, `content/catalog`, `content/progression`, `content/guidance`, or `content/coverage` relative to `3b4c6f9`.
8. Commit the regenerated schema, validator, and sidecars.

## Task 6: Establish one shared interaction-authoring layer

**Files:**

- Add/modify: product-neutral interaction modules for connection, fission, copy, spawn, hit testing, and pure proof-action authoring
- Modify: `src/app/interact/**` to consume the shared layer where retained
- Modify: `src/game/interface/proof-moves.ts`
- Modify: `src/game/interface/proof-surface.ts`
- Modify: `src/game/interface/loupe/interact/{construct,hittest,spawn}.ts`
- Modify: `src/game/interface/{construction-loupe,artifact-drop,proof-motion}.ts`
- Tests: shared controller tests plus game proof-surface/controller tests

1. Synchronize current-main interaction tests and add game-native failing tests for gesture arbitration, passive/modifier routing, blur/visibility cancellation, action allocation, and current certificate/correspondence payloads.
2. Extract current-main geometry/lifecycle controllers so neither app nor game owns duplicate legality/certificate synthesis.
3. Replace the monolithic game shadow catalog and its local connection/copy/deletion/deiteration/normalization implementations with the shared action authoring plus game-specific labels, fixed orientation, nested-vacuous batching, and construction callbacks.
4. Replace the Insert prompt with the proof-spawn cascade. Migrate bound-predicate arity, occurrence selection naming, ordered binders, and port correspondence.
5. Preserve the game viewport's explicit selection vocabulary, mapping, physics, and zoom gates while adding passive sampling, modifier routing, spawn/fission placement, overlays, and lifecycle cancellation.
6. Remove stale construct-controller join/sever shadows while preserving the construction loupe's two-surface connection claim.
7. Run focused interaction, game, app, browser-independent, and typecheck suites; commit when green.

## Task 7: Add direct routes and exhaustive coverage for all 26 rules

**Files:**

- Modify: shared connection and sever gesture policy
- Modify: game proof router/surface overlays
- Tests: exhaustive rule-route and event-driven controller tests

1. Add a failing compile-time/runtime coverage table keyed by the exact `ProofStep['rule']` union. Each entry must drive a real input route, capture its emitted action, and successfully apply it in the intended backward context.
2. Add failing interaction tests for a selected-line context menu whose explicit endpoint rows produce one `wireSever` action with the labeled retained prefix.
3. Add failing interaction tests for dragging a closed witness output to a distinct same-wire non-output endpoint producing `anchoredWireSplit`; preserve same-wire output-to-output `headStrip` arbitration.
4. Add or adapt concrete routes for spawn, connection/contract, deletion including undecided inconsistent cuts, copy/iteration, double/vacuous introduction, conversion, fusion/fission, comprehension instantiate/abstract, theorem artifact drop, and relation fold/unfold.
5. Delete `GameProofAction`, Insert, endpoint transport, fuel deiteration, and all duplicated rule-authoring paths; keep only a thin game filter over shared action discovery where artifact citation ownership requires it.
6. Run the exhaustive coverage and lifecycle suites, then all game and app interaction tests; commit when green.

## Task 8: Prove conformance and absence of the displaced model

**Files:**

- Append only: `/tmp/visual-proof-assistant-curse-breaker-foundation-20260720.md`

1. Run `npm run typecheck`.
2. Run the complete non-formal Vitest suite in portable mode.
3. Run browser suites with required host permissions if sandbox-only listener/Chromium restrictions recur.
4. Run `npm run content:validate`, `npm run build:desktop`, and `npm run test:desktop-startup`.
5. Run `git diff --check` and verify authoritative content paths are unchanged from `3b4c6f9`.
6. Search source, tests, schema, and JSON for displaced names/shapes: `endpointTransport`, rule `insertion`, deiteration `fuel`, record binders, `GameStep`, `GameSteps`, `applyGameSteps`, step-shaped save timelines, plain proof-context objects, synthetic empty artifact theorems, and game imports from `src/app`.
7. Request independent code review focused separately on kernel parity, state/persistence authentication, and interaction completeness; repair all actionable findings.
8. Rerun every affected validation after review fixes.
9. Append `<conformance>` to the foundation record with owners, deletions, migrations, commands, and observed results. Do not alter its pre-action sections.
10. Use the branch-finishing workflow to report the final commit set and integration options.
