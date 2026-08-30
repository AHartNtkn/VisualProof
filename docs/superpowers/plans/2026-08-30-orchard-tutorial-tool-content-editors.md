# Orchard Tutorial and Tool Content Editors Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add permanent live developer editing for tutorial instructions and tool names/descriptions, and make the opening tutorial teach every required control.

**Architecture:** Split editable copy from immutable tutorial progression and tool mechanics by introducing strictly decoded, live content revisions backed by checked-in JSON. Publish whole candidate revisions through the existing native/playtest authored-content boundary, then reuse the established foreground editor and pause ownership contract for two focused editors.

**Tech Stack:** TypeScript, DOM APIs, Vite, Vitest, Rust, Tauri, Axum, WebdriverIO

**Spec:** `docs/superpowers/specs/2026-08-30-orchard-tutorial-tool-content-editors-design.md`

## Global Constraints

- Developer Tools remains an application setting and the only gate for developer interactions.
- Tutorial progress and tool mechanics remain keyed by stable semantic IDs, never editable prose.
- Permanent edits write checked-in game content and become live only after the permanent write succeeds.
- `Escape` opens Pause and preserves the foreground editor and draft; `Backspace` closes the foreground editor only outside editable text.
- Player progress, accepted orders, and world state are not changed by tutorial or tool copy editing.
- Launch Tool remains absent from every player and developer tool surface.
- Tests prove behavior and responsibility boundaries, not source substrings or exact replaceable prose.
- User-facing changes require direct in-app exercise with real controls before completion.

## Requirement Delta

- Spec: Content authority — editable tutorial and tool copy live in separate strictly decoded checked-in JSON documents.
- Spec: Tutorial instruction content — every visible instruction teaches the actual control needed for its milestone.
- Spec: Tutorial editor interaction — developer mode exposes a clickable current tutorial card and permanent live text editor.
- Spec: Tool content and editor interaction — both Tools views show descriptions and expose permanent name/description editing in developer mode.
- Spec: Permanent publication — tool and tutorial copy use atomic whole-document publication without writing player saves.
- Implementation-local: Enabling developer mode releases active pointer capture so the approved tutorial-card click is reachable; this is a reversible input-surface mechanism and changes no progression or content semantics.
- Implementation-local: Separate focused tutorial and tool editor controllers share the established DOM contract rather than generalizing the diagram-specific order editor; this preserves the specified behavior with smaller ownership boundaries.

---

### Task 1: Live tutorial and tool content authorities

**Files:**
- Create: `game/content/tutorial.json`
- Create: `game/content/tools.json`
- Create: `src/game/tutorial/content.ts`
- Create: `src/game/tools/content.ts`
- Modify: `src/game/tutorial.ts`
- Modify: `src/game/tools.ts`
- Test: `tests/game/tutorial-content.test.ts`
- Test: `tests/game/tool-content.test.ts`
- Test: `tests/game/tutorial.test.ts`
- Test: `tests/game/tools.test.ts`

**Interfaces:**
- Consumes: existing `TutorialMilestoneId`, tutorial milestone ordering, `ToolId`, and immutable tool mechanics.
- Produces: `TutorialContentRevision`, `LiveTutorialContent`, `openingTutorialContent`, `decodeTutorialContent(raw: unknown)`, `ToolContentRevision`, `LiveToolContent`, `openingToolContent`, and `decodeToolContent(raw: unknown)`; lookup methods throw for absent semantic IDs.

- [ ] **Step 1: Write failing decoder and authority tests**

```ts
expect(decodeTutorialContent(validTutorialRecords).definition('move').text).toContain('W')
expect(() => decodeTutorialContent(withMissingVisibleMilestone)).toThrow(/missing/i)
expect(() => decodeTutorialContent(withBlankText)).toThrow(/blank/i)
expect(decodeToolContent(validToolRecords).definition('iteration').description).toMatch(/right-click/i)
expect(() => decodeToolContent(withChangedId)).toThrow(/unknown|missing/i)
expect(() => decodeToolContent(withBlankDescription)).toThrow(/blank/i)
```

- [ ] **Step 2: Run the focused tests and confirm RED**

Run: `npm test -- --run tests/game/tutorial-content.test.ts tests/game/tool-content.test.ts tests/game/tutorial.test.ts tests/game/tools.test.ts`

Expected: FAIL because the content modules and JSON-backed copy authorities do not exist.

- [ ] **Step 3: Implement strict immutable revisions and live publishers**

```ts
export type TutorialContentDefinition = { readonly milestoneId: VisibleTutorialMilestoneId; readonly text: string }
export type ToolContentDefinition = { readonly id: ToolId; readonly name: string; readonly description: string }

export class LiveTutorialContent {
  public constructor(private revisionValue: TutorialContentRevision) {}
  public get current(): TutorialContentRevision { return this.revisionValue }
  public publish(next: TutorialContentRevision): void { this.revisionValue = next }
}
```

Keep prerequisite/event functions in `src/game/tutorial.ts` and category/capacity/color/silhouette in `src/game/tools.ts`. Resolve instruction text and tool names/descriptions through the live content revisions without copying those editable fields back into mechanics.

- [ ] **Step 4: Author novice-capable default copy**

Populate `tutorial.json` with every visible milestone and the controls listed in the spec. Populate `tools.json` with exactly the three visible IDs and descriptions covering each tool's real input sequence. Do not add entries for silent milestones or Launch Tool.

- [ ] **Step 5: Run focused tests and type checking**

Run: `npm test -- --run tests/game/tutorial-content.test.ts tests/game/tool-content.test.ts tests/game/tutorial.test.ts tests/game/tools.test.ts`

Run: `npm run typecheck`

Expected: both PASS, including proof that progression and cycling still operate by IDs after live copy changes.

- [ ] **Step 6: Commit**

```bash
git add game/content/tutorial.json game/content/tools.json src/game/tutorial/content.ts src/game/tools/content.ts src/game/tutorial.ts src/game/tools.ts tests/game/tutorial-content.test.ts tests/game/tool-content.test.ts tests/game/tutorial.test.ts tests/game/tools.test.ts
git commit -m "feat(game): separate editable tutorial and tool copy"
```

### Task 2: Permanent authored-copy publication

**Files:**
- Create: `src/game/content-client.ts`
- Create: `game/content-publication.ts`
- Modify: `src-tauri/src/save_store.rs`
- Modify: `src-tauri/src/commands.rs`
- Modify: `src-tauri/src/lib.rs`
- Modify: `src-tauri/src/playtest_server.rs`
- Modify: `game/vite.config.ts`
- Test: `tests/game/content-client.test.ts`
- Test: `tests/game/content-publication.test.ts`
- Test: `tests/game/vite-content-watch.test.ts`
- Test: `src-tauri/src/save_store.rs`
- Test: `src-tauri/src/playtest_server.rs`

**Interfaces:**
- Consumes: `TutorialContentRevision`, `ToolContentRevision`, live publishers, and the existing atomic order-content file replacement discipline.
- Produces: `AuthoredContentClient.saveTutorial(records)`, `AuthoredContentClient.saveTools(records)`, `publishTutorialContentRevision(...)`, and `publishToolContentRevision(...)`. Neither operation accepts a save slot ID.

- [ ] **Step 1: Write failing transport and publication tests**

```ts
await client.saveTutorial(candidate)
expect(request).toHaveBeenCalledWith('save-tutorial', { content: candidate })
await publishToolContentRevision({ candidate, contentClient, content: live, isCurrent: () => true })
expect(events).toEqual(['persist', 'publish'])
```

Add failure cases proving a rejected persistent write does not publish the live revision and stale world generation cannot publish after persistence.

- [ ] **Step 2: Write failing Rust persistence and route tests**

The tests must prove exact-ID/nonblank validation, atomic replacement, restoration after a post-publication failure where applicable, distinct tutorial/tool routes, and no mutation of any save fixture or live save row.

Run: `cargo test --manifest-path src-tauri/Cargo.toml authored_content -- --nocapture`

Expected: FAIL because tutorial/tool stores and routes are absent.

- [ ] **Step 3: Extract the reusable atomic file publication primitive**

Refactor the order content store's temp-write, flush, rename, directory-sync, and restoration operations into one private primitive used by orders, tutorial copy, and tool copy. Preserve order/save reconciliation semantics unchanged. Add strict Rust records and validators for the two new content documents.

```rust
#[tauri::command]
pub fn save_tutorial_content(input: TutorialContentInput, state: State<'_, AppState>) -> Result<()>;

#[tauri::command]
pub fn save_tool_content(input: ToolContentInput, state: State<'_, AppState>) -> Result<()>;
```

- [ ] **Step 4: Add native and playtest transports**

Register `save_tutorial_content` and `save_tool_content`; expose authenticated POST routes `/__orchard_playtest/content/tutorial` and `/__orchard_playtest/content/tools`; select Tauri or playtest HTTP transport using the same environment contract as order publication.

- [ ] **Step 5: Prevent Vite session reloads for authored copy writes**

Extend the ignored watch set to `content/tutorial.json` and `content/tools.json`. Extend the watch test to edit each file through its content route and prove the active page is not reloaded.

- [ ] **Step 6: Run focused TypeScript and Rust tests**

Run: `npm test -- --run tests/game/content-client.test.ts tests/game/content-publication.test.ts tests/game/vite-content-watch.test.ts`

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Expected: PASS with permanent bytes and live revisions unchanged on every rejected candidate or failed write.

- [ ] **Step 7: Commit**

```bash
git add src/game/content-client.ts game/content-publication.ts src-tauri/src/save_store.rs src-tauri/src/commands.rs src-tauri/src/lib.rs src-tauri/src/playtest_server.rs game/vite.config.ts tests/game/content-client.test.ts tests/game/content-publication.test.ts tests/game/vite-content-watch.test.ts
git commit -m "feat(game): publish authored copy atomically"
```

### Task 3: Tutorial text editor and reachable developer interaction

**Files:**
- Create: `game/tutorial-editor.ts`
- Modify: `game/tutorial-card.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`
- Modify: `game/main.ts`
- Modify: `game/world-state.ts`
- Test: `tests/game/tutorial-editor.test.ts`
- Test: `tests/game/tutorial-card.test.ts`
- Test: `tests/game/world-state.test.ts`

**Interfaces:**
- Consumes: `TutorialContentRevision`, `publishTutorialContentRevision`, current visible `TutorialInstruction`, existing developer preference, and foreground-state checks.
- Produces: `mountTutorialEditor(root, actions)`, `TutorialEditorController.edit(definition)`, `Ledger`-independent tutorial-card `edit(milestoneId)` action, and developer-mode pointer release.

- [ ] **Step 1: Write failing controller behavior tests**

```ts
card.render(instruction, true, true)
card.root.click()
expect(calls.edited).toEqual(['move'])

editor.edit({ milestoneId: 'move', text: 'Use W to move.' })
text.value = 'Use W/A/S/D to move.'
form.requestSubmit()
await settled()
expect(calls.saved[0].definition('move').text).toBe('Use W/A/S/D to move.')
```

Cover nonblank validation, permanent-save rejection, live-card refresh, Backspace outside text, Backspace inside text, Escape/Pause draft preservation, Resume, and disabling Developer Tools closing the editor.

- [ ] **Step 2: Run focused tests and confirm RED**

Run: `npm test -- --run tests/game/tutorial-editor.test.ts tests/game/tutorial-card.test.ts tests/game/world-state.test.ts`

Expected: FAIL because the editor and developer click action do not exist.

- [ ] **Step 3: Implement the focused editor and card action**

The form contains immutable milestone ID, one required textarea, inline error, Cancel, and Save. It publishes a complete candidate revision and closes only after publication succeeds. The card advertises and handles editing only while Developer Tools is enabled.

- [ ] **Step 4: Integrate world/pause ownership**

Mount the editor beside the order editor. On developer-mode enable, release active pointer capture and show a cursor without changing camera/progression. Route Escape to Pause first, keep the editor mounted behind it, restore the draft on Resume, and make Backspace the editor close action only when no editable control owns it.

- [ ] **Step 5: Run focused tests and type checking**

Run: `npm test -- --run tests/game/tutorial-editor.test.ts tests/game/tutorial-card.test.ts tests/game/world-state.test.ts tests/game/tutorial.test.ts`

Run: `npm run typecheck`

Expected: PASS, with milestone completion still independent of edited text.

- [ ] **Step 6: Commit**

```bash
git add game/tutorial-editor.ts game/tutorial-card.ts game/index.html game/style.css game/main.ts game/world-state.ts tests/game/tutorial-editor.test.ts tests/game/tutorial-card.test.ts tests/game/world-state.test.ts
git commit -m "feat(game): edit tutorial copy in developer mode"
```

### Task 4: Tool descriptions and tool content editor

**Files:**
- Create: `game/tool-editor.ts`
- Modify: `game/ledger.ts`
- Modify: `game/tool-selector.ts`
- Modify: `game/index.html`
- Modify: `game/style.css`
- Modify: `game/main.ts`
- Test: `tests/game/tool-editor.test.ts`
- Test: `tests/game/ledger.test.ts`
- Test: `tests/game/tool-selector.test.ts`

**Interfaces:**
- Consumes: `ToolContentRevision`, `publishToolContentRevision`, immutable mechanics catalog, existing ledger developer flag, and foreground-state checks.
- Produces: `mountToolEditor(root, actions)`, `ToolEditorController.edit(definition)`, `LedgerActions.editTool(toolId)`, and selector/feedback lookup through the current live tool content.

- [ ] **Step 1: Write failing ledger, selector, and editor behavior tests**

```ts
expect(toolRow.querySelector('[data-tool-description]')?.textContent).toBe(savedDescription)
toolRow.click()
expect(calls.editedTools).toEqual(['iteration'])
expect(calls.acquired).toEqual([])

live.publish(renamedRevision)
inventory.cycle('1', 100)
selector.render(inventory, 100)
expect(selectedRow.textContent).toBe('Renamed Iteration')
```

Cover both Available and Acquired views, immutable ID presentation, nonblank fields, failed-save draft retention, Backspace text ownership, and Escape/Pause draft restoration.

- [ ] **Step 2: Run focused tests and confirm RED**

Run: `npm test -- --run tests/game/tool-editor.test.ts tests/game/ledger.test.ts tests/game/tool-selector.test.ts`

Expected: FAIL because descriptions and tool editing do not exist.

- [ ] **Step 3: Render live content without weakening mechanics**

Pass the current tool content revision into the ledger and selector. Render name and description for each visible row. Continue filtering, cycling, acquisition, saves, colors, silhouettes, and held models exclusively through immutable tool mechanics and IDs.

- [ ] **Step 4: Implement and integrate the focused tool editor**

The form contains immutable tool ID, required name and description fields, inline error, Cancel, and Save. In developer mode, row click opens the editor in both subtabs and does not acquire. Saving publishes the complete tool content revision, refreshes the open ledger, updates future selector and feedback copy, then closes.

- [ ] **Step 5: Run focused tests and type checking**

Run: `npm test -- --run tests/game/tool-editor.test.ts tests/game/ledger.test.ts tests/game/tool-selector.test.ts tests/game/tools.test.ts`

Run: `npm run typecheck`

Expected: PASS, including fixed mechanics before and after arbitrary valid name/description edits.

- [ ] **Step 6: Commit**

```bash
git add game/tool-editor.ts game/ledger.ts game/tool-selector.ts game/index.html game/style.css game/main.ts tests/game/tool-editor.test.ts tests/game/ledger.test.ts tests/game/tool-selector.test.ts
git commit -m "feat(game): edit tool names and descriptions"
```

### Task 5: Behavioral integration, fixture hygiene, and direct application validation

**Files:**
- Modify: `game/e2e/developer-orders.e2e.ts`
- Modify: `game/e2e/tutorial-progression.e2e.ts`
- Modify: `scripts/check-game-desktop.sh`
- Modify: `scripts/generate-game-saves.ts` only if authoritative content changes affect generated save bytes
- Modify: `game/generated-saves/*.sqlite3` only through the generator when bytes differ
- Test: all affected `tests/game/**/*.test.ts`

**Interfaces:**
- Consumes: both completed developer content flows and the canonical generated-save script.
- Produces: native behavioral coverage, exact content restoration after tests, clean checked-in fixtures, and direct manual interaction evidence.

- [ ] **Step 1: Extend native behavioral coverage**

Drive the real Developer Tools setting and actual UI controls. Edit the current tutorial instruction, confirm the card changes without milestone mutation, pause with Escape, resume to the same draft, close with Backspace, edit a tool name/description from each Tools subtab, observe the open ledger and `1` selector using the saved name, restart, and confirm persistence. Back up and restore both JSON files byte-for-byte in test cleanup.

- [ ] **Step 2: Audit new tests for behavioral authority**

Reject tests whose only assertion is a source substring, DOM scaffolding label, exact default editable prose, fixture presence, or implementation call sequence where the wrong user behavior could still pass. Keep assertions tied to stable IDs, visible state, permanent bytes, progression invariants, or real control outcomes.

- [ ] **Step 3: Regenerate and compare every save fixture**

Run: `npm run game:generate-saves`

Run: `git status --short game/generated-saves`

Expected: generated saves either remain byte-identical or all generator-derived changes are present; no hand-mixed fixture state remains.

- [ ] **Step 4: Run the complete automated suite**

Run: `npm test`

Run: `npm run typecheck`

Run: `npm run build`

Run: `cargo test --manifest-path src-tauri/Cargo.toml`

Run: `./scripts/check-game-desktop.sh`

Expected: every command PASS and authored content files match their pre-run bytes.

- [ ] **Step 5: Directly exercise the native application**

Launch the app and use real mouse/keyboard input through the visible desktop. Inspect the entire UI after each specified tutorial/tool edit, Pause, Resume, Backspace, selector cycle, settings transition, and restart. Confirm no unintended world interaction, focus loss, navigation, selection, or presentation change. Restore edited checked-in content through the UI or exact saved backup, rerun the affected interaction, and confirm a clean working tree.

- [ ] **Step 6: Commit**

```bash
git add game/e2e/developer-orders.e2e.ts game/e2e/tutorial-progression.e2e.ts scripts/check-game-desktop.sh scripts/generate-game-saves.ts game/generated-saves
git commit -m "test(game): verify permanent developer copy editing"
```
