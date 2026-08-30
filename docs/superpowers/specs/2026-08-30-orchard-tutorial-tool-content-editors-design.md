# Orchard Tutorial and Tool Content Editors Design

## Scope

This extension adds permanent, live developer editing for tutorial instructions and for tool names and descriptions. It also replaces the opening tutorial's placeholder-like instructions with copy that teaches a new player the controls needed to perform each requested action.

The existing application-level Developer Tools setting remains the sole authority for exposing developer interactions. No separate build, save-specific content, or alternate developer mode is introduced.

## Content authority

Tutorial progression remains keyed by the existing `TutorialMilestoneId` values. Milestone order, prerequisites, event recognition, visibility, tutorial enablement, and durable completion remain code-owned behavior. Checked-in `game/content/tutorial.json` owns only the text for every visible opening-tutorial milestone.

Tool identity and mechanics remain code-owned. The existing tool IDs, category, cycle order, acquisition requirements, colors, silhouettes, and effects cannot be changed through the editor. Checked-in `game/content/tools.json` owns only each visible tool's name and description.

Both content files are decoded strictly. Tutorial content must contain every and only visible tutorial milestone ID exactly once with nonblank text. Tool content must contain every and only visible tool ID exactly once with nonblank name and description. Invalid edits are rejected without changing either the checked-in file or the live content.

The semantic IDs, not editable prose, remain the authority for progression, tool selection, saves, and tests.

## Tutorial instruction content

The opening tutorial must tell a first-time player both what to accomplish and how to use the relevant controls. Its instruction sequence must cover:

- moving with W/A/S/D;
- looking with the mouse after engaging the world;
- ascending with Space;
- descending with Ctrl;
- sprinting with Shift while moving;
- selecting a tree with left click, moving around it with the movement controls, and returning with Backspace;
- pressing 1 to expose and cycle the available tools, selecting Sprout Spawner, and right-clicking clear ground to plant two more blank sprouts, including that crowded placements are refused;
- opening the ledger with Tab, using Tools > Available, and acquiring Double Cut;
- selecting Double Cut with 1, selecting a tree with left click, and right-clicking a branch to add two nested cuts;
- reopening the ledger after the Double Cut explanation so Iteration becomes available, then acquiring it from Tools > Available;
- selecting Iteration with 1, right-clicking a nonblank tree to hold a cutting, right-clicking clear ground to duplicate it, and using Backspace to release a held cutting;
- opening Orders > Available, accepting the blank-sprout order, using Iteration to take a blank sprout, and right-clicking that order's pot to deliver it.

The three silent order-completion milestones remain silent and have no editable tutorial card text.

## Tutorial editor interaction

When Developer Tools is enabled, the visible tutorial card is clickable. Clicking it opens a small foreground editor for the current milestone's text. The milestone ID is shown as immutable context; only the text is editable. Saving a nonblank value publishes it permanently to `game/content/tutorial.json`, updates the live card immediately, and closes the editor. A rejected save leaves the editor and draft visible with an error.

Enabling developer mode releases active world mouse capture so this click interaction is reachable. This does not change world, tutorial, order, or save progression. Normal click-to-engage behavior remains available after developer mode is turned off.

Backspace is the general step-back control: outside an editable text control it closes the foreground content editor. Backspace inside the text field edits text normally. Escape opens Pause from the editor, preserves the editor and its draft behind Pause, and Resume restores them.

## Tool content and editor interaction

Every visible tool has a nonblank description. The Tools ledger tab displays the current name and description in both Available and Acquired views.

When Developer Tools is enabled, clicking a tool tile in either Tools view opens a foreground editor for that tool. The tool ID is shown as immutable context. Only name and description are editable. The normal acquire action is unavailable from that developer interaction, so a click cannot both edit and acquire.

Saving nonblank values publishes them permanently to `game/content/tools.json`, updates the open Tools tab immediately, and closes the editor. Subsequent selector displays and acquisition feedback use the saved name. Fixed tool visuals and behavior do not change. A rejected save leaves the editor and draft visible with an error.

The editor follows the same Backspace, Escape/Pause, draft preservation, and developer-mode shutdown behavior as the tutorial and order editors.

Initial descriptions explain actual use:

- Sprout Spawner plants a blank sprout by right-clicking clear ground and refuses crowded locations near trees or order pots.
- Double Cut is used by left-clicking a tree and right-clicking a branch, adding two nested cuts at that branch.
- Iteration takes a cutting by right-clicking a tree, duplicates it by right-clicking clear ground, delivers a matching cutting by right-clicking an order pot, and releases a held cutting with Backspace.

## Permanent publication

Content editing writes the checked-in game content files, not a save, installation-specific preference, or per-session overlay. The browser playtest and native application use the same validated publication semantics.

Publication validates the complete candidate document before writing it, replaces the target atomically, and changes the live revision only after the permanent write succeeds. Vite ignores these authored-content writes so saving does not reload or reset the running world. Tutorial and tool content publication does not write the current game save because it changes authored copy, not player progress.

## Validation

Tests assert behavior through semantic milestone and tool IDs. They may verify that edited copy is displayed and persists, but must not make progression or mechanics depend on exact default prose or source-code structure.

Completion requires direct exercise in the native application through real pointer and keyboard input: enable Developer Tools, edit tutorial text, edit a tool name and description, verify live display and reopen behavior, verify Escape/Pause and Backspace behavior, restart and verify persistence, and restore the checked-in content files. The complete resulting UI state must be inspected after each interaction.
