# Orchard Tutorial, Progression, and Interface Design

**Status:** Approved 2026-08-29

This slice fills out Orchard's opening sequence without creating temporary
tutorial or content systems. It adds persistent tutorial progress, scalable
tool acquisition and order prerequisites, one new tree-spawning tool, four
opening orders, a usable play interface, and repository-backed order editing.

## Opening result

A new orchard contains one blank tree and starts with Sprout Spawner acquired.
The player learns the existing movement and orbit controls, plants two more
sprouts, acquires Double Cut and Iteration through the ledger, and completes
four orders. The last two orders can be completed in either order.

The new-orchard form has a Tutorials checkbox that is checked by default. Its
value belongs to that save and can later be changed from Settings.

Disabling tutorials hides tutorial instructions and makes every tutorial check
pass. It does not mark tutorial milestones complete or change gameplay state.
Actions performed while tutorials are disabled still complete their ordinary
tutorial milestones. Re-enabling tutorials resumes at the first milestone the
player has not performed.

## Tutorial sequence

The tutorial card occupies the upper-left corner and contains one instruction
at a time beside a provisional figure. It has no checklist, progress pips, or
permanent script outline.

The opening sequence is:

1. Demonstrate movement, mouse look, ascent, descent, and sprint.
2. Left-click the initial tree and demonstrate orbit movement.
3. Press `Backspace` to return to free flight.
4. Use Sprout Spawner on clear ground twice.
5. Open the ledger with `Tab` and acquire Double Cut for zero capacity.
6. Close the ledger and apply Double Cut successfully.
7. Read a direct explanation of Double Cut: targeting a leaf adds two nested
   layers there; targeting an intermediate branch adds two nested layers from
   that branch.
8. Reopen the ledger and acquire Iteration for zero capacity.
9. Duplicate a tree that is not a blank sprout onto clear ground.
10. Accept and deliver the blank-sprout order.
11. Complete the single-Double-Cut order.
12. Complete the two final Double-Cut-only orders in either order.

Tutorial code observes committed gameplay events and records tutorial progress.
It never grants tools, creates trees, accepts orders, or performs proof moves.
Sprout Spawner belongs to every new save's starting inventory. Double Cut and
Iteration always use the same ledger acquisition mechanism, whether tutorials
are enabled or disabled.

The tutorial card disappears after the first order's delivery explanation.
Completion of the remaining three orders continues the tutorial silently until
both final orders are complete.

## Input behavior

`Escape` always opens Pause from free flight, orbit, a held cutting, or the open
ledger. Pausing preserves the exact camera mode, held cutting, equipped tool,
ledger state, and orchard state. Resume returns to that state.

`Backspace` is the step-back control. If an Iteration cutting is held, the first
press clears it. Otherwise, if the camera is orbiting a tree, the press restores
free flight.

`Tab` toggles the ledger. The number keys select tool categories. Category `1`
initially contains Sprout Spawner, Double Cut, and Iteration, and repeated
presses cycle through the acquired tools in that category. Unacquired tools are
not part of the cycle and are not shown to the player.

The category selector is normally absent. Pressing `1` temporarily shows the
number and a vertical list of every acquired tool in that category. The
equipped tool is highlighted. Repeated presses move the highlight and change
the held model together. The list fades after a short period without another
category-key press. The ordinary HUD does not permanently name the equipped
tool because the held model already communicates it.

## Tools and tree placement

Each acquired tool has a simple held model made from colored primitives. The
three opening tools use distinct colors and silhouettes. Final tool art and the
tutorial companion are separate design passes.

Sprout Spawner uses the existing stationary right-click tool action. A
successful action creates a blank proof tree at the targeted ground point. The
placement must leave clearance from every existing tree and order pot. The
initial clearance value is an authored gameplay constant that can be tuned
later. An invalid placement explains the refusal and changes nothing.

The tool inventory stores acquired tool IDs. Authored tool definitions provide
their category and reputation-capacity requirement. The established reputation
system remains unchanged. Double Cut and Iteration both require zero capacity
in this opening sequence.

## Ledger interface

The ledger is a centered overlay with two levels of navigation. Its permanent
tabs are Tools and Orders. Each selected tab has one contextual row directly
beneath it; redundant section titles and explanatory filler do not appear.

The Tools tab has Available and Acquired views. Tools are descriptive rows.
Only tools the player can currently acquire appear in Available, and only owned
tools appear in Acquired.

The Orders tab has Available, Active, and Completed views. Orders are visual
tiles built around their goal previews. Runtime order tiles do not have titles,
move or tool labels, reward decorations, recommendation logic, search, or
filters. Unavailable orders do not appear.

The player may accept any number of available orders. Every accepted order
owns its own pot. Abandoning an active order returns its tile to Available and
removes its pot. Successful delivery removes the pot and moves the tile from
Active to Completed.

The upper-right play interface contains quiet save and operation status. The
ledger does not add a reputation display in this slice. The held tool model,
temporary category selector, tutorial card, reticle, and concise failure
feedback form the rest of the in-world interface.

## Opening order graph

The opening catalog contains four fixed orders. Each awards one reputation.

1. A blank sprout.
2. One bare Double Cut, unlocked by completing the blank-sprout order.
3. An irregular diagram made from arbitrary valid Double Cut applications.
4. A different irregular diagram made the same way.

Completing the single-Double-Cut order unlocks both irregular goals. The final
two diagrams are authored once during implementation and stored permanently.
There is no puzzle-generation feature or runtime puzzle generation.

Order definitions contain stable IDs, prerequisite IDs, rewards, authoritative
diagram snapshots, and optional remembered formula text. Availability is
derived from completed prerequisite orders and tutorial checks; it is not a
separate persisted order state. The saved order lifecycle remains pending,
accepted with pot placement, or completed.

## Settings

Pause gains a Settings action. Settings contains:

- Tutorials, a per-save checkbox whose initial value comes from orchard
  creation.
- Developer Tools, an application-wide checkbox that is off by default.

Changing Tutorials immediately updates instruction visibility and tutorial
checks without completing milestones or changing gameplay state. Developer
Tools controls access to developer mode; it is not save progression.

## Repository-backed order editing

With Developer Tools enabled, backtick toggles developer mode and shows a clear
mode indicator. In developer mode, clicking an order tile opens that order's
editor instead of performing its ordinary action. Clicking the Orders primary
tab opens a new-order editor.

The editor shows the stable order ID as read-only context. It can edit
prerequisite IDs, reward, and optional formula input, and it displays the
authoritative diagram preview. It also contains a Delete action. Order-ID
renaming is not part of this feature.

The new-order editor starts with the blank diagram—the empty sheet or true
tree—as its authoritative goal and with blank formula input. It accepts the new
stable ID and the same editable content as an existing order. Creating or
deleting an order updates the checked-in catalog and running game immediately.
Creation adds its lifecycle entry to the current save. Deletion removes its
lifecycle entry and any active pot. A create or delete that would leave an
invalid prerequisite graph fails without changing the catalog or save.

An order without remembered formula text opens with a blank formula field. An
order with remembered text shows it. Submitting formula text parses it, creates
a new authoritative diagram, stores the submitted text, and refreshes the
preview. Formula text is an optional input convenience and has no runtime
authority. Runtime behavior always consumes the stored diagram.

Saving writes the checked-in game-content catalog, not installation-specific
or save-specific content. A successful save activates the revision immediately
in the running game. The ledger tile, prerequisite projection, linked pot
rendering, and delivery validation all switch to the saved definition together.

The current static catalog import becomes one live catalog authority shared by
the ledger, order session, tutorial gates, and renderer. Accepted order state
continues to carry its order ID and pot placement; it does not gain a separate
goal snapshot.

The permanent write completes before the live catalog publishes the revision.
A formula parse failure, invalid prerequisite graph, or filesystem failure
keeps the editor open with a concrete error and leaves both the checked-in file
and loaded catalog unchanged. Tutorial copy receives no content-validation
system.

## Saved state

The current save format is replaced with one exact schema that additionally
stores:

- whether tutorials are enabled;
- completed tutorial milestone IDs;
- acquired tool IDs;
- the existing reputation and lifecycle state for every authored order.

Order definitions, goal diagrams, prerequisite edges, optional formula text,
and tutorial copy are game content rather than save data. Equipped-tool choice,
the temporary category list, the open ledger tab, developer mode, and held
cuttings are transient.

The application preference for Developer Tools is stored separately from game
saves. Generated saves and persistence fixtures are regenerated through the
production toolchain after the schema changes. The save format has no versions,
migrations, legacy readers, or compatibility aliases.

## Runtime ownership

One tutorial session owns completed milestone IDs and evaluates gameplay events.
It exposes whether a tutorial check passes under the save's Tutorials setting.
It does not own world mutations.

One tool-inventory controller owns acquired tools, authored category membership,
the selected acquired tool in each category, and the temporary category-list
presentation state. Held Iteration cuttings remain part of tool interaction
state.

One live order catalog owns the currently loaded definitions and repository
updates. The order session continues to own player reputation and order
lifecycle states. The renderer continues to own pot and tree presentation.
`game/main.ts` composes their events and prepared publications.

## Scope boundary

This slice includes the complete opening tutorial, reversible tutorial display,
three-tool category cycling, Sprout Spawner, four prerequisite-linked orders,
the redesigned HUD and ledger, Settings, and repository-backed order creation,
editing, and deletion.

It does not include final tutorial-companion art, final tool art, additional
tool categories, input rebinding, final tutorial prose, a general object editor,
Blender-like world manipulation, order-ID renaming, puzzle-generation tooling,
runtime puzzle generation, search, order filters, or recommendation logic.
