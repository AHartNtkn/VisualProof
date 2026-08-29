# Orchard First Order Loop Design

**Status:** Approved 2026-08-29

Orchard's next slice delivers one complete order from acceptance through
delivery. It adds tree duplication, theorem citation, two equipped items, a
player-placed pot, persistent order state, and one reputation award.

## Goal

A player can accept one starter order, place its pot, grow the requested tree,
and deliver an exact copy without consuming the source tree. The same iteration
item also duplicates whole trees onto the ground and performs ordinary
subtree iteration within one tree.

The starter order asks for a bare double cut grown from the initial blank
seedling. Both required proof operations are real kernel operations. Delivery
uses the orchard as a library of proven theorems rather than introducing a
submission-only proof shortcut.

## Calculus model

The orchard is a library. Every standing tree is a theorem equivalent to the
empty sheet, and the empty sheet represents true. Loading a save establishes
the orchard's trusted library state; save loading does not replay proofs or
validate proof histories.

The shared proof layer gains a small library abstraction. A library entry
names a theorem diagram supplied by its host. Applying an entry checks only
whether the requested citation is structurally valid, then uses the native
theorem-rewrite machinery. It does not check or replay a proof of the library
entry. Orchard library entries are propositions rather than open relations, so
they have no external boundary positions. Every wire belonging to the standing
tree remains part of that theorem diagram.

The iteration item selects one of two operations from the source and target:

- A proper subtree targeting a branch in the same tree uses the kernel's
  ordinary iteration rule. The target must be the source region or one of its
  descendants, and it cannot lie inside the copied content.
- A whole tree targeting another tree cites the source through the orchard
  library. A proper subtree can never target another tree.

Whole-tree citation also defines duplication and delivery. Citing into a new
blank diagram produces an independent tree. Citing into a pot's blank
submission diagram produces the diagram checked against the order goal.

Deiteration is not part of the iteration item. It will receive a separate tool
design and may share an equipped item with erasure.

## Equipped items and gestures

The player has two visibly distinct equipped items for this slice: double cut
and iteration. Pressing `1` swaps them. The HUD identifies the equipped item,
and changing items cancels any held cutting.

Double cut keeps its current stationary secondary action on the targeted
branch. It changes no camera or navigation state.

Iteration uses two stationary secondary actions. The first takes a cutting:

- targeting the root branch takes the whole tree;
- targeting another branch takes that branch's complete subtree.

The second action chooses a destination:

- ground plus a whole tree creates an independent duplicate;
- a legal branch in the same tree performs ordinary iteration;
- a branch in another tree plus a whole tree performs library citation;
- a pot plus a whole tree attempts delivery.

Every other source and destination combination fails with a short explanation
and no state change. An invalid destination leaves the cutting held so the
player can try again. A successful action clears it. `Escape` cancels a held
cutting before performing its existing orbit-exit behavior.

A ground destination is the terrain point under the reticle. The duplicate's
horizontal position is that point, and its yaw follows the player's horizontal
facing direction. The source tree is never changed or consumed.

## Catalog, pot, and order

`Tab` opens the catalog and releases relative input. Opening records the
current displayed camera position and horizontal facing. Closing requests
world engagement again without changing the camera or navigation mode.

The catalog has Pending and Completed tabs. The one starter order can be
accepted or abandoned without cost. Accepting records a pot position several
world units in front of the view captured when the catalog opened, projected
onto the terrain. The player therefore chooses the pot's location by moving
and facing before opening the catalog.

The accepted pot displays the authored goal as a hologram. It is a
submission-only target and is never editable. Abandoning the order removes the
pot and returns the order to Pending.

Delivery requires a whole-tree cutting. The library citation is applied to the
pot's blank submission diagram, and the result is compared with the authored
goal by exact kernel diagram isomorphism. A mismatch changes nothing and
leaves the cutting held. A match removes the pot, moves the order to Completed,
awards one reputation, clears the cutting, and leaves the source tree standing.

## Runtime authorities

`GameSession` remains the sole authority over standing trees. The orchard
library is derived from the session's current tree map; it is not a second
mutable copy of the trees.

A pure tool-state controller owns the equipped item and held cutting. A held
cutting records the source tree identity, the source tree value used to create
it, and the selected subtree or whole-tree library entry. If the source tree
changes before placement, the cutting is stale and placement fails.

An order session owns one lifecycle state per order plus reputation. The state
is a closed choice: pending, accepted with one pot placement, or completed.
The authored catalog owns order IDs, display copy, goal diagrams, and rewards.
The Pending and Completed tabs are projections of this one state map.

The world renderer owns tree, terrain, and pot presentation and targeting. It
does not decide tool semantics, order state, or diagram equality. A catalog
controller owns the Pending and Completed interface and input suspension.
`game/main.ts` composes these authorities.

## Prepared world changes

Tree update and tree insertion are two variants of one prepared world change.
For either variant, the session plans the complete next tree value, the
renderer prepares its representation without publishing it, and `SaveWriter`
accepts the durable operation. The session and renderer then publish the same
prepared result.

A duplicate receives a fresh game-tree ID before preparation. Save operations
for inserting that tree and later updating it retain their order. Camera and
repeated update coalescing remains limited to operations where replacing an
older queued value is semantically safe.

Order transitions follow the same discipline. Accept prepares the accepted
order and pot. Abandon prepares pot removal and a return to Pending. Completion
prepares pot removal, Completed state, and the reputation award as one change.
Each change becomes live only after the writer accepts its durable operation.

Planning failure, renderer preparation failure, or save-queue rejection leaves
live state unchanged. A later asynchronous write failure retains the committed
live state and the exact queued operation, exposes retry status, and never
rolls gameplay back.

## Save data and transports

The current save format is replaced with a schema that also stores:

- reputation;
- one lifecycle state for every authored order, where only the accepted state
  carries a pot position and yaw.

Trees and their placements remain the saved proof authority. Equipped-item and
held-cutting state is transient. Authored goals and catalog copy are content,
not save data.

The order table has one row per order ID and one state column. Its constraints
require pot placement for the accepted state and prohibit pot placement for
pending or completed states. Accept changes pending to accepted. Abandon
changes accepted to pending and clears the placement. Completion changes
accepted to completed, clears the placement, and increments reputation exactly
once in one SQLite transaction.

The Rust `SaveStore` adds ordered operations for inserting a tree and performing
those order transitions. Tauri IPC and the browser playtest service expose the
same operations through the same store methods.

Rust validates the stored structure, state-specific pot fields, finite pot
coordinates, and nonnegative reputation. The frontend requires the persisted
order-ID set to equal the authored catalog's ID set before mounting the world.
An unknown or missing order ID keeps the slot on the start menu with a concrete
load error; no partial world is mounted.

The save format has one exact current shape. There are no versions, migrations,
legacy readers, or fallback parsing. Generated saves and persistence fixtures
are regenerated through the production toolchain.

## Validation

Kernel tests must show that library citation inserts a trusted theorem without
checking or replaying its proof, uses the shared theorem-rewrite authority, and
works at every permitted target polarity. They must also enforce ordinary
same-tree iteration scope and reject every proper-subtree cross-tree request.

Game tests must cover item swapping, cutting cancellation, root and proper
subtree selection, stale cuttings, every source and destination combination,
ground placement, source preservation, fresh duplicate identity, and prepared
update and insertion behavior.

Order tests must cover catalog derivation, acceptance, pot placement,
abandonment, mismatched delivery, successful delivery, source preservation,
Completed state, and a single reputation award.

Rust and transport tests must cover tree insertion followed by update, pot
placement across reload, abandon and completion transactions, idempotent
reputation award, ordered retry, strict rejection of an incomplete current
schema, and every added operation through both Tauri and HTTP transports.

Renderer and input tests must cover terrain and pot targeting, prepared tree
insertion, pot appearance and removal, `1`, `Tab`, `Escape`, engagement changes,
and gesture cancellation.

Direct application exercise must use the production controls to:

1. create an orchard;
2. accept the starter order from a chosen viewpoint;
3. reload and confirm the pot placement;
4. swap items with `1`;
5. duplicate the seedling onto targeted ground;
6. perform a legal same-tree iteration and attempt an illegal target;
7. grow the bare-double-cut theorem;
8. attempt a mismatched delivery;
9. deliver the exact theorem and inspect pot departure, Completed state,
   reputation, and source preservation;
10. reload and inspect the resulting orchard and progression state.

The primary flow and its adjacent transitions must be exercised directly in
the native application. Browser playtesting must confirm the same frontend
behavior through the shared save service. TypeScript tests, type checking,
Rust tests, the game build, native end-to-end tests, and generated-save checks
must all pass.

## Scope boundary

This slice contains one order, two equipped items, ordinary iteration,
whole-tree library citation, tree duplication, player-chosen pot placement,
order persistence, and one reputation award.

It does not contain deiteration, erasure, additional tools, spawning blank
seedlings, prerequisite unlocks, tutorials, land expansion, sound, balancing,
or final art.
