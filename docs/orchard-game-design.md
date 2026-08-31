# Orchard (working title) — ratified demo design

Ratified 2026-08-26 in a grilling session. This document records the first
releasable demo design and the current playable order-loop contract. The demo
is "conceptually complete" when every core mechanic is present and exercised
by real puzzles, so anything added later is an enhancement rather than a
missing foundation.

## Identity

A legitimate standalone game — not educational software — that gamifies mathematical formalization the way Shenzhen IO gamifies assembly programming: the mechanics are the unabstracted real thing, and it need not even be obvious that the player is doing mathematics. The full calculus is non-negotiable: the calculus may be massaged (rules refactored or decomposed into primitives, as comprehension already has been), but if some rule cannot be given a workable tool and cannot be decomposed around, the game concept fails. Full calculus, but no nontrivial higher-order-logic content in the demo.

## Semantics

The orchard is one sheet of assertion. Each tree is an isolated top-level subgraph of that sheet; the whole orchard stands for one giant conjunction of theorems. Trees are diagrams as rendered by the existing 3D tree representation (`src/view3d/`) — nothing of the 2D Peirce notation appears anywhere in the game; cuts are branch banding, not circles.

- **Seedlings.** A seedling is a blank sheet — semantically ⊤, rendered as a
  small white stick. The current orchard begins with one seedling. Whole-tree
  iteration onto the ground duplicates a standing tree for free, gives the
  duplicate a fresh identity, and leaves the source standing.
- **Forward reasoning only.** Everything standing in the orchard is honestly proven at all times. Backward reasoning is parked, not rejected (a possible later tool at the pot).
- **Iteration and citation.** Ordinary iteration copies a proper subtree only
  within that same tree. A whole-tree cutting is a trusted library entry and
  may be cited into another tree at a permitted polarity. Citation checks the
  requested rewrite but does not replay a proof of the source theorem. Loading
  an orchard trusts its standing library; it does not re-verify trees or load
  proof histories.
- **No player-defined relations.** The game is perfect-information throughout. Where content involves "definitions" (the Boolean capstone), the player proves the *existence* of a relation once and thereafter duplicates that existence proof by cutting — no minting, no naming UI.
- **Progress is never forcibly lost.** Pots are not editable, delivery does not consume trees, and deletion is only ever the player's explicit choice.

## Core loop

Accept orders from a catalog; grow the ordered tree; deliver it by iterating a copy into the order's pot.

- **Ledger.** `Tab` toggles a centered ledger and releases world input. Tools
  has Available and Acquired views; Orders has Available, Active, and
  Completed views. Available orders are derived from completed prerequisites.
  Multiple orders may be active at once, each with its own pot. Abandonment
  removes only that order's pot and returns the order to Available with no
  penalty.
- **Pot.** Opening the catalog captures the player's displayed position and
  horizontal facing. Accepting places the pot six world units ahead of that
  chosen view and displays a hologram of the goal diagram. A goal is always
  exactly one tree (a conjunction is one tree that branches immediately). The
  pot is a submission-only region and is never editable.
- **Delivery.** Submission is literally the iteration move targeting the pot: the player takes a cutting of a tree and inserts it. If the cutting is not an exact match (isomorphism) of the goal, the iteration simply fails — sound cue and a short message, nothing lost, nothing to clean up. On an exact match the pot accepts: it departs with the copy, the order moves to the completed tab, reputation is awarded, and the source tree remains standing. Pots do not persist as trophies.

## Interaction

Loading or creating an orchard uses that same interaction to engage free
flight, so the world accepts movement without another click. While engaged,
mouse motion changes yaw and pitch, `W`/`S` move forward and
back, `A`/`D` strafe, `Space`/`Control` move vertically, and `Shift` sprints. A
small center reticle is the aim point. When free flight is inactive, the world
shows only “Click to play.”

A primary click while free flight is active selects the tree under the reticle
and enters the same 3D proof-tree interaction used by the assistant. The
orchard supplies the selected tree, its world placement, and its control
mapping. While a tree is selected, `A`/`D` rotate around it, `W`/`S` change the
horizontal radius, and `Space`/`Control` change eye height. Mouse movement and
the wheel do not move the selected-tree camera. The shared interaction remains
the sole owner of the camera pose, component focus, click classification, and
  focus glide. `Backspace` restores the exact pre-selection free-flight pose
  and requests free-flight input again during that same key interaction, so
  play resumes without another click when engagement succeeds.

`Escape` opens Pause from free flight, orbit, a held cutting, or the open
ledger. Pausing suspends world input and frame updates without changing the
camera mode, held cutting, selected tool, ledger state, or orchard state.
Resume returns to that exact play state. Main Menu finishes pending saves before
closing the world and refreshes the saved-orchard list in the same application
session; a save failure leaves Pause open. Quit Game likewise requires pending
saves to finish before closing the native application.

The player begins with Sprout Spawner. Its stationary secondary action plants a
blank sprout on clear ground; placement within four horizontal world units of a
tree or active order pot is refused without changing the orchard. Double Cut
and Iteration are acquired from the ledger. Pressing `1` cycles only the tools
already acquired in category 1 and briefly shows that category's list. Double
Cut applies its proof move with one stationary secondary release on the targeted
branch.

Iteration is a two-stage stationary secondary gesture. The first release takes
either the whole targeted tree or a targeted proper subtree. The second release
chooses its destination:

- a whole tree onto ground creates a free, independent duplicate;
- a proper subtree onto its source tree performs ordinary iteration;
- a whole tree onto another tree performs trusted library citation when the
  target polarity permits it; and
- a whole tree onto the accepted order's pot attempts delivery.

A proper subtree cannot target a different tree. Invalid destinations explain
the refusal and keep the cutting held so the player can try again. `Backspace`
clears a held cutting before applying its orbit-exit behavior. Deiteration is
not part of Iteration; it remains a future, separate tool.

A dragged mouse does not move the camera or fire a proof action. Proof actions
do not change the camera or navigation mode. A successful change publishes one
complete tree value to the live session and renderer and queues that same value
for saving.

Game camera state owns free/selected mode and the exact free-flight pose. The
shared 3D interaction owns the selected-tree camera pose. The renderer owns
targeting and render projections, the input adapter owns browser listeners and
transient samples, and the composition root samples input once per frame.
Saves always receive the stored free-flight pose while a tree is selected.
Relative-input engagement is transport only: rejection or loss leaves the
loaded world and camera state unchanged, clears transient input, and exposes no
parallel control path.

## Progression and economy

- **Opening prerequisite DAG.** A blank-sprout order opens first. Completing it
  unlocks one bare Double Cut; completing that order unlocks two authored
  irregular Double-Cut goals together. Each awards one reputation, and the two
  final orders may be completed in either order. This is the implemented first
  branch of the larger puzzle DAG: previously opened content stays open.
- **Tools unlock by readiness** — completion of specific puzzles — and each tool unlock opens that tool's starter puzzle sequence, which carries its tutorial.
- **Tutorials** are a per-save preference, enabled by default at orchard
  creation and editable in Settings. One upper-left instruction at a time leads
  through movement, look, ascent/descent, sprint, orbit and `Backspace`, two
  sprouts, both tool acquisitions, Double Cut, Iteration duplication, and the
  first delivery. The card then disappears while the remaining order milestones
  continue silently. Disabling tutorials hides the card and opens tutorial-gated
  ledger entries without marking milestones complete; ordinary actions still
  record their evidence, so re-enabling resumes at the first genuinely unmet
  instruction.
- **Reputation** is the single progression stat: a cap that rises as puzzles are completed. Unlocks and expansion draw against the cap (usage accumulates toward the cap; mechanically like spending money, but framed as standing rather than wealth).
- **Expansion** is core: the player starts on a bounded plot and opens adjacent land (later: floating islands, planetoids — the world is abstract and 3D). Areas should be visually distinct to aid navigation and self-organization, but are never bound to logical domains — organization is the player's, aided by fences and signs. Decoration beyond fences and signs is not core.

## Content

No runtime puzzle generation, ever — it has been investigated repeatedly and does not produce interesting puzzles. Two sources, both developer-time:

1. **Enumerate-then-curate catalogs.** For each decidable/semidecidable domain: exhaustively enumerate theorems up to a size (modulo symmetries like variable ordering), filter by interestingness criteria (e.g. reject anything solvable by erasure alone — criteria designed per domain), then hand-select. Demo domains: propositional, second-order Boolean formulas, first-order equational logic. The three enumeration/filter pipelines are dev-tooling deliverables of the demo.
2. **Hand-authored sequences**, inspired by real formalizations and teaching material. The demo's capstone is a Boolean sequence: establish the adjunction between true and false, use it to identify the universal properties of the Boolean operators, derive the truth tables from those universal properties, then prove the algebraic laws. When the capstone is reachable and every core mechanic is exercised by real puzzles, the demo is complete.

Developer Tools is an application-wide preference in Pause > Settings. When it
is enabled, backtick toggles a visible developer mode. In that mode an order
tile opens the repository-backed editor, while clicking the Orders primary tab
opens a new-order editor. The editor changes prerequisites, reward, and optional
formula input; the stored diagram remains runtime authority and is previewed
before publication. Existing IDs are read-only, new orders begin with a blank
goal, and Delete removes the order's lifecycle entry and active pot. A successful
save writes `game/content/orders.json` before publishing the catalog revision.
Accepted order instances keep the goal they had when accepted; catalog edits
affect later views and acceptances. Invalid formulas, invalid prerequisite graphs,
and persistence failures leave both the running catalog and checked-in content
unchanged.

Developer mode also makes the visible tutorial card and tool tiles editable.
The tutorial editor changes the current instruction text. The tool editor changes
the selected tool's name and description, and both Tools views show those
descriptions. Successful edits update the running interface and checked-in game
content. `Backspace` closes a foreground editor when text does not own the key;
`Escape` opens Pause and preserves the editor draft. Tutorial instructions and
tool descriptions explain the controls needed to use them.

The game must not crash during play. Developer tooling is a convenience for
changing game content, not a production content-management system. It must not
acquire content histories, save migrations, concurrent-edit coordination, upgrade
merging, or automated recovery unless requested game behavior needs them.

**Bootstrap corpus.** The `game/cursebreaker` branch (worktree `.worktrees/cursebreaker-domain`) holds 121 entirely propositional puzzles in the kernel's own diagram JSON (`content/puzzles/`), each with a machine-checked backward solution (`content/validation/`), a prerequisite DAG (`content/progression/core.json`), and a hint-intervention system (`content/guidance/`). The diagram-JSON loader files are byte-identical to main, so the puzzles load unchanged. Those puzzles are stated in backward orientation — the stored diagram is the goal, which is exactly what a pot hologram needs; the backward solutions flip to forward solvability certificates under the shared-implementation polarity-flip law. This corpus is interim content for implementation and will eventually be replaced by the propositional enumeration pipeline. Nine of the puzzles already exercise lemma citation.

## Tech

- **Codebase:** an isolated branch of the VisualProofAssistant repo that directly consumes the shared `src/kernel` and `src/view3d` authorities; full separation into its own repo later. The proof assistant itself is an investigation platform with no maintenance obligation.
- **Shell:** a standalone Tauri app, scaffolded from the start of implementation (save-file I/O, window/input behavior, and packaging proven in the real shell throughout). Web tech inside: Vite + three.js, unchanged.
- **Saves:** unlimited named save slots backed by files, Skyrim-style. A save
  stores its name, free-flight camera pose, trees, reputation, tutorial setting
  and completed milestones, acquired tool IDs, and every authored order's
  pending/accepted/completed lifecycle (including active pot placement). Open
  ledger/editor state, selected tool, held cutting, developer mode, and selector
  visibility are transient. The save format always has one exact current shape:
  no format versions, migrations, legacy readers, or fallback parsing. Runtime
  worlds are constructed only by loading ordinary saves; developer and stress
  fixtures use the same persistence authority. Developer content edits may make
  existing saves invalid. Saves do not record a content version, and the engine
  does not migrate or repair saves after content changes. Recovery is deleting
  or manually editing the affected save.
- **Scale:** the shared `src/view3d/transition.ts` track owns growth timing, interruption, and sampling. Each changing tree owns one track independently, so several trees may animate concurrently. The established stress workload has proven static rendering, LOD, and culling to 2000 trees; generated game saves preserve that workload against the production renderer. Every tree uses the same kernel-backed model and can take the temporary per-frame render role when it changes.
- **Renderer authority:** `game/` is the sole 3D world frontend. Performance workloads are ordinary generated game saves, and stress tests exercise the same production renderer used by play.

## Deferred to implementation, by design

These are decisions the session explicitly ruled must be made in situ, not in this document:

- Gesture design for later proof moves beyond the current stationary secondary
  releases (some, like wire severing, may require a distinct interaction).
- The tool taxonomy: likely by building many overlapping candidate tools and keeping the covering subset that individually feels good. Constraint fixed now: the shipped tool set must be closed over the shipped catalog (every order solvable), and must cover the full calculus.
- Per-tool vocabulary and tutorial text.
- Per-domain interestingness criteria for the enumeration pipelines.
- Orchard aesthetics: the 3D shape of the world, region flavors, day/night, sound.
- Balancing: reputation values, unlock thresholds, DAG shape beyond the teaching spine.
- Backward reasoning at the pot (parked as a possible later feature).
