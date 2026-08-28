# Orchard (working title) — ratified demo design

Ratified 2026-08-26 in a grilling session. This document records every decision the session settled for the first releasable demo, and lists what was deliberately deferred to implementation time. The demo is "conceptually complete": every core mechanic present and exercised by real puzzles, so that anything added later is enhancement, not core.

## Identity

A legitimate standalone game — not educational software — that gamifies mathematical formalization the way Shenzhen IO gamifies assembly programming: the mechanics are the unabstracted real thing, and it need not even be obvious that the player is doing mathematics. The full calculus is non-negotiable: the calculus may be massaged (rules refactored or decomposed into primitives, as comprehension already has been), but if some rule cannot be given a workable tool and cannot be decomposed around, the game concept fails. Full calculus, but no nontrivial higher-order-logic content in the demo.

## Semantics

The orchard is one sheet of assertion. Each tree is an isolated top-level subgraph of that sheet; the whole orchard stands for one giant conjunction of theorems. Trees are diagrams as rendered by the existing 3D tree representation (`src/view3d/`) — nothing of the 2D Peirce notation appears anywhere in the game; cuts are branch banding, not circles.

- **Seedlings.** A seedling is a blank-sheet spawn — semantically ⊤, rendered as a small white stick. Spawning is free and unlimited.
- **Forward reasoning only.** Everything standing in the orchard is honestly proven at all times. Backward reasoning is parked, not rejected (a possible later tool at the pot).
- **Citation = iteration.** Iterating one tree into another is theorem citation; the orchard is the player's library. This is the calculus's own iteration rule, not a separate mechanic.
- **No player-defined relations.** The game is perfect-information throughout. Where content involves "definitions" (the Boolean capstone), the player proves the *existence* of a relation once and thereafter duplicates that existence proof by cutting — no minting, no naming UI.
- **Progress is never forcibly lost.** Pots are not editable, delivery does not consume trees, and deletion is only ever the player's explicit choice.

## Core loop

Accept orders from a catalog; grow the ordered tree; deliver it by iterating a copy into the order's pot.

- **Catalog.** Pending and completed orders live in separate tabs. The player may accept as many orders as they want. Orders can be abandoned freely from the same interface — pot vanishes, order returns to the catalog, no penalty. Orders never expire.
- **Pot.** Accepting an order produces a pot displaying a hologram of the goal diagram. A goal is always exactly one tree (a conjunction is one tree that branches immediately). The pot is a submission-only region — never editable, so the player cannot lose work into it.
- **Delivery.** Submission is literally the iteration move targeting the pot: the player takes a cutting of a tree and inserts it. If the cutting is not an exact match (isomorphism) of the goal, the iteration simply fails — sound cue and a short message, nothing lost, nothing to clean up. On an exact match the pot accepts: it departs with the copy, the order moves to the completed tab, reputation is awarded, and the source tree remains standing. Pots do not persist as trophies.

## Interaction

Loading an orchard restores its saved free-flight pose and waits for a world
click before accepting movement. That click engages cursorless relative input;
while engaged, mouse motion changes yaw and pitch, `W`/`S` move forward and
back, `A`/`D` strafe, `Space`/`Control` move vertically, and `Shift` sprints. A
small center reticle is the aim point. When free flight is disengaged, the world
shows only “Click to play.”

A primary click while engaged orbits the tree under the reticle. Orbit restores
the ordinary pointer, ignores mouse motion, uses `A`/`D` to rotate, `W`/`S` to
change distance, and `Space`/`Control` to change height. `Escape` restores the
exact pre-orbit free pose and leaves free flight disengaged. Secondary click has
no camera or tree effect.

The pure camera state is the sole free/orbit and persisted-pose authority. The
renderer owns tree targeting and display only, the input adapter owns browser
listeners and transient motion only, and the composition root samples input
once per frame. Saves always receive the stored free-flight pose, including
while orbiting. Pointer Lock is only the relative-input transport: rejection or
loss leaves the loaded world and camera state unchanged, clears transient input,
and exposes no fallback control path.

## Progression and economy

- **One prerequisite DAG of puzzles.** The root of the DAG is a teaching spine: propositional fundamentals first; completing them unlocks the second-order propositional basics sequence and (as a separate branch) first-order equational logic; after all fundamentals, the Boolean capstone unlocks. Bulk/optional sequences (the ~100 propositional puzzles and counterparts in other domains) bud off the spine for pacing. Each puzzle unlocks only a few others so the player is never flooded. No hard acts — everything previously opened stays open.
- **Tools unlock by readiness** — completion of specific puzzles — and each tool unlock opens that tool's starter puzzle sequence, which carries its tutorial.
- **Tutorials** are delivered by a robot companion that accompanies the player after each tool unlock, giving plain guidance ("try this") on the starter puzzles, then leaves. Text is allowed and should be sparse, direct, and well written; the game is mostly quiet. Vocabulary is horticultural-first: mathematical terminology avoided but not banned, with each tool's naming decided when the tool is designed.
- **Reputation** is the single progression stat: a cap that rises as puzzles are completed. Unlocks and expansion draw against the cap (usage accumulates toward the cap; mechanically like spending money, but framed as standing rather than wealth).
- **Expansion** is core: the player starts on a bounded plot and opens adjacent land (later: floating islands, planetoids — the world is abstract and 3D). Areas should be visually distinct to aid navigation and self-organization, but are never bound to logical domains — organization is the player's, aided by fences and signs. Decoration beyond fences and signs is not core.

## Content

No runtime puzzle generation, ever — it has been investigated repeatedly and does not produce interesting puzzles. Two sources, both developer-time:

1. **Enumerate-then-curate catalogs.** For each decidable/semidecidable domain: exhaustively enumerate theorems up to a size (modulo symmetries like variable ordering), filter by interestingness criteria (e.g. reject anything solvable by erasure alone — criteria designed per domain), then hand-select. Demo domains: propositional, second-order Boolean formulas, first-order equational logic. The three enumeration/filter pipelines are dev-tooling deliverables of the demo.
2. **Hand-authored sequences**, inspired by real formalizations and teaching material. The demo's capstone is a Boolean sequence: establish the adjunction between true and false, use it to identify the universal properties of the Boolean operators, derive the truth tables from those universal properties, then prove the algebraic laws. When the capstone is reachable and every core mechanic is exercised by real puzzles, the demo is complete.

**Bootstrap corpus.** The `game/cursebreaker` branch (worktree `.worktrees/cursebreaker-domain`) holds 121 entirely propositional puzzles in the kernel's own diagram JSON (`content/puzzles/`), each with a machine-checked backward solution (`content/validation/`), a prerequisite DAG (`content/progression/core.json`), and a hint-intervention system (`content/guidance/`). The diagram-JSON loader files are byte-identical to main, so the puzzles load unchanged. Those puzzles are stated in backward orientation — the stored diagram is the goal, which is exactly what a pot hologram needs; the backward solutions flip to forward solvability certificates under the shared-implementation polarity-flip law. This corpus is interim content for implementation and will eventually be replaced by the propositional enumeration pipeline. Nine of the puzzles already exercise lemma citation.

## Tech

- **Codebase:** an isolated branch of the VisualProofAssistant repo, sharing `src/kernel` and `src/view3d`, merged-into as those improve; full separation into its own repo later. The proof assistant itself is an investigation platform with no maintenance obligation.
- **Shell:** a standalone Tauri app, scaffolded from the start of implementation (save-file I/O, window/input behavior, and packaging proven in the real shell throughout). Web tech inside: Vite + three.js, unchanged.
- **Saves:** unlimited named save slots backed by files, Skyrim-style. The save format always has one exact current shape: no format versions, version checks, migrations, legacy readers, or fallback parsing. Runtime worlds are constructed only by loading ordinary saves; developer and stress fixtures use the same persistence authority.
- **Scale:** the existing `src/view3d/transition.ts` tween machinery suffices for growth animation. Each changing tree owns its short tween independently, so several trees may animate concurrently. The established stress workload has proven static rendering, LOD, and culling to 2000 trees; generated game saves preserve that workload against the production renderer. Every tree uses the same kernel-backed model and can take the temporary per-frame render role when it changes.
- **Renderer authority:** `game/` is the sole 3D world frontend. Performance workloads are ordinary generated game saves, and stress tests exercise the same production renderer used by play.

## Deferred to implementation, by design

These are decisions the session explicitly ruled must be made in situ, not in this document:

- Gesture design for proof moves in 3D (starting from the 2D app's gestures where they transfer; some, like wire severing, will be redesigned entirely).
- The tool taxonomy: likely by building many overlapping candidate tools and keeping the covering subset that individually feels good. Constraint fixed now: the shipped tool set must be closed over the shipped catalog (every order solvable), and must cover the full calculus.
- Per-tool vocabulary and tutorial text.
- Per-domain interestingness criteria for the enumeration pipelines.
- Orchard aesthetics: the 3D shape of the world, region flavors, day/night, sound.
- Balancing: reputation values, unlock thresholds, DAG shape beyond the teaching spine.
- Backward reasoning at the pot (parked as a possible later feature).
