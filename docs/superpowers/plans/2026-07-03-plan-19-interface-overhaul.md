# Plan 19: The interface overhaul — interaction design first

**USER DIRECTION (2026-07-03):** the overhaul is NOT just visuals/layout — "it also means things related to interaction. For example, applying different rules, connecting wires… right now almost none of these feel very good to actually interact with." Process correction from the render rounds: "you weren't very thorough on what does and doesn't get demoed… started asking about things that relied on previous things that weren't demoed. Some planning for thoroughness would go a long way." Therefore: the COMPLETE component inventory below is the contract; every item is assigned to a demo round; no round consults the user on anything whose prerequisites have not themselves been demoed and decided. The user is the design eye (collaboration protocol in rendering-laws memory): each round presents MULTIPLE genuinely different mechanisms as WORKING demos against the real engine, never sketches.

## The complete inventory

### A. Direct manipulation on the sheet (the foundation — everything else composes with it)
- A1 Selection: what a click/tap selects (node, wire, region); multi-select; deselect; marquee/lasso; visual selection state; what HOVER communicates (selectable? draggable? valid target?)
- A2 Moving: body drag, region drag (exists — feel re-judged in context), pinned-vs-released semantics (arrangement persists, position doesn't — standing design question)
- A3 Zoom (fixed background — settled law) + any focus/navigate affordance (double-click to zoom-to-region?)
- A4 Undo/redo: depth, visibility, keyboard; redo currently absent
- A5 Wire connection (join): today click-wire, click-wire, press button — candidate mechanisms: drag from line-end to line-end; drag port-to-port; magnetic snap on release
- A6 Wire severing: today a rule buried in menus — candidate: cut gesture (stroke across a wire), select+key
- A7 Node creation (term): today a λ-text box + Add — candidates: text box retained but placed well; palette drag-out; on-canvas radial create; structured term builder
- A8 Node creation (relation refs): today chooser buttons — candidates: palette of known relations; drag from Library entry onto the sheet
- A9 Cut/bubble creation: today select+wrap button — the Peirce-native candidate: DRAW the circle around content (lasso = cut); modifier for bubble+arity
- A10 Delete: select+button — candidates: key, drag-to-void, gesture

### B. Rule application (the proving interactions — depends on A's selection/gesture vocabulary)
- B1 Rule discovery/browsing: how the user learns what applies HERE (today: text-button menu appears after selection). Candidates: contextual menu (radial/linear) at the selection; always-visible rule palette that lights up by applicability; hover-preview of each rule's RESULT (ghost diagram) before commit
- B2 Rules with a target (iteration into a region; insertion): pick-target second phase vs drag-the-selection-into-the-region as a gesture
- B3 Rules with arguments (theorem citation): the two-phase wire picking — inference where possible (fold already infers); citing = choose theorem, args inferred when unambiguous, picked otherwise
- B4 Conversion (βη): term input + fuel on a node — candidates: normalize button + step-wise reduction preview; inline term editing
- B5 Polarity awareness: making positive/negative visible where it gates rules (region shading exists; is it enough?)
- B6 Structural rules (double cut, vacuous, erasure, severing): discoverability + gesture mapping per A
- B7 Comprehension instantiate/abstract: the most parameter-heavy flows — staged wizards vs in-place picking
- B8 Refusal presentation: kernel messages are the UX copy (law) — WHERE they land (status line vs anchored at the refusing thing) and how they persist

### C. The proof model surface (depends on B)
- C1 Goal setting: LHS/RHS snapshots — today two buttons over the live sheet; candidates: explicit goal panel; drag current sheet into a goal slot; goal-first workflow framing
- C2 Session/meet presentation: forward vs backward sides, the meet check, side switching — today a toggle + status text; candidates: two-lane view (companion is the seed), explicit meet indicator
- C3 Derivation history: the recorded steps — today invisible except Undo; candidates: step list/timeline with jump (replay machinery already supports it)
- C4 Assemble/check/name: theorem naming input + assemble — placement and flow
- C5 Replay: stepping UI (buttons/keys exist) — scrubber/timeline; step labels; entering/leaving replay
- C6 The companion (PiP/split): default state, placement, interaction with modes (machinery shipped in plan 17)

### D. Chrome assembly (depends on A–C decisions — LAST, not first)
- D1 Overall layout: where library/actions/status/inputs live; what is permanent vs contextual
- D2 Mode identity: EDIT/PROVE/REPLAY made visually unmistakable
- D3 The Library panel: files, load state, session group, per-theorem actions
- D4 Status/messaging surface (with B8)
- D5 Theme system (LIGHT/DARK settled as looks; chrome must join them)
- D6 Keyboard map + power-user layer
- D7 Text inputs that remain (λ-terms, names, fuel): placement, validation feedback

### E. Motion & feedback polish (throughout, judged at the end)
- E1 Rule-application transitions (today: rebuild + resettle; candidate: staged morphs)
- E2 Physics feel parameters in final context
- E3 Hover/selection animation timing

## Demo rounds (dependency-ordered; each round = 3–4 working variants per question, real engine, user judges)

- **Round 1 — A1 selection + hover vocabulary.** Everything downstream reads through it. Variants differ in what hover shows and how selection accumulates/clears.
- **Round 2 — A5/A6/A9 construction gestures** (join, sever, draw-a-cut) + A7/A8 creation. Uses Round 1's selection.
- **Round 3 — B1/B2 rule application model** (discovery + targeting), on Round 1–2 vocabulary. The biggest single feel item.
- **Round 4 — B3/B4/B7 parameterized flows** + B8 refusals.
- **Round 5 — C1–C5 proof model surface** (goals, sides, history, replay).
- **Round 6 — D assembly**: full chrome variants integrating all prior decisions; C6 placement; D2 mode identity.
- **Round 7 — E polish pass** on the winner.

Rule of the process: a round's demos may ONLY depend on machinery already decided in earlier rounds (or shipped pre-overhaul). If a variant needs an undecided dependency, it moves to the round after that dependency. The inventory above is the checklist — every item gets a ⟨round, decided-in, verdict⟩ record as the rounds complete.

- [x] Round 1 demos built and judged. **VERDICT (user, 2026-07-03): A1 = variant D's brush** — drag paints items in/out of the selection, plain click toggles one, empty click clears (subsumes B's shift-click toggle, which the user liked); B judged strictly better than the current model, D a step above B. **Required fix adopted:** hover must stay visible on already-selected items (B's darkening vanished there; on wires there was NO signal at all). Realized as `ui-lab/round1-e.ts`: hover on unselected = blue tint/stroke (the would-be catch); hover on selected = the amber darkens (dark-amber #92400e tint on nodes/regions, wider dark-amber restroke on wires); readout appends "— selected". Verified by screenshot on both the selected-wire and selected-node cases.
- [x] Round 2 demos built and judged. **VERDICTS (user, 2026-07-04):** A (verbs-on-selection) incremental — but context-aware menus are a good idea (feed into Round 3). B (direct gestures) directionally correct: drag-join and slash-sever KEEP; lasso too tedious for large diagrams — replace with select + Space = cut, Shift+Space = SO bubble; double-click-for-term is a wasted double-click. C: keep BOTH slash and double-click sever behind an options toggle (slash default); radial spawn menu = right idea, wrong implementation — cut does not belong in it, the trigger collided with selection, and it cannot scale to thousands of relations (**the spawn browser is its own design round, queued below**). Mechanical rulings, all realized in `round2-d` (the composite): N-ary join (J joins all selected lines); sever immediate (no pick-again phase); selecting a cut + its contents wraps the subtree once (absorbHits); Delete works across regions and DISSOLVES selected boundaries (contents propagate up, selected contents die); drag a selected node to MOVE it between regions (reparent with wire-scope correction — wholly-owned wires travel, shared wires keep scope when valid, else tightest common ancestor). Physics discovery: regions dodge an approaching dragged node (sibling repulsion), so placement drags FREEZE settling until release. App-level findings to port at integration: (1) `edit.ts wrap()` leaves wholly-enclosed wires scoped OUTSIDE the new cut — semantic mismatch with what drawing a circle around them says; (2) `hitTest` claims a region's whole disc, so "empty space inside a cut" never exists for click/dblclick triggers — any spawn-menu trigger must not depend on hitting nothing.
- [ ] Round 2b — the spawn browser (own design project per user ruling). BUILT, awaiting verdict: three surfaces inside the full composite, browsing a synthetic 140-relation/11-namespace library (`ui-lab/library.ts`; composite factored to `ui-lab/composite.ts`). **A — command palette** (`/` at cursor: ranked substring search, ↑↓+Enter, `\…` = λ-term, empty query = recents; spawns at invocation point — key trigger, so region discs can't eat it). **B — library panel** (folding sidebar: search + namespace groups + recents; rows drag out; drop point = region). **C — contextual cascade** (STILL right-click opens menu at point — right-drag still slashes, selection untouched; search row, λ-term, recents, namespace submenus on hover; spawns at the clicked point, inside cuts included). All 13 gesture checks green. Observed for integration: long namespaced defIds truncate on the node disc — label display needs a rule (e.g. name sans namespace).
- [ ] Round 3 demos built and judged.
- [ ] Round 4 demos built and judged.
- [ ] Round 5 demos built and judged.
- [ ] Round 6 demos built and judged.
- [ ] Round 7 polish; integration plan filed (laws-as-tests, like plan 13 did for rendering).
