# Curse-Breaker Current-Main Engine Integration Design

## Outcome

The curse-breaker game uses the TypeScript proof model from `origin/main` at
`d0c3eae`, preserves the meaning and ordering of all authored game content, and
provides a visible game interaction that can author every retained proof rule.
Proof history, completed artifacts, saves, and build-time witnesses all use the
same authenticated action model.

## Considered approaches

### Selected: reconstruct the TypeScript proof domain and migrate the game

Import the complete entangled TypeScript kernel from current main, then make
`ProofAction` and authenticated `ProofContext` the single authorities throughout
the game. Extract main's reusable interaction mechanics into a product-neutral
layer, adapt the game viewport around them, and add the two direct gestures main
does not yet provide (`wireSever` and `anchoredWireSplit`). Regenerate validation
sidecars from unchanged authored puzzles.

This is the only approach that preserves the new rule invariants without keeping
the old model alive beside them.

### Rejected: merge all of current main

This would also import the retired proof-assistant shell and the Lean formalization,
neither of which belongs to the curse-breaker product. It creates ownership and
package conflicts unrelated to the requested TypeScript engine update.

### Rejected: copy only rule files

The rules now depend on authenticated contexts, occurrence certificates, receipts,
port correspondence, allocation reservations, action replay, and changed diagram
representations. A rule-only copy would compile only by recreating adapters around
the displaced model and would not authenticate artifacts or saves.

## Responsibility model

### Kernel

`src/kernel/diagram`, `src/kernel/term`, `src/kernel/rules`, and `src/kernel/proof`
own all proof semantics. The kernel accepts only authenticated contexts, validates
certificates and correspondence, reserves fresh identifiers, applies atomic steps,
and applies a whole `ProofAction` as one user operation. No UI module fabricates
legality, theorem authority, or proof evidence.

### Interaction mechanics

A product-neutral interaction layer owns geometry and gesture lifecycle:
connection dragging, fission dragging, selected-pattern copying, proof spawning,
hit testing, cancellation, and pure conversion of recognized gestures into kernel
actions. It imports kernel, view, and shared hit contracts only. It does not know
game progression, artifacts, or the assistant shell.

### Game interaction router

The game owns arbitration and game vocabulary. Its proof router orders competing
gestures, fixes backward proof orientation, opens the construction loupe, supplies
game labels, and routes the resulting `ProofAction` through one controller action.
The construction loupe retains its genuinely game-specific cross-surface draft
connection workflow. Artifact drag remains the sole theorem-use interaction.

### Session and completed artifacts

An active timeline contains ordered `ProofAction`s and one derived diagram state
per action. Undo position and move count refer to user actions, never constituent
steps. A first puzzle completion moves the retained backward action witness into an
insertion-ordered `CompletedArtifact` map. The completed-ID set, unlock state, and
available artifacts are projections of that map.

Each completed artifact registers a theorem with canonical blank as `lhs`, the
authored puzzle start as `rhs`, no forward actions, and the retained backward
actions as `backActions`. Registration starts from the authenticated catalog base
context and proceeds in completion order, so dependencies are available exactly
when earned.

### Save and content validation

The new save version serializes action timelines and ordered completed artifacts.
Loading replays each completion from its puzzle start to blank, verifies its unlock
position, and registers its theorem before decoding later dependents. Step-shaped
timelines and bare completed IDs are rejected; no legacy decoder remains.

Build-only validation sidecars also store actions. Their 1,039 user moves remain
1,039 actions. Deiterations acquire explicit evidence at their original replay
state, the empty comprehension binder record becomes an ordered empty array, and
the four insertion moves become single multi-step actions whose canonical result
matches the old move. `expectedRules` is derived by flattening action steps.
Puzzles, manifest, catalog, progression, guidance, and coverage remain byte-identical.

## Complete interaction contract

| Rule | Game interaction |
| --- | --- |
| `openTermSpawn` | context-click region, spawn term |
| `closedTermIntro` | context-click region, spawn closed term |
| `relationSpawn` | context-click region, spawn relation |
| `boundRelationSpawn` | context-click region, spawn bound predicate |
| `wireJoin` | drag between distinct ordinary wires |
| `congruenceJoin` | drag compatible endpoints with congruent heads |
| `anchoredWireContract` | drag distinct wires through a closed witness |
| `anchoredWireSplit` | drag a closed witness output to a distinct endpoint on the same wire |
| `headStrip` | drag between two term outputs on one equality wire |
| `wireSever` | proof slash across concrete endpoint legs; trunks and junctions refuse |
| `erasure` | contextual Delete/Backspace |
| `doubleCutElim` | contextual Delete/Backspace |
| `vacuousElim` | contextual Delete/Backspace |
| `inconsistentCutElim` | contextual Delete/Backspace with undecided refusal preserved |
| `deiteration` | contextual Delete/Backspace using certified evidence |
| `iteration` | drag selected semantic surface into a region |
| `doubleCutIntro` | W or menu |
| `vacuousIntro` | Shift+W |
| `conversion` | double-click normalization or menu-selected target |
| `fusion` | F on selected wire or double-click wire |
| `fission` | pull an internal term occurrence into its direct region |
| `comprehensionInstantiate` | selected bound bubble to named relation or construction loupe |
| `comprehensionAbstract` | Shift+W relation-abstraction transaction |
| `theorem` | drag an earned artifact onto an exact occurrence or empty region |
| `relUnfold` | contextual menu |
| `relFold` | contextual menu |

Connection arbitration is deterministic: different-wire connection rules precede
same-wire `headStrip`/`anchoredWireSplit`; fission precedes copy; ordinary selection
runs only when no proof gesture claims the pointer. Contextual deletion orders
double-cut, vacuous, inconsistent-cut, erasure, then deiteration. Blur, visibility
loss, modifier changes, and cancellation clear all gesture state.

## Complexity ledger

| Category | Selected treatment |
| --- | --- |
| Essential behavior | Current-main rule semantics; backward game proof; all 26 rule interactions; unchanged logical content; authenticated artifacts |
| Essential state | Active action timeline; derived diagram states; ordered completed action witnesses; settings and puzzle selection |
| Invariants | Authenticated contexts only; one gesture equals one action; replay reaches canonical blank; artifact authority is registered, not fabricated; fresh IDs are reserved atomically |
| Derived state | Completed IDs, unlocks, available artifacts, move count, puzzle fingerprints, interaction affordances |
| Accidental state to delete | Step timelines, parallel completed-ID set, plain context maps, empty synthetic theorem histories, validation step arrays |
| Accidental control flow to delete | Shadow rule discovery, local certificate synthesis, hand-applied action constituent steps, fallback save decoding |
| Accidental code volume to delete | General insertion, endpoint transport, fuel deiteration, duplicate game gesture implementations, obsolete codecs and fixtures |
| Power leaks to remove | Arbitrary insertion, mutable/unbranded contexts, UI-created theorem authority, allocation outside an action |

No ledger category remains unknown. The retained complexity corresponds to proof
semantics, gesture disambiguation, or durable authentication.

## Failure handling

Kernel refusal is authoritative and must not be converted into a success-shaped
fallback. An undecided inconsistent-cut check reports refusal and stops contextual
deletion; a certified miss may proceed to later deletion candidates. Save decoding
fails closed on bad fingerprints, unavailable prerequisites, invalid action JSON,
failed replay, non-blank completion, or theorem-registration failure. Gesture
controllers cancel cleanly without mutating session state.

## Decisive validation

1. Synchronize and run current-main TypeScript kernel/proof tests.
2. Prove all 26 tags have event-driven game tests that emit and successfully apply
   their actions, including lifecycle and arbitration cases.
3. Replay all 109 validation solutions as 1,039 actions to canonical blank.
4. Round-trip active and completed action histories through the new save format and
   reject the displaced format.
5. Prove manifest, puzzle, catalog, progression, guidance, and coverage files are
   unchanged from branch commit `3b4c6f9`.
6. Run typecheck, focused tests, full tests, content validation, desktop build,
   startup smoke, and browser interaction tests.
7. Search source, tests, schemas, and JSON for every displaced representation and
   assert the game has no `src/app` dependency.
