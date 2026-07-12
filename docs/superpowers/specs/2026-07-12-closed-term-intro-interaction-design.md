# Closed-term introduction interaction design

## Outcome

Proof mode uses the existing term-spawn cascade to author `closedTermIntro`. A blank-region secondary click opens the same λ-term entry used in Edit mode. Closed terms commit as proof steps; open or malformed terms are refused without closing the cascade.

## Shared interaction

`SpawnCascade` remains the sole spawn presentation and term-entry implementation. It continues to capture the invocation screen point, world point, and region and delegates submission through its existing `spawnTerm` callback.

Host policy differs by mode:

- Edit parses and constructs any well-formed term node through `addTermNode`.
- Proof parses the same source, requires zero free ports, and records `{ rule: 'closedTermIntro', region, term }` through the ordinary proof commit path.

Proof opens the cascade with empty relation and bound-predicate catalogs, so only λ-term spawning appears. Edit retains its complete relation and binder catalog. There is no proof-menu action, separate prompt, or alternate spawn component.

## Gesture routing

In Proof mode, a secondary click in unselected blank space opens spawning in the smallest containing region. Right-clicking a selected object or diagram object continues to open the existing proof context menu. The transverse slash remains Edit-only wire severing.

Both the main single-track proof canvas and fixed-side proof fronts expose the same routing and cascade implementation.

## Commit and placement

`closedTermIntroStep(source, region)` parses and provides immediate open-term feedback. The kernel applier remains authoritative at commit and replay.

After the synchronous non-conversion proof commit rebuilds the view engine, the host identifies the newly minted node and seeds its body at the captured world point. Thus Edit and Proof spawning share not only the menu but the placement affordance.

## Validation

Tests cover helper parsing/closure, cascade persistence on refusal, blank-region versus object context routing, main and fixed-side proof-step recording, invocation placement, Proof catalog restriction, undo/replay, and absence of a competing menu/prompt path. Typecheck and all ordinary tests must pass with zero failures. Physics tests are not run.
