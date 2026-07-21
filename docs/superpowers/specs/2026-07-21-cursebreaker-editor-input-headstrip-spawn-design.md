# Cursebreaker Editor Input, Head-Strip, and Spawn Design

## Outcome

Cursebreaker uses one predictable destructive-key contract, restores the authoritative head-strip transformation, and makes empty structural boundaries directly spawnable during relation construction.

## Keyboard Ownership

Keyboard meaning belongs to the active context:

- A focused text field retains native `Delete` and `Backspace` editing.
- A focused construction canvas sends both keys through the same construction-deletion path.
- A focused puzzle canvas sends both keys through the same contextual proof-operation path.
- `Escape` dismisses the active prompt, menu, or construction interface.
- Neither `Delete` nor `Backspace` dismisses an interface.

The construction loupe therefore removes Backspace from its close resolver and from its close instructions. Text-entry guards continue to let the browser edit text. Non-text destructive keys fall through to the construction controller, where the existing selection-deletion operation owns both keys.

## Head-Strip Semantics

The implementation on `main` is authoritative. Head-strip accepts two distinct term nodes only when they form a self-contained binary equation in one region, have aligned head-normal rigid spines, and satisfy the supplied free-port correspondence.

The transformation replaces the equation. It removes the two source terms and their binary output wire, removes their endpoints from other wires, and creates fresh paired equations for each nontrivial aligned argument closure. A nullary or wholly trivial equation disappears completely. Extra equation endpoints and an equation wire scoped outside the nodes' region are rejected.

The additive Cursebreaker variant and tests that permit the source equation to survive are displaced, not retained as an alternate mode.

## Puzzle Destructive-Key Routing

`Delete` and `Backspace` share one resolver. Before generic contextual deletion, the resolver recognizes exactly two selected term nodes and constructs a `headStrip` step using their attached-port correspondence. The real kernel preflights the step; a valid step is committed, while an inapplicable pair falls through to existing deletion behavior.

This selection route is the only interaction affordance for head-strip. Same-wire output dragging no longer authors `headStrip`; connection gestures remain responsible only for connection operations. The drag-based head-strip route and the tests that encode it are removed rather than preserved as an alternate path.

## Construction Spawn Menu

The construction spawn cascade lists primitive choices in this order:

1. `λ term…`
2. `Empty cut`
3. `Empty quantifier bubble…`
4. available bound predicates
5. recent and namespaced relations

The cascade owns only menu rendering and callback dispatch. The construction loupe owns the draft mutations and routes them through its existing history and reconciliation seam.

`Empty cut` creates a fresh child cut in the invocation region with no contents. `Empty quantifier bubble…` opens a focused nonnegative-integer arity prompt; submission creates a fresh child bubble in the invocation region with no contents. Escape closes that prompt, while Delete and Backspace remain native editing keys within it.

## Validation

Implementation follows focused test-first cycles:

- construction-loupe key tests prove Escape closes and neither destructive key closes;
- browser tests prove native text deletion and the menu/prompt lifecycle;
- construction tests prove both destructive keys delete selected draft objects;
- kernel head-strip tests prove exact replacement semantics and structural gates;
- puzzle-controller tests prove both keys author the same head-strip step;
- connection tests prove dragging cannot author head-strip;
- spawn tests prove menu order and both empty-region callbacks;
- TypeScript type checking verifies the integrated contracts.

The physics suite is unrelated to these responsibilities and is not run.
