# Session regression repair design

## Outcome

Restore zero-failure ordinary validation by completing the cursor-timeline migration and returning all proof-front canvas rendering to the existing canvas adapter. Redo behavior remains intact, and no test is weakened to conceal a regression.

## Proof timeline contract

`ProofTimeline` contains retained history and a cursor:

- `states` retains every reachable diagram in the current redo line.
- `transitions` retains the proof step between each adjacent state.
- `cursor` selects the current state.
- `timelineActiveSteps(timeline)` returns `transitions.slice(0, cursor)` and is the only representation of the current derivation.

Undo and redo move only the cursor. Applying at an earlier cursor truncates future states and transitions before appending. Theorem declaration, fixed-side assembly, pipelines, and assertions consume `timelineActiveSteps`; they never interpret raw retained transitions as active proof steps.

The former `steps` field is renamed, not aliased. There is no compatibility path preserving its ambiguous meaning.

## Canvas ownership

`CanvasAdapter` remains the sole owner of `CanvasRenderingContext2D`. Its render input becomes a frame containing:

- an optional background color; and
- ordered layers, each with shapes and an optional alpha value.

The adapter clears once, fills the background when supplied, and draws layers in order. Each layer's alpha is isolated with save/restore so it cannot leak to later layers.

`ProofFrontViewport` stores a `CanvasAdapter`, not a browser context. Its base diagram, hover highlight, and motion overlay become three frame layers. Direct context acquisition, clearing, filling, alpha mutation, and `drawShapes` calls are deleted from the app component.

## Validation

Session tests prove retained redo history, active-prefix behavior, redo restoration, divergent truncation, and theorem assembly. Canvas tests prove background fill, ordered rendering, and alpha isolation. The existing architecture test must find no application reference to `CanvasRenderingContext2D`. Typecheck and the complete ordinary suite must pass with zero failures. Physics tests are not run because physics is unchanged.
