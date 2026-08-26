# Task 14 independent review

## Verdict

Rejected pending three Important fixes. The implementation uses the real menu,
proof, serializer/loader, replay, and GPU-picking paths, and all required focused
commands pass. However, the new browser coverage does not directly prove three
explicit Task 14 outcomes.

## Critical findings

None.

## Important findings

1. **The browser workflow never asserts that surface binder names are discarded
   and the persisted term payload is canonical nameless syntax.**

   In `e2e/construction.spec.ts:89-101`, the `editJson()` node type omits the
   serialized `term`, and the assertion checks only `freeArity`. In
   `e2e/interaction.spec.ts:258-267`, the post-spawn proof snapshot similarly
   reduces the term node to a count. After save/load,
   `e2e/interaction.spec.ts:320-333` narrows every step to its `rule`, and the
   replay assertion at `e2e/interaction.spec.ts:341-358` narrows nodes to their
   `kind`. Consequently, the browser test would still pass if `(\\x. x) a`
   leaked source binder names into the stored node/action or if either saved
   term payload were corrupted while retaining the same rule tag and node kind.
   Assert `A(L(B(0)),F(0))` after the real menu submission and in the loaded
   `lambdaTermSpawn` action, and assert the expected `F(0)` normal form at the
   converted/replayed state.

2. **Undo and redo are not validated as diagram-state transitions.**

   `e2e/interaction.spec.ts:293-298` checks only that clicking the real controls
   changes the history cursor from 2 to 1 and back. It never checks that undo
   restores the redex term or that redo restores its normal form while
   preserving the two unary caps and their incidences. A history implementation
   that updates cursor presentation but leaves the displayed/current diagram
   stale would satisfy this test. Assert the current structural term and
   cap/wire invariants after each control click.

3. **The 3D test proves Lambda metadata and GPU picking/focus, but not visible
   Lambda rendering.**

   `e2e/view3.spec.ts:15-19` establishes Lambda entities only in a Node-created
   `scene3`, while `e2e/view3.spec.ts:64-80` establishes that the browser's
   invisible picking geometry returns a `t:` key and can be focused. The
   renderer constructs the visible `Line2` and a separate invisible picking
   `THREE.Line` (`src/view3d/render.ts:167-181`), so absent or transparent
   Lambda display strokes could leave this test green. The existing ink
   readback at `e2e/view3.spec.ts:92-112` belongs to the empty-sheet trunk test
   and is not Lambda-specific. Add a real canvas readback or equivalent rendered
   artifact assertion at projected Lambda-stroke locations in addition to the
   existing GPU-pick/focus assertions.

## Minor findings

None.

## Confirmed behavior

- `examples/lambda.json` is accepted by `loadTheory`, verified, and replayed by
  both application and browser coverage; its shape matches the version-2 normal
  serializer schema.
- The construction test selects the exact `Lambda expression` row and asserts
  one term node, exactly two unary `IOTA` caps, two two-ended `IOTA` wires, and
  the `out`/`f:0` term incidences.
- The double-click candidate is first resolved through the real painted 2D
  stroke hit path before the conversion action is asserted.
- Save/download, file-input reload, library replay, 3D switching, GPU hover, and
  focus all use real application controls.
- Pipeline, session, and proof-snapshot code are generic over actions; their new
  representative Lambda tests do not weaken prior assertions. Lambda step JSON
  exhaustiveness already lives in the proof JSON layer. `scripts/emit-theories.ts`
  contains no proof-step switch, so it needs no Lambda case.

## Validation run

- `npx vitest run tests/app/pipeline.test.ts tests/app/session.test.ts tests/app/proof-snapshot.test.ts`
  — 3 files passed, 7 tests passed.
- `npx playwright test e2e/construction.spec.ts e2e/interaction.spec.ts e2e/view3.spec.ts`
  — 18 tests passed.
- `npm run typecheck` — passed.
- `git diff --check cf1be213..526dfc81` — passed.
