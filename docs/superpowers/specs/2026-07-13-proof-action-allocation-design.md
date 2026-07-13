# Proof Action Allocation Reservations

## Outcome

A proof action planned from one diagram can replay on a separate destination
without introducing a region, node, or wire ID owned by either namespace. The
same deterministic allocation governs scratch planning, live application,
serialization, theorem verification, composition, iteration, and later steps
that reference IDs introduced earlier in the action.

## Representation

`ProofAction` gains optional non-logical `allocation` metadata:

```ts
type ProofAllocation = {
  readonly regions: readonly RegionId[]
  readonly nodes: readonly NodeId[]
  readonly wires: readonly WireId[]
}
```

These arrays are exclusion namespaces, not logical operands and not promises
that any particular ID will be allocated. CopyPlanner stores the complete
source namespaces in sorted order. Empty allocation is absent from the action
and omitted from JSON, preserving the existing serialized shape and replay
behavior. JSON parsing validates the three arrays and rejects duplicate IDs so
one action has a canonical exclusion set.

At runtime the arrays convert once to an immutable `IdReservation` containing
three read-only sets. This is the only runtime reservation representation.

## Replay and allocation flow

`applyAction` validates and converts its optional allocation, then passes the
same reservation to every constituent `applyStep` call. `applyStep` keeps an
optional final reservation parameter whose default is empty, so direct callers
retain current behavior. Every fresh-producing rule reachable through
`ProofStep` passes the relevant reserved set to the canonical `freshId`
allocator or passes the complete reservation to a nested splice.

`freshId` chooses the first candidate absent from both the live taken set and
the supplied reserved set. Reservations do not change rule gates, diagram
content, or logical results.

CopyPlanner creates one `ProofAllocation` from the source diagram before
candidate generation. Its scratch compiler applies steps with the derived
runtime reservation, and every candidate action carries the same allocation.
Consequently IDs discovered during scratch application are exactly recreated
during live replay, including IDs named by later steps.

Iteration, comprehension, relation unfolding, theorem application, and every
other nested structural splice receive the same action reservation. No dummy
nodes, global state, post-step renaming, or ID-insensitive freshness check is
used.

## Persistence and composition

Action JSON includes `allocation` only when at least one namespace is nonempty.
Theorem JSON inherits this through its action arrays, so saving/loading and
theorem verification use ordinary `applyAction` with the restored exclusions.

`composeActions` applies each source action's reservation while replaying both
meet sides, preserves that allocation on the composed action, and continues to
map only logical host operands through the evolving isomorphism. Exclusion IDs
are not host references and are therefore never isomorphism-mapped.

## Validation and errors

Malformed allocation metadata fails as malformed proof JSON. Direct action
application rejects empty IDs or duplicate entries before applying a step.
Reservation arrays may overlap across region/node/wire namespaces because
those namespaces are independent.

Tests directly cover independent cross-diagram node, wire, and region
collisions; a multi-step recipe whose later step names a reservation-shifted
earlier region; persisted action/theorem replay; composed allocation; nested
iteration/splice allocation; malformed metadata; and omission/default behavior
for ordinary actions.
