# In-place Head-strip Reduction Design

## Outcome

`headStrip` in TypeScript and Lean replaces a binary rigid-head equation with
the nontrivial equations between corresponding prefix-closed arguments. It no
longer retains the two source term nodes or their shared output wire. When all
argument positions are trivial, including the nullary rigid-head case, the
matched equation discharges completely.

The rule refuses an output wire with any endpoint beyond the two selected term
outputs. Users must sever a multi-endpoint equality before applying
`headStrip`; no implementation may silently lose or preserve the additional
equality.

## Selected Model

The affected subgraph is exactly two distinct term nodes in one region plus
their shared binary output wire. Existing rigid-head, head-normal-form, spine
alignment, and port-correspondence gates remain authoritative. The binary-wire
gate runs after identifying the shared output wire and before any result is
constructed.

On success, the result is built from survivors rather than from an augmented
copy:

1. compute the nontrivial corresponding argument pairs;
2. remove both selected term nodes and the shared output wire;
3. remove their endpoints from every surviving support wire;
4. add two prefix-closure nodes and one binary output wire for each nontrivial
   argument position; and
5. attach each new closure's actual free support to the corresponding surviving
   host wires.

Unrelated regions, nodes, wires, scopes, and endpoints remain unchanged modulo
Lean's dense-index reindexing. No retained-original alias, compatibility mode,
or augmenting head-strip path remains.

## Alternatives Rejected

Keeping the existing augmenting rule and adding a separate cleanup step leaves
two competing meanings for `headStrip` and preserves the reported root cause.
Allowing multi-endpoint output wires while deleting only the selected endpoints
would retain a weakened fragment rather than perform the selected equation
reduction. Deleting the entire multi-endpoint wire would lose the additional
equality. Both multi-endpoint variants are therefore rejected.

## TypeScript Authority

`applyHeadStrip` performs all gates before mutation. The shared output wire must
contain exactly the two selected output endpoints. A larger endpoint list raises
a `RuleError` that says the wire must be severed first.

The final `nodes` and `wires` records omit the selected nodes and shared output
wire from the outset. Surviving wires filter the selected nodes' endpoints;
new argument nodes attach only to those surviving wire IDs. `mkDiagram` remains
the sole final structural validator.

Tests observe the final graph, not source substrings: source nodes and the old
equation wire are absent, nontrivial argument equations are present with the
expected support, a trivial/nullary equation discharges, unrelated structure
survives, and a third endpoint is refused without changing the input.

## Lean Authority

`HeadStripPayload` proves that the shared output wire is binary in addition to
proving both selected output occurrences. This is the formal counterpart of the
TypeScript refusal gate.

The executable raw transformation uses the established concrete survivor-domain
machinery to remove the two selected nodes and the shared output wire, then adds
the compacted argument-equation nodes and wires to that frame. Provenance and
interface transport map surviving source wires through the survivor domain and
map no source wire to a fresh argument-equation wire.

The semantic proof establishes full replacement equivalence. The forward
direction derives corresponding argument equalities from the shared rigid-head
equation. The backward direction uses congruence of application and lambda
abstraction to reconstruct equality of the removed aligned rigid-head terms
from every corresponding argument equality. The old proposition and proof
whose conclusion is `original ↔ original ∧ arguments` are removed or replaced;
they are not an acceptable statement of the new rule.

## Interaction and Documentation Migration

The connection-drag interaction remains a way to select the two outputs, but a
same-wire drag on a wire with a third endpoint now receives the kernel refusal.
The earlier head-strip interaction design and tests that describe exact-pair
selection while retaining a multi-output wire are updated to the binary-only,
destructive behavior. Serialization and composition shapes do not change.

## Validation

The TypeScript regression tests must first fail against the augmenting
implementation for source-node removal, equation-wire removal/discharge, and
multi-endpoint refusal. Lean checking must fail against the old payload/raw
model once the new binary and replacement statements are introduced.

Completion requires fresh successful results from the focused TypeScript rule
and interaction tests, the ordinary TypeScript suite, type checking, formal tag
correspondence, and `lake build`. A repository search must find no active
head-strip comment, test, theorem, or design statement that says the originals
remain, all-trivial stripping is a no-op, or multi-endpoint stripping is
allowed. `git diff --check` and the formal placeholder audit must also pass.
