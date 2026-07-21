# In-place Head-strip Reduction Design

## Outcome

`headStrip` in TypeScript and Lean replaces a binary rigid-head equation with
the nontrivial equations between corresponding prefix-closed arguments. It no
longer retains the two source term nodes or their shared output wire. When all
argument positions are trivial, including the nullary rigid-head case, the
matched equation discharges completely.

The rule applies only when the equation has exactly the two selected term
attachments. An extra explicit endpoint is an ordinary additional attachment;
a wire scoped above the terms has an existential attachment, shown as a node in
the user-facing diagram. Both are already outside the binary-equation pattern.
Users must sever or deiterate that additional structure before applying
`headStrip`; no implementation may silently lose or preserve it.

The complete new ruleset retains the former append-only capability as a
derived operation. Iterate the complete local equation subgraph—both term
nodes and their internal output wire—into the same region, then apply
destructive `headStrip` to the copied equation. The original subgraph remains
because iteration owns copying; the argument equations remain because
`headStrip` owns reduction. No append-only head-strip executor is retained.

## Selected Model

The affected subgraph is exactly two distinct term nodes in one region plus
their shared self-contained binary output wire. Existing rigid-head,
head-normal-form, spine-alignment, and port-correspondence gates remain
authoritative. The concrete checks for extra explicit endpoints and an
external existential attachment run after identifying the shared output wire
and before any result is constructed; together they enforce one user-level
binary-equation condition.

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

The two selected terms are co-resident. If their shared wire is scoped above
their region, its user-visible existential node is an additional attachment,
so the pair is not a complete binary head-strip redex.

## Alternatives Rejected

Keeping the existing augmenting rule and adding a separate cleanup step leaves
two competing meanings for `headStrip` and preserves the reported root cause.
Allowing multi-endpoint output wires while deleting only the selected endpoints
would retain a weakened fragment rather than perform the selected equation
reduction. Deleting the entire multi-endpoint wire would lose the additional
equality. Both multi-endpoint variants are therefore rejected.

Retaining one selected term as an output-wire anchor is also rejected. In the
nonlocal or multi-endpoint shapes where such an anchor matters, the operation
is redundant-occurrence management rather than reduction of a complete local
equation. Iteration and deiteration retain ownership of copying and redundant
occurrence removal.

## TypeScript Authority

`applyHeadStrip` performs all gates before mutation. The shared output wire must
contain exactly the two selected output endpoints, and its existential
attachment must be local to the nodes' region. A larger endpoint list raises a
`RuleError` that says the wire must be severed first; an external existential
attachment raises the same conceptual binary-applicability refusal.

The final `nodes` and `wires` records omit the selected nodes and shared output
wire from the outset. Surviving wires filter the selected nodes' endpoints;
new argument nodes attach only to those surviving wire IDs. `mkDiagram` remains
the sole final structural validator.

Tests observe the final graph, not source substrings: source nodes and the old
equation wire are absent, nontrivial argument equations are present with the
expected support, a trivial/nullary equation discharges, unrelated structure
survives, and an ordinary or existential third attachment is refused without
changing the input. A system-level test iterates the complete equation and
head-strips the copy, then verifies directly that the original equation and
exactly the expected argument equations remain.

## Lean Authority

`HeadStripPayload` proves that the shared output wire has exactly the two
selected explicit endpoints and no external existential attachment. These are
the representation-level components of the same binary-applicability contract
used by TypeScript.

The executable raw transformation uses the established concrete survivor-domain
machinery to remove the two selected nodes and the shared output wire, then adds
the compacted argument-equation nodes and wires to that frame. Provenance and
interface transport map surviving source wires through the survivor domain and
map no source wire to a fresh argument-equation wire.

The semantic proof establishes full replacement equivalence. The forward
direction derives corresponding argument equalities from the shared rigid-head
equation. The backward direction uses congruence of application and lambda
abstraction to reconstruct equality of the removed aligned rigid-head terms
from every corresponding argument equality. A proposition whose conclusion is
only `original ↔ original ∧ arguments` is not an acceptable soundness statement
for the primitive replacement rule.

The former append behavior is proved separately as composition of the
authoritative iteration result and the authoritative destructive head-strip
result. It may have helper theorems describing that composition, but it must
not introduce an append-expanded raw diagram or alternate head-strip result.

## Interaction and Documentation Migration

The connection-drag interaction remains a way to select the two outputs, but a
same-wire drag on a wire with a third endpoint now receives the kernel refusal.
The earlier head-strip interaction design and tests that describe exact-pair
selection while retaining a multi-output wire are updated to the binary-only,
destructive behavior. A planner may offer the old append capability as one
multi-step action containing iteration followed by head-strip; serialization
continues to record only those ordinary primitive steps.

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
allowed. It must also find no append-expanded raw head-strip diagram or
survivor/anchor branch. A TypeScript macro test and Lean composition theorem
must demonstrate the former append-only result through iteration followed by
destructive head-strip. `git diff --check` and the formal placeholder audit
must also pass.
