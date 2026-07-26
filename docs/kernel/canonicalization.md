# Phase-1 kernel canonicalization

This document describes the canonical Phase-1 TypeScript graph model. The
signature authority is `src/kernel/diagram/sig.ts`, eager identity normalization
is owned by `src/kernel/diagram/canonical/identity.ts`, canonical graph labeling
is owned by `src/kernel/diagram/canonical/explore.ts`, and exact occurrence
matching is owned by `src/kernel/diagram/subgraph/match.ts` together with the
independent certificate checker.

## Signatures and graph objects

The wire-signature grammar is exactly:

```text
Sig ::= iota | rel(Sig, ...)
```

`iota` is the individual signature. `rel(args)` is a relation signature whose
ordered argument list may be empty and may recursively contain either signature
form. Signature equality is recursive structural equality; `sigKey` is an
injective structural serialization.

A diagram contains regions, nodes, and wires:

- Regions form a tree with one `sheet` root and zero or more `cut` children.
- Nodes have exactly three kinds: `atom`, `ref`, and `identity`.
- Wires have a region scope, a signature, and an unordered endpoint set.

An `atom` carries a relation signature. Its `head` port and ordered `arg`
positions are canonical content. A `ref` carries a definition id and a relation
signature; its `arg` positions are ordered canonical content. An `identity`
carries one signature and an arity of at least two.

Identity ports have integer incidence indices only because the stored diagram
needs distinct addresses for its endpoints. Those indices are not semantic
positions. Canonicalization and occurrence checking discard the index and
preserve the unordered multiset of incident wires.

## Eager identity normalization

Every public construction and rewrite normalizes identities before exposing the
result. The normalizer validates the raw graph, then applies the first available
rule in this fixed priority:

1. Degeneracy drop: delete the lexicographically first identity incident to
   fewer than two distinct wires.
2. Co-scoped collapse: when every incident wire is scoped in the identity's own
   region, delete the lexicographically first eligible identity and merge its
   wires. The lexicographically first wire survives; non-identity endpoints are
   unioned into it.
3. Same-region fusion: for the lexicographically first pair of identities in
   one region that share a wire, keep the lexicographically first node, delete
   the other, and rebuild the survivor from the sorted set of distinct incident
   wire ids.

After one rewrite the graph is validated again and rule selection restarts at
Rule 1. Normalization stops only when none of the three rules applies, so the
result is a fixpoint. Sorted node ids, sorted incident wire ids, fixed rule
priority, and lexicographically selected survivors make the result
deterministic.

The returned `wireImage` maps every input wire to its surviving output wire or
to `undefined` when no wire survives. When Rule 2 absorbs wires, all composed
images are redirected to the selected survivor and path-compressed before the
receipt is returned. Proof steps use that receipt to transport boundary and
action wire identities across eager normalization.

## Exact canonical graph labeling

The canonical explorer treats a diagram as a colored port hypergraph. Initial
colors contain only local isomorphism-invariant data:

- region kind;
- node kind, signature, identity arity, and ref definition id;
- an ordered boundary-incidence vector for each pinned wire.

Each refinement round combines an object's previous color with neighbor colors:

- region children, resident nodes, and scoped wires enter as sorted multisets;
- atom/ref positional ports retain their port keys;
- an identity's incident wire colors are sorted before entering its node
  signature;
- wire endpoint signatures are sorted, and wire scope and wire signature are
  retained.

Identity incidence indices never enter initial coloring, refinement, or
serialization. Only the unordered identity-neighbor multiset is refined.

Refinement is split-only because every new signature includes the old color.
The number of color classes therefore increases monotonically until it
stabilizes. If a class remains tied, the explorer individualizes every member
of the first tied class in turn, re-refines, and recursively keeps the
lexicographically least discrete serialization. It never chooses one
representative heuristically.

At a discrete leaf, objects are ordered by their unique colors and serialized
with the complete region tree, node content, wire signatures and scopes,
positional atom/ref ports, unordered identity incidences, endpoint sets, and
ordered boundary pin vector. Equal canonical strings hold exactly when the
bounded diagrams are structurally isomorphic.

The individualization search is exponential in the worst case. That is the
cost of an exact invariant for highly symmetric graphs; it does not weaken the
comparison.

## Exact structural occurrence matching

`findOccurrences` performs an exhaustive injection search over host regions,
nodes, and wires. A candidate must preserve:

- region placement and the exact contents of every proper selected subtree;
- node kind, region, recursive signature, identity arity, and ref definition id;
- positional atom/ref endpoints;
- exact internal wire scope, signature, and endpoint set;
- ordered boundary attachments, allowing only the intended extra host
  endpoints at the open boundary;
- the full unordered incident-wire multiset of every identity node.

Every emitted occurrence is checked again by
`checkOccurrenceCertificate`. The certificate records only graph maps and
ordered boundary attachments.

`explorationFuel` is the sole optional bound. It limits graph-candidate probes,
not comparison semantics. Exhausting it returns `status: 'exhausted'`; that
status is not evidence that no occurrence exists. Without a bound, the finite
candidate space is explored completely.

Canonicalization and occurrence matching perform no beta-eta comparison and
have no semantic term-equivalence channel. Phase-1 equality decisions are
recursive signature equality and exact graph structure only.
