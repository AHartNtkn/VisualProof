# Canonicalization Algorithm

This document describes the exact canonical form for proof diagrams, as implemented in `src/kernel/diagram/canonical/`. The entry point is `canonicalForm` in `canonical.ts`; the fingerprint API in `fingerprint.ts` wraps it.

---

## Object model and what isomorphism preserves

A `Diagram` has three sorts of objects: **regions**, **nodes**, and **wires** (`diagram.ts`).

**Regions** form a tree rooted at the unique `sheet` region. Non-root regions are either a `cut` (a negation context) or a `bubble` (a quantifier context carrying an integer arity). A `cut` or `bubble` holds a `parent: RegionId` linking it toward the root.

**Nodes** are either a `term` node — carrying a well-formed Term and living in some region — or an `atom` node — carrying a `binder: RegionId` (always a bubble that encloses the atom) and also living in some region.

**Wires** carry a `scope: RegionId` (the quantifier that introduces the individual) and a list of `endpoints`, each of which is a node-id plus a `Port`. Ports on term nodes are `output`, `freeVar name`, or `arg index`; ports on atom nodes are `arg index` only. The wire endpoint set is a partition: every required port of every node belongs to exactly one wire.

Two diagrams are **isomorphic** if there exist bijections on regions, nodes, and wires that jointly preserve: the root region; region kind, parent, and bubble arity; node kind, region, atom binder, and term-node shape key (see below); wire scope and endpoint sets (by positional port key, see below). The canonical form is a string that is identical for isomorphic diagrams and distinct for non-isomorphic ones.

---

## Positional ports and the semantic justification

A term node's free-variable names are internal labels, not semantic content. Spec §2.2 defines a term node's denotation by its positional constructor relation: the function (arity, structure, argument order) where the free-variable names have been replaced by position-indexed slots `p0, p1, …` in first-occurrence order.

The function `termShapeKey` in `shape.ts` computes this. It calls `freePorts(t)` — which returns free port names in first-occurrence order — builds a rename map `name → p{i}`, applies it via `renamePorts`, then serializes the result with `serializeTerm`. Two term nodes that differ only in free-variable names get the same shape key and are treated as isomorphic at that level.

Wire endpoints also use positional keys. `positionalPortKey` in `shape.ts` maps `output → "out"`, `freeVar name → "v{i}"` where `i` is the name's index in `freePorts(t)`, and `arg index → "a{index}"`. The canonical form uses these keys for every endpoint in a wire, so it is invariant under consistent per-node free-variable renaming — which preserves semantics — while remaining sensitive to argument order, wiring topology, and everything else that matters.

---

## Initial coloring

`initialColors` in `canonical.ts` assigns each object an integer color based solely on its local, isomorphism-invariant content, with no reference to ids or neighbors.

Regions are tagged with their kind key: `"R|sheet"`, `"R|cut"`, or `"R|bubble/{arity}"`. Nodes are tagged with their content key: `"N|atom"` for atom nodes, `"N|term:{shapeKey}"` for term nodes. A boundary-pinned wire is tagged with the ordered vector of every boundary position exposing that identity, `"W|pins[i,…]"`; all other wires are tagged `"W|w"`.

The function `rankSignatures` collects all these signature strings, sorts them lexicographically, and assigns rank integers 0, 1, 2, … in order. Every object's color is the rank of its signature. Objects with identical local content receive the same initial color; objects with different content receive different ones.

`buildIndex` in `canonical.ts` pre-computes all adjacency relationships used by refinement and serialization: parent/children for regions, nodes-in-region, wires-scoped-to-region, node-region, node-binder, port-order per node, port-to-wire map per node, wire-scope, and wire endpoints with positional port keys.

---

## Refinement: signatures, monotonicity, and termination

After initial coloring, `refine` iterates `refineOnce` until the number of color classes stops growing.

`refineOnce` builds a new signature for each object that combines its old color (the color from before this refinement round) with the colors of its neighbors, then calls `rankSignatures` to produce fresh integer colors.

**Region signature:** `R|{cur}|p:{parentColor}|c:{sortedChildColors}|n:{sortedNodeColors}|w:{sortedWireColors}`. Parent color is `-` for the root sheet. Child, node, and wire color lists are sorted numerically before inclusion, so the signature is invariant under the order in which those lists were constructed.

**Node signature:** `N|{cur}|r:{regionColor}|b:{binderColor}|{portKey}={wireColor},…`. Binder color is `-` for term nodes. Port entries are listed in the node's canonical port order (as stored by `buildIndex`): `["out", "v0", "v1", …]` for term nodes and `["a0", "a1", …]` for atom nodes. Port order is not sorted — it encodes the specific argument positions of atom nodes and the first-occurrence order of free variables in term nodes. Both are semantically significant.

**Wire signature:** `W|{cur}|s:{scopeColor}|e:{sortedEndpointStrings}`. Each endpoint string is `{nodeColor}.{portKey}`. The endpoint list is sorted lexicographically, making the signature invariant under the order in which endpoints were added to the wire.

**Why refinement is split-only and terminates:** Every signature string is prefixed by the object's old color. If two objects had equal colors in round `k` they had identical signatures in round `k-1` and therefore the same old color going into this round; if the neighborhood colors now differ, their new signatures differ and they get different new colors — a split. If they had different colors in round `k` their signatures include different prefixes, so they get different new colors — the split is preserved. No two objects with distinct colors can merge. Formally: for any round, the partition induced by new colors is a refinement of the partition induced by old colors. The number of classes is therefore monotone non-decreasing and bounded above by the number of objects, so the loop terminates.

---

## Individualization: branch rule and correctness of the minimum

When refinement stabilizes but the partition is not discrete — some color class still has more than one member — the diagram has genuine automorphic symmetry that refinement cannot break.

`firstTiedClass` in `canonical.ts` finds the first such class: it inspects all three sort maps for colors assigned to more than one object, picks the smallest tied color value (colors are globally ranked across sorts), and returns the sort and sorted member list for that class.

`individualize` clones the color state and sets one chosen member's color to `classCount(c)` — a value strictly larger than any existing color, so it is strictly fresher than all current classes. After individualization, `refine` is called again on the result; the individualized member is now unique and its new signatures propagate through the neighborhood, typically resolving additional ties.

`search` iterates over every member of the first tied class, individualizes each one in turn, re-refines, and recurses. At each leaf (a discrete partition), `serializeWith` produces a deterministic string. `search` keeps the lexicographically smallest string across all branches.

**Why this is an isomorphism invariant:** any automorphism maps the first tied class onto itself (it is defined by colors, which are isomorphism-invariant). For every element `m` in the class and every automorphism `φ`, individualizing `m` and then individualizing `φ(m)` produce isomorphic colored diagrams — so their subtree minima are identical. The minimum over all branches is therefore the same regardless of which isomorphic copy of the diagram we start from.

No member of the first tied class is skipped. This is what makes the form exact rather than heuristic: a heuristic break-tie rule might explore only one candidate, producing a canonical form that happens to work on most diagrams but fails on carefully constructed symmetric ones. Here every candidate is explored.

---

## Discrete-partition precondition of serialization

`serializeWith` is only ever called from `search` after `firstTiedClass` returns `null`, meaning every color class is a singleton. Under this precondition:

`ordinalize` sorts each sort's id list by ascending color; because every color is unique, this produces a total order with no ties, and the resulting ordinal map is a well-defined bijection `id → {0, 1, …, n-1}`.

`sortByOrd` uses that ordinal map as the sort key, producing the sorted traversal order.

The serialized lines are:
- One line per region: `r{ord}:{kindKey}:p={parentOrdStr}` where parent is `-` for the root or `r{parentOrd}` otherwise.
- One line per node: `n{ord}:{contentKey}:r=r{regionOrd}` optionally followed by `:b=r{binderOrd}` for atom nodes.
- One line per wire: `w{ord}:{pinPrefix}s=r{scopeOrd}:e={sortedEndpointStrings}` where pin prefix is `pins[i,…]:` for boundary-pinned wires and empty otherwise, and endpoint strings are `n{nodeOrd}.{portKey}` sorted lexicographically.

All five uses of `regionOrd.get(...)` — a region's own ordinal, a region's parent, a node's region, an atom's binder, and a wire's scope — are guarded with explicit error throws (`DiagramError`) rather than `!` non-null assertions, because those are the internal consistency properties we want to verify loudly rather than silently corrupt.

---

## Boundary pinning

`canonicalForm` accepts an optional `pinnedWires: readonly WireId[]`. The list is an ordered list of boundary incidences, not a set: every id must exist, and repeated ids mean those positions expose the same line of identity.

`buildIndex` accumulates every incidence index in `pinOf: WireId → number[]`. `initialColors` uses the full vector, so `[w,w,u]`, `[w,u,w]`, and `[w,u,u]` are distinct interfaces even when the underlying diagram is unchanged. Boundary order and the alias relation are therefore both canonical content.

This ensures boundary order is significant: two diagrams with the same wiring but different boundary orderings get different canonical forms. With an empty boundary the canonical form equals `diagramFingerprint`, intentionally — a 0-ary relation is a sentence.

---

## Complexity

The individualization-refinement algorithm has **exponential worst-case complexity** in the number of objects. The branching factor at each tied class is the class size; worst-case depth is the number of tied classes; in the most adversarial case (completely symmetric diagrams) this explores a number of leaves exponential in the number of objects.

The algorithm is **exact always**: it never makes heuristic choices. This is the no-heuristics trade. A heuristic canonical labeler would be fast but could return false positives (diagrams that are non-isomorphic but happen to receive the same form). Proof diagrams are small and mostly asymmetric; refinement alone resolves almost all cases without any branching.

---

## Storage note

`diagramFingerprint` in `fingerprint.ts` returns `canonicalForm(d)` — the full canonical string. This string is the comparison key for isomorphism. Do not compare hashes for soundness-relevant equality. If profiling shows fingerprint length is a storage concern, hash at the storage layer and keep the full canonical string as the in-memory comparison key; that way a hash collision is caught immediately on comparison and cannot silently produce an unsound proof.
