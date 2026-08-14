# Refinement-driven isomorphism and occurrence matching

Status: approved design (session ruling 2026-08-13); implementation follows
via the standard plan workflow.

This replaces the kernel's two exhaustive search engines — canonical-form
labeling in `src/kernel/diagram/canonical/explore.ts` and the occurrence
matcher in `src/kernel/diagram/subgraph/match.ts` — with color refinement
that does all the work on every diagram anyone actually draws, keeping
enumeration only where it is mathematically forced.

## 1. The ruling this design rests on

Color refinement alone is not a complete isomorphism test for this data
model, and this is provable inside the kernel's own validity rules.
Counterexample: six arity-2 identity nodes joined pairwise by six wires
into one ring of six (asserts w₁=…=w₆) versus two rings of three (asserts
w₁=w₂=w₃ and w₄=w₅=w₆). Same censuses; refinement stabilizes with one node
class and one wire class in both; the class-quotient wiring is identical;
the diagrams are not isomorphic and are semantically different sentences.
A hub-connected variant defeats any connected-components patch. In
general, arbitrary graphs embed into this diagram class (vertices →
identity nodes, edges → 2-end wires), so a branch-free complete test would
be a polynomial-time general graph-isomorphism algorithm.

User ruling: accepted. Such gadgets are semantically degenerate (a cluster
of identity nodes means the same as one identity node) and will not appear
unless drawn adversarially, but the kernel must still judge them
correctly. Therefore: **refinement decides everything whenever its stable
classes are genuine automorphism orbits — which is every practical
diagram — and a candidate-enumeration backstop remains in the code for the
adversarial residue.** The backstop's dormancy on orbit-clean diagrams is
tested (instrumented, not asserted).

Second ruling: definition argument order stays canonical. The one
surviving consumer of canonical *labeling* (as opposed to iso testing) is
`canonicalArgOrder` in `src/app/define.ts`, which gives a newly defined
relation an id-invariant argument order so isomorphic selections produce
identical definitions. It keeps a trimmed lex-min labeling, running once
per definition on a small extracted body.

## 2. Shared refinement engine — `canonical/refine.ts`

One module owns index building, initial content colors, and refinement
rounds; both the iso test and the retained labeling consume it. It
generalizes the current private machinery of `explore.ts` to run over the
disjoint union of one or two diagrams. Colors are computed from content
only — region kind, node kind/signature/arity/defId, wire signature, pin
positions, and neighbor colors (positional ports keyed, identity
incidences / wire endpoints / sibling regions as sorted multisets) — never
from which side of the union an element is on, so color classes span both
diagrams. Refinement iterates to a stable partition exactly as
`refineOnce`/`refine` do today.

Individualization is a primitive of the engine: give one element a fresh
color and re-refine. The engine also exposes the class census (per color:
members on each side).

## 3. Pairwise isomorphism — `canonical/iso.ts`

Public API (names final at implementation time, semantics fixed here):

- `diagramIso(a, b, aPins?, bPins?): DiagramIso | null` — replaces
  `exploreIso`. Pins are the ordered boundary wire lists; pin positions
  enter the initial colors as they do today, so boundary order is
  respected, including repeated positions.
- `sameDiagram(a, b, aPins?, bPins?): boolean` — the equality form used by
  every call site that today compares `exploreForm` strings; implemented
  as `diagramIso(...) !== null`.

Algorithm:

1. Refine A and B jointly.
2. Any color class whose two sides have unequal member counts → not
   isomorphic, immediately.
3. If every class has exactly one member per side, read the bijection off
   the colors and **verify it structurally in linear time**: every region's
   kind and parent, every node's kind/content/region, every wire's
   signature, endpoint multiset, and pin positions must transport
   correctly. The returned mapping is always verified, so a false
   "isomorphic" is impossible even if refinement had a bug; only "not
   isomorphic" answers rest on refinement keys being iso-invariant (they
   are: built from content only).
4. Otherwise take the smallest tied class, fix its least A-member (any
   fixed choice is complete, because the image of that member under any
   isomorphism must lie in the matched class), and try each B-member of
   the class in turn: individualize both to one fresh shared color,
   re-refine, recurse. First success returns its mapping; all candidates
   failing → not isomorphic.

On orbit classes the first B-candidate always succeeds, so no backtracking
occurs on practical diagrams; the candidate loop is the dormant
completeness backstop for §1's gadgets, where branching is unavoidable. No
fuel parameter: kernel equality checks must be decisive (matching today's
`exploreForm`, which is also unbounded).

Instrumentation: a production-neutral counter of failed individualization
candidates (in the spirit of the existing `__benchCounter`), so tests can
assert dormancy.

## 4. Call-site conversions and deletions

`exploreForm`, `boundaryForm`, `exploreLabeling`, and `exploreIso` leave
the public kernel surface (`kernel/diagram/index.ts`).

Both-diagrams-in-hand sites become pairwise calls:

- `kernel/proof/theorem.ts` (citation equality, twice) → `sameDiagram`
  with the respective boundaries.
- `kernel/rules/fold.ts` (extracted vs expected body, pinned) →
  `sameDiagram`.
- `app/session.ts` (forward vs backward side) → `sameDiagram`.
- `app/replay.ts` (meet equality, then `exploreIso`) → one `diagramIso`
  call: null means the meets differ; non-null is the mapping.
- `kernel/rules/iteration.ts` (form filter then `exploreIso`) → one
  `diagramIso` per probe.
- `kernel/proof/compose.ts` (`exploreIso` twice) → `diagramIso`.
- `kernel/proof/compile-content.ts` (first-occurrence form vs each
  candidate; planned-vs-actual `exploreIso`) → pairwise calls.

Fingerprint-style sites hold the diagram value instead of a canonical
string and compare pairwise at the comparison point:

- `app/copy-planner.ts` `resultFingerprint` — carries the result diagram
  (or whatever its consumer actually compares; confirmed during
  planning).
- `app/shell.ts` `editForm` test hook — exposes the edit sheet's
  structure for the "defining a relation leaves the sheet untouched" e2e;
  replaced by a comparison the e2e can perform pairwise (e.g. a retained
  diagram snapshot compared with `sameDiagram`, or strict JSON equality if
  untouched means identical storage; confirmed during planning).
- `theories/reification.ts` `selectedChildForm` — same treatment against
  its consumer.

Diagnostics that printed canonical forms on mismatch (e.g.
`theorem.ts`'s debug output) print a plain id-ordered structural dump
instead; the two dumps are explanatory, not comparable-by-eye canonical
forms, which is acceptable for an error path.

## 5. Retained labeling for definitions

`explore.ts` shrinks to the lex-min individualization search built on the
§2 engine, exporting only what `canonicalArgOrder` needs: a discrete
canonical wire ordering of a closed pattern diagram. The search keeps its
current semantics (explore every member of a tied class, keep the
lexicographically least serialization — the completeness argument in the
current header comment stands). Cold path, small inputs; no orbit pruning
is added. Not exported from the kernel index; `define.ts` imports it
directly.

## 6. Occurrence matching — `subgraph/match.ts` rewritten

Public contract unchanged: `findOccurrences(host, pattern, {explorationFuel,
inRegion, attachments})` returns all distinct occurrence footprints as
certificate-checked `Occurrence` values with `status`
`'complete' | 'exhausted'` and a step count. Callers stay untouched except
for fuel budget review (§7).

Engine: constraint propagation over refinement colors, then
most-constrained-first search.

- Host is refined once (unseeded; colors are invariants of the host).
- Every pattern element (region, node, wire) gets a candidate set of host
  elements, initialized by local content: node kind/sig/arity/defId, wire
  signature, region kind; regions additionally by `inRegion`, boundary
  wires additionally by seeded `attachments`.
- Propagation to a fixpoint, one constraint at a time, honoring the
  fragment asymmetry exactly as the current matcher's checks define it:
  - nested pattern cuts are **exact**: equal censuses of children, nodes,
    and scoped wires (today's `matchSubtree` gate), so a host cut whose
    subtree census disagrees leaves the candidate set;
  - the top container is **at least**: pattern root children/nodes embed
    injectively, extra host siblings allowed;
  - internal wires are **exact**: endpoint multiset and derived scope must
    transport (today's `wireCompatible`, non-boundary branch);
  - boundary wires are **sub-multiset**: pattern endpoints embed into the
    host wire's endpoints, host scope an ancestor-or-equal of the mapped
    root (today's boundary branch);
  - positional ports (atom head/args, ref args) force their wire images
    and vice versa; identity incidences and wire endpoint multisets
    constrain as multisets.
- Search assigns the pattern element with the smallest candidate set
  first, re-propagating per branch; a branch dies at its first emptied
  candidate set. Enumeration here is the *output* — returning all
  occurrences means visiting each — but rigid patterns reach every
  occurrence with zero dead branches. Certificate checking at record time
  (`checkOccurrenceCertificate`) and footprint dedupe (for symmetric
  patterns whose distinct assignments share an image) both stay.
- Fuel: one candidate placement per step, same as today's `spend`
  granularity in spirit; `'exhausted'` when it runs out.

## 7. Fuel budget review

Step counts change scale (propagation kills branches that today burn
thousands of steps), so the three explicit budgets are rechecked during
implementation: `app/interact/cite.ts` (caller-supplied fuel),
`app/define.ts` `inferFoldArgs` (64), `kernel/rules/iteration.ts` (its
budget at the `findOccurrences` call). Budgets must be justified against
the new step definition — no inherited magic numbers.

## 8. Testing

- **Soundness regression (born from §1):** the ring pair — one six-ring
  vs two three-rings of arity-2 identities — must be judged not
  isomorphic; likewise the hub-connected variant. These are permanent
  kernel tests.
- **Dormancy:** orbit-clean symmetric diagrams (e.g. an identity node
  with several interchangeable wires; nested symmetric cuts) assert zero
  failed individualization candidates via the §3 counter.
- **Witness correctness:** shuffled-id property tests — generate a
  diagram, permute all ids, assert `diagramIso` finds a mapping and the
  linear verifier accepts it; with pinned boundaries, assert pin-order
  sensitivity (permuted pins on asymmetric boundaries must fail).
- **Matcher:** the existing `findOccurrences` tests encode the contract
  and must pass unchanged. Add: a rigid-chain instance whose step count is
  asserted against an exactly derived bound (the objective form of "no
  blind permutation"), and a symmetric-pattern instance asserting the
  footprint set is exactly the distinct-image set.
- **End to end:** the frege replays; full suite and `tsc` green before
  each commit (per repo policy, the physics suite is not used as
  verification).

## 9. Explicitly out of scope

- Orbit pruning / automorphism discovery in the retained lex-min labeling
  (cold path, small inputs).
- Collapsing automorphism-equivalent matcher branches before footprint
  dedupe (bounded by real symmetry sizes; revisit only with evidence).
- Any change to definition-argument-order semantics or authoring UX.
