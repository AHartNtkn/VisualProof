# Primitive wire-quantifier rules

Replace the two monolithic relation sever/join rules in the TypeScript kernel
with nine paired primitive rules, each acting uniformly on all ends of one
wire. Everything the monolithic rules can do compiles to a sequence of these
primitives, so the kernel loses its most complex rule and the interactions
built to feed it. The Lean formalization keeps the monolithic rule and gains a
theorem that it is redundant: its compiled primitive sequence produces the same
result.

## Why

The monolithic rules pack an entire substitution or abstraction into one move.
Join requires the user (or script) to supply a whole content diagram up front;
sever requires designating every occurrence of a pattern, with ordered formal
selection. Those input shapes forced the order-sensitive, multi-stage
interactions that made the quantifier moves finicky, and they make the kernel
checker's largest and most intricate code path (occurrence matching, overlap
checks, boundary signature checks).

Decomposing substitution into per-connective steps is the move Gödel and
Bernays made in NBG class theory: replace the comprehension schema (one axiom
per formula) with finitely many class-formation operations that generate it.
The same decomposition works here, and the repo already contains one piece of
it: iota sever/join, a single-wire split/merge primitive. One other piece has
been built once before: the bubble-era comprehension rules gained a
`diagonalize` helper (plan 16, 2026-07-03) that let one wire serve several
argument positions — the same operation as the argument-duplicate primitive
below — but that code was deleted with the rest of the bubble comprehension
machinery in the signature-indexed-wires redesign, so it is precedent, not
current code.

## Vocabulary used below

- **Dying wire**: the wire being instantiated (join) or created (sever).
- **Site**: one applied end of the dying wire; site *i* sits in region *rᵢ*
  with argument wires *x̄ᵢ*. "Applied" means the endpoint is an application
  node, not an attachment of the wire as someone else's argument.
- **Content**: the open diagram substituted for the wire, with ordered formals
  *f₁..fₙ* and fixed ambient parameter wires.
- **Live wire / residual**: during compilation, a wire with one end per site,
  owing a sub-content (its residual) still to be expanded.

## The primitive inventory

Every primitive transforms **all** ends of one wire in a single step. That
uniformity is what makes each step sound: adding or changing ends one at a
time would let different ends implicitly pick different witnesses for the same
bound relation.

| # | Primitive pair | Effect on each end W(x̄) | Class |
|---|---|---|---|
| 1 | merge / end-partition sever | ends of two wires become one wire / one wire's end set partitions into two wires (this is today's iota sever/join with the iota-only signature restriction removed) | gated |
| 2 | delete-all-ends / spawn-ends | end vanishes / ends appear at chosen sites | gated |
| 3 | cut-wrap / cut-absorb | becomes ¬W′(x̄), a cut holding one end of a fresh wire | equivalence |
| 4 | parallel split / parallel fuse | becomes W′(x̄) beside W″(x̄), fresh wires; fuse requires pairwise co-located ends with identical arguments | equivalence |
| 5 | arity-shift / arity-unshift | becomes W′(x̄, yᵢ) where yᵢ is a fresh wire **scoped at that end's region rᵢ** | equivalence |
| 6 | argument permute; argument duplicate / contract | argument positions reorder; one position becomes two attached to the same wire per end | equivalence |
| 7 | argument drop / extend | a position disappears (its per-site wires lose an end) / a position appears attached to a chosen visible wire per site | gated |
| 8 | apply-formal / abstract-formal | becomes xₖ(ȳ): the end's own k-th argument wire is applied to the rest | gated |
| 9 | identity leaf / identity abstract | becomes an identity node over the arguments | gated |

Shared side conditions, stated once: all endpoints of the acted-on wire must
be applied (primitive 1 is the exception — merge tolerates any endpoint kind,
and merge is also the only way a wire occurring in argument position gets
instantiated, exactly as with the monolith's `nonAppliedEndpoint` refusal);
fresh wires are co-scoped with the old wire, except arity-shift's per-site
wires, which are scoped at each end's current region; every rule takes the
orientation boolean, and gates follow the existing scheme
(`joinRequiresNegative` / `severRequiresPositive`, flipped by orientation).

Vacuous intro/elim (spawn or discard an endpoint-free wire of any signature,
ungated) already exists and is the tenth member of the family.

## Soundness: one lemma covers all nine

Each primitive replaces site contents Tᵢ(W) by Tᵢ′(W̄′) uniformly. If a
definable witness F makes Tᵢ(F(W̄′)) equal Tᵢ′(W̄′) pointwise at every site,
then the surrounding diagram is unchanged as a function of the sites —
pointwise equality composes through any context, so mixed site polarities are
irrelevant — and the step old→new is sound exactly when the wire's scope has
negative polarity (forward). If a witness G exists in the other direction too,
the step is an ungated equivalence. Gates are therefore not designed; they
fall out of which witnesses exist:

| Primitive | F (eliminating W) | G (introducing W) |
|---|---|---|
| delete-all-ends | W := ⊤ | — |
| cut-wrap | λx̄.¬W′x̄ | λx̄.¬Wx̄ |
| parallel split | W′ ∧ W″ | W′ := W″ := W |
| arity-shift | λx̄.∃y.W′(x̄,y) | λx̄y.W(x̄) |
| permute / duplicate | composition with the permutation / λ(x,ȳ).W′(x,x,ȳ) | inverse composition |
| drop | λ(x̄,z).W′(x̄) | — (the dropped per-site wire is arbitrary) |
| merge into V | W := V | — |
| apply-formal | λ(z,ȳ).z(ȳ) | — |
| identity leaf | W := (=σ) | — |

Two model-side obligations, both already met: arity-shift's G needs every sort
nonempty, which `PreModel.inhabited` (Model.lean:57) assumes and which ungated
vacuous elim already relies on; apply-formal's F needs the application
relation to exist as a value, which holds in the full models the semantics
uses.

## Completeness: compiling the monolithic rules

Join compiles by induction on the residual's size (nodes + wires + regions,
then remaining argument plumbing). Case on the live wire's residual ψ:

1. **ψ has an internal wire w scoped at ψ's root** (any signature, including
   relational — `Sig` is recursive): arity-shift. The per-site wire yᵢ lands
   at whatever region the live end currently occupies, so a quantifier under a
   cut in the content is spawned inside the per-site cut and reads locally as
   universal. Quantifier alternation costs nothing. The shifted wire becomes
   an ordinary formal, so its later uses need no special handling.
2. **Root has two or more items and no root-scoped internal wire**: parallel
   split, both halves keeping all formals. Running case 1 first is what
   handles shared quantifiers such as ∃y.(A(y) ∧ B(y)).
3. **Root is a single cut**: cut-wrap; the residual becomes the cut interior.
4. **Empty residual**: delete-all-ends, then vacuous elim.
5. **Leaf (a single node)**: fix the argument plumbing (permute, duplicate,
   drop; a parameter argument arrives by extend choosing that parameter at
   every site), then: end of a fixed wire — parameter, ambient wire, or atom,
   which is a signature-wire end — merges into it; end of a formal (content
   that applies one of its own arguments) is apply-formal, irreducibly its own
   primitive because the target wire differs per site; identity nodes use the
   identity leaf. Ref nodes need no primitive: recurse into the stored
   definition body, then `fold` each site (fold is already an equivalence).

Every case strictly shrinks the measure, and the cases cover every content
constructor. The terminal state equals the monolithic join's output up to
fresh naming and identity normalization — the same quotient splice already
owns.

Sever is not argued separately. Every primitive is one of an inverse pair with
dual gates, and a legal monolithic sever instance is the exact inverse of a
legal join instance (its occurrence data — content match, shared parameters,
formal designations — is what makes it so). The reversed sequence with
reversed orientation compiles it, landing on `severRequiresPositive` gates.
The one reverse-direction side condition worth stating: arity-unshift requires
the dropped position to attach, at every site, to a wire scoped at that site's
region whose endpoints that occurrence exhausts — mechanically checkable, no
matching.

Worked example, φ(x) = ∃y.(P(x,y) ∧ ¬Q(y)) into unary R: arity-shift (yᵢ at
each site's region) → parallel split → left half merges into signature wire P
→ right half cut-wraps → drop formal 1 → merge into Q. Each site ends as
∃yᵢ.(P(xᵢ,yᵢ) ∧ ¬Q(yᵢ)).

## TypeScript kernel changes

- Remove the iota-only signature restriction from iota sever/join; the gates
  and scope checks stay as they are. This is primitive 1.
- Delete the `relation` variants of `WireSeverInput`/`WireJoinInput`,
  `ContentOccurrence`, and the occurrence-matching half of
  `wire-quantifier.ts`.
- Add the new primitive rules with the side conditions above. Update
  `step.ts`, `json.ts`, `compose.ts`, and the error vocabulary accordingly.

## The compiler

One pure function — (dying wire, content, formals, parameters) → list of
primitive steps — implements the induction above; the sever direction is the
same function run in reverse orientation from occurrence data. It lives beside
the proof-composition layer, never inside `rules/`: the kernel checks only
primitive steps and never sees the monolithic input shape.

## Migration

Two artifact classes use the monolithic rules today, and both migrate through
the compiler:

- 34 relation-kind sever/join constructions across 13 files in
  `src/theories/` swap to compiler calls that splice primitive steps into the
  script.
- `examples/frege.json` contains 79 serialized relation-kind steps; a one-time
  conversion pass expands each through the compiler and re-serializes.

All replay tests (frege, arithmetic) staying green is the acceptance test for
the compiler.

## Lean strategy

The monolithic rule and the in-flight relation-content-join soundness plan
stay; that plan should land first, because its singleton-erasure and insertion
receipts are the ingredients the primitive proofs reuse. Then: one soundness
theorem per primitive (each an instance of the witness lemma above), and a
redundancy theorem stating that the compiled primitive sequence replays to the
monolithic rule's output modulo identity normalization and fresh naming.
Monolithic soundness and primitive-set completeness become corollaries of the
same statement.

## Interaction layer

The interactions that existed only to feed the monolithic rules — occurrence
designation, ordered-formals highlighting, and the sever/join commit gestures
consuming them — are deleted with no one-for-one successors.

The replacement property is checkable from the kernel signatures alone: every
primitive's input is a single wire, a specific port, an oriented drag between
two specific objects, or an unordered set of ends. Nothing takes an ordered
tuple, so no interaction anywhere can depend on the order in which things were
highlighted. Argument correspondence in merge and fuse is positional by
signature; reordering is its own local gesture (drag one port past another).
Standing interaction laws are unchanged: no menus for proof actions, no editor
intent encoded as diagram or proof content, matcher validates only at commit.
Gesture details (which drag means merge versus fuse; how arity-shift picks the
new position's signature) are a separate design session.

Iteration, deiteration, erasure, and deletion interactions are untouched.

## Testing

- Per-primitive kernel unit tests, including extending the polarity-matrix
  suite to all nine pairs.
- Compiler round-trip tests: on the existing fixtures, the compiled sequence's
  final diagram equals the old monolithic output.
- Replay suites (frege, arithmetic) green after migration; error-vocabulary
  tests updated.

## Out of scope

- Decomposing erasure/insertion in the kernel (the same pattern applies and
  the user-facing gestures would not change; separate project).
- Decomposing iteration/deiteration.
- Any one-gesture "instantiate with content" convenience built on the
  compiler.
- Gesture design for the new primitives.
