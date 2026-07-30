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
| 1 | merge / end-partition sever | ends of two wires become one wire / one wire's end set partitions into two wires (today's iota sever/join with the iota-only signature restriction removed, and with a fresh-wire-scope parameter: the split-off wire may be scoped at any region enclosing all its endpoints, gated by that region's polarity — see "Identity substitution derived") | gated |
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
fresh wires are co-scoped with the old wire, except sever's split-off wire
(scope chosen, see the table) and arity-shift's per-site wires, which are
scoped at each end's current region; every rule takes the orientation
boolean, and gates follow the existing scheme (`joinRequiresNegative` /
`severRequiresPositive`, flipped by orientation).

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

## Identity substitution derived (folded in per 2026-07-29/30 rulings)

Substitution — the fifth identity transformation — is implemented today as an
`IdentityRetarget` array riding iteration and deiteration steps (Rule 5 of the
2026-07-25 identity-node design). No interaction constructs that evidence:
both app call sites hard-code `retargets: []` (`copy-planner.ts:156`,
`moves.ts:76`), so equality substitution is unreachable from the UI. A
standalone move-one-endpoint rule was considered and **rejected** — the
system had endpoint-moving rules once (λ-era `fusion`/`congruenceJoin`) and
removed them deliberately. Instead, substitution becomes **derived** from the
severing machinery this project already builds:

- **The derivation.** Given id(a, b) at region r and an endpoint P(a) at q
  inside r: (1) iterate the identity node into q — plain iteration, no
  retargeting; (2) sever wire a, partitioning the P-endpoint and the copied
  node's a-port onto a fresh wire scoped at q. The state at q is
  ∃a′(a′ = b ∧ P(a′)), which the one-point rule collapses to P(b)
  eagerly. Two user steps; normalization does the landing.
- **Sever gains a fresh-wire-scope parameter** (an amendment to primitive 1):
  the split-off wire may be scoped at any region enclosing all the moved
  endpoints, gated by that region's polarity. Today's same-scope sever is the
  special case choosing the old scope.
- **Normalization Rule 2 extends** from "all attached wires co-scoped with
  the node" to "all but exactly one": an identity node whose attached wires
  are all scoped at its region except a single outer wire collapses by the
  one-point rule ∃x@R(x = t ∧ Φx) ≡ Φt — an equivalence at any polarity,
  which is already the soundness citation Rule 2 carries. Two or more outer
  wires still decline, exactly as before.
- **Why derived beats primitive here:** the standalone rule needed a bespoke
  side condition (never retarget the justifying node's own port, else a
  false id(a,b) becomes a true id(b,b)). In the derivation that shape is
  unreachable except through the sever step, whose polarity gate blocks it
  in precisely the contexts where it would be unsound. The constraint is
  structural, not bolted on.
- **Rule 5 of the identity-node design is superseded**: iteration and
  deiteration lose the `retargets` field and copy exactly; the serialized
  step schema drops the field; `IdentityRetargetSemantics.lean` support is
  retired with it. Retargeted steps in the theory scripts
  (`arithmetic-comm-carrier.ts`) migrate to iterate + sever pairs and their
  reverses.
- **No new gestures.** Step 1 is the existing drag-copy; step 2 is the
  existing Family-1 sever stroke (touch the endpoint and the copied node's
  port, drop inside the target region). Identity therefore adds expressivity
  with no interaction surface beyond the insertion row above.

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

**Insertion redundancy (2026-07-30, corrected same day).** Monolithic
insertion — splice an arbitrary well-formed graph into a negative region —
is stepwise derivable from the primitives: introduce a vacuous nullary
relation wire at the region (ungated), spawn its application there
(negative-gated), and ground the wire to the graph as content through the
compiled join, whose gate sits at the wire's scope. Insertion is
comprehension-grounding of a vacuous proposition — the exact hypothesis-
handle pattern every theory script already uses. The Lean obligation is
therefore a corollary of the join redundancy theorem plus the soundness of
the two auxiliary steps; the same derivation shows ref-spawn plus unfold is
conservative (definitions stay macros). The negative-splice soundness lemma
is still independently required: it grounds the backward erasure gate (one
rule, two readings, per the flipped-polarity law). One further small
derivability lemma (2026-07-30): every per-site argument-extend (the
kernel form, attachments chosen per end) equals a uniform extend followed
by per-site sever and join at the new position — the witness ignores the
position, so the choices are free. This licenses the gesture layer's
uniform-only surface and would license narrowing the kernel input to the
uniform form if ever wanted. An earlier version of
this note claimed opposite-parity content is forward-underivable and
proposed an admissibility-style theorem; that analysis covered only the
spawn-and-cut fragment and omitted the join family — retracted.

## Interaction layer

### Deletions

The interactions that existed only to feed the monolithic rules are deleted
with no one-for-one successors: the ordered-highlight occurrence-designation
model (this supersedes "Interaction: designating an occurrence" in the
2026-07-25 redesign spec, which is retired with the rules it served), the
pending-relation contact flow's occurrence semantics, and the sever/join
commit gestures in `connection.ts`/`moves.ts`.

The replacement property is checkable from the kernel signatures alone: every
primitive's input is a single wire, a specific port, an oriented drag between
two specific objects, or an unordered set of contacts. Nothing takes an
ordered tuple, so no interaction anywhere can depend on the order in which
things were highlighted.

### Principles

- **One-site demonstration.** Every primitive acts uniformly on all ends of a
  wire, so the user demonstrates the change at one end; the kernel applies it
  everywhere, the overlay previews all ends transforming during the drag, and
  a failed gate refuses by spring-back at commit, under the existing
  forward/backward orientation toggle.
- **Object-typed gestures.** What a gesture means is fixed by which objects it
  touches — wire strand, end node, argument port, cut boundary, blank region —
  never by selection order or menus.
- **Contact sets.** Gestures that need several sites accumulate contacts as
  transient editor state (the existing pending-contact machinery) and commit
  one atomic step; contacts are sets.

### Family 1 — the drawing gesture (comprehension direction)

Draw a stroke from blank space, touch contacts, drop the loose end; the drop
region is where the created thing lives (loose-end law). The contact type
selects the rule:

| Contacts | Rule |
|---|---|
| blank spots in regions | spawn-ends (0-ary; n-ary ends are then built by plumbing gestures, so nothing is unreachable) |
| ends of one wire | end-partition sever |
| applied ends of different wires | abstract-formal (the same-head case derives via sever + extend) |
| identity nodes | identity abstract |
| strands of existing wires (≥2) | identity insertion: the stroke materializes as an identity node at the drop region with one port per contacted wire. The drop point selects the region independently of where the wires are rendered (a two-anchor drag cannot; this is why insertion is not a Family 2 row). The committed step orders the wires canonically, never by contact order, so equal contact sets always produce the same diagram. When the drop region is the wires' common scope the kernel's existing collapse yields the shared-wire form. Replaces the `i` key and the menu row. |
| nothing | opens the spawn list (vacuous intro moved to Q/Shift+Q, 2026-07-30; the arity prompt this row once cited is struck) |

In every row but identity insertion the stroke becomes a wire; the drawn
wire's signature is determined by the rule except for spawn-ends/vacuous
intro, which reuse the existing arity prompt.

### Family 2 — object-typed drags (instantiation direction)

| Grab → drop | Rule |
|---|---|
| wire strand → another wire's strand | merge |
| end node → co-located parallel end | parallel fuse |
| end node → blank beside itself (tear) | parallel split |
| end node's rim → blank (pull out a dangling stub) | arity-shift (arity prompt for the new position's signature) |
| argument port → off the node | remove position: arity-unshift when its side condition holds, else argument-drop — identical result diagram, only the gate differs, so preferring the ungated rule is deterministic |
| argument port → past a sibling port | permute |
| argument port → sibling port on the same wire | contract |
| argument port → beside itself | duplicate |
| argument port → its own end's center | apply-formal |
| end node → one of its own argument ports | identity leaf |
| wire strand → an end of another wire | extend (uniform parameter; struck 2026-07-30: a one-commit per-site gesture re-bundles local acts — the new position is born semantically inert, and each site's attachment is an ordinary local join afterward) |
| lasso around one end | cut-wrap |
| cut boundary → the end it encloses | cut-absorb |
| Delete on a wire | delete-all-ends; on an endpoint-free wire, vacuous elim |

Worked example — instantiating R with ∃y.(P(x,y) ∧ ¬Q(y)) is six drags: pull a
stub out of one R-end, tear the end, connection-drag the left half onto P,
lasso the right half's end, rip off its first port, connection-drag onto Q.

### Keyboard and palette conformance fixes (folded in per 2026-07-29 ruling)

The current implementation violates the approved 2026-07-10 proof-interaction
design in ways this project fixes because it is already rebuilding this layer:

- **W with an empty selection spawns an empty double cut at the region under
  the pointer** (today it refuses "select something first"); W with a
  selection wraps it, unchanged. The Delete precedence (double-cut elim →
  vacuous elim → erasure → deiterate) is unchanged. (A Shift+W arity-prompt
  binding was wrongly listed here as surviving doctrine; it belonged to the
  replaced second-order bubble calculus and is not part of this design.)
- **Menu rows duplicating agreed dedicated interactions are removed**: erase,
  doubleCutWrap, doubleCutElim, vacuousElim, deiterate, identityInsert, and
  iterate (menu-triggered iteration was explicitly removed by the 2026-07-10
  design and regressed).
- **Q with the pointer over a region spawns a bare quantifier wire there**
  (an individual existential; 2026-07-30 ruling: a floating existential is
  meaningful content — its presence changes the statement, if only
  trivially, unlike identity collapse — so it gets a direct move).
- **Shift+Q spawns a floating proposition quantifier** (a bare nullary
  relation wire; 2026-07-30 ruling). This closes the signature-birth gap
  inductively: ι comes from Q, rel([]) from Shift+Q, and every other
  signature follows by applying the handle (spawn list), rim-pulling new
  first-order positions, and extension-dragging wires of already-built
  signatures — argExtend takes the dragged wire's signature, so nesting
  recurses. Distinct from the struck Shift+W: no arity prompt, no sig
  stipulation — the two fixed births plus context-driven growth.
- **The palette trigger becomes an explicit still right-click** (today it
  opens on a plain click over a hit). The only remaining rows are relFold
  and citeTheorem (relUnfold's row is deleted — double-click is its
  gesture). These two are name-driven: choosing a stored definition or
  theorem is inherently a picker, which the diagram cannot determine, so
  the rows are the correct interface rather than debt (2026-07-30 ruling;
  an earlier revision called their retirement "recorded debt" — struck).

Drag-to-iterate, highlight+Delete erasure, and deiteration gestures are
untouched.

## Testing

- Per-primitive kernel unit tests, including extending the polarity-matrix
  suite to all nine pairs.
- Compiler round-trip tests: on the existing fixtures, the compiled sequence's
  final diagram equals the old monolithic output.
- Replay suites (frege, arithmetic) green after migration; error-vocabulary
  tests updated.
- One browser test per gesture row in both families (commit and spring-back
  refusal), plus the keyboard fixes: W on an empty selection spawns the double
  cut at the hovered region; the palette opens only on a still right-click;
  the removed menu rows are absent.
- Identity substitution: unit tests for the Rule 2 extension (one outer wire
  collapses, two or more decline) and the sever scope parameter (gate follows
  the chosen region's polarity); the two-step derivation produces P(b) from
  P(a) under an enclosing identity, in both orientations; replay equality for
  the migrated retargeted theory steps; the flow end to end in the browser.
- Identity insertion via the drawing gesture: the uniqueness shape (equality
  asserted inside a cut the wires do not enter), n-ary contact sets, and the
  pin that permuted contact orders commit structurally identical diagrams.

## Out of scope

- Decomposing erasure/insertion in the kernel (the same pattern applies and
  the user-facing gestures would not change; separate project).
- Decomposing iteration/deiteration.
- Any one-gesture "instantiate with content" convenience built on the
  compiler.
- Retiring the residual palette (relUnfold, relFold, citeTheorem) — recorded
  debt against the standing menu ban.
