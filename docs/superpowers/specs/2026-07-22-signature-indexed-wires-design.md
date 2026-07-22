# Signature-Indexed Wires Design

**Date:** 2026-07-22
**Status:** Approved design, not implemented

## Outcome

Replace second-order quantifier bubbles with a single unified wire concept
indexed by a recursive signature. Every wire — term line of identity or
quantified relation of any order — is `{ scope, sig, endpoints }`, obeying one
scope law, one polarity law, one body mechanism, and one fold/unfold rule. The
bubble region kind, atom `binder` fields, binder colors, quantifier ordering,
the monolithic comprehension rules, and the proxy/host binder-spine dependency
machinery are all deleted. The system becomes a classical higher-order logic
over untyped λ-terms; the current second-order system is its depth-≤1 fragment.

This spec supersedes `docs/superpowers/plans/2026-07-22-relation-wire-so-quantifiers.md`
(deleted), which specced the two-sort variant without the decomposed rule set
or the signature index.

## Motivation

The bubble representation carries three redundancies, each a source of
complexity with no semantic content:

1. **Order.** Overlapping same-scope quantifiers must nest, forcing an
   arbitrary order. ∃R∃S φ and ∃S∃R φ are semantically identical but are
   distinct diagrams with distinct canonical forms; theorem citation across the
   difference fails without a reorder rule (none exists).
2. **Names.** Binder identity is a region id rendered as a hue drawn from an
   unbounded namespace — colors-as-names, with the attendant matching
   machinery: exact binder-identity checks, open-binder pure-chain conditions,
   stub-bubble chain reconstruction in extraction.
3. **Placement.** A bubble is a spatial region, so material inside ∃R's bubble
   not mentioning R is representationally distinct from the same material
   outside, though ∃R(φ ∧ ψ) ≡ (∃R φ) ∧ ψ when R ∉ ψ.

All three are exactly the redundancies the first-order representation already
avoids: a line of identity has no name, no order against its siblings, and no
region of its own — only a scope. The kernel already agrees on the key
invariant: `cutDepth` ignores bubbles in both TS and Lean, so quantifier
polarity is *already* derived from cut position, not from the bubble.

The bubble encoding also forced the comprehension rules to be monolithic
(instantiate = choose witness + rewrite every occurrence + dissolve region,
atomically) and forced the outer-dependency feature (`e3d8714`) into
proxy-bubble/host-bubble pairing with binder-spine validation and prefix
repair — ~1.8k lines that exist only because binding is regional.

Finally, the library plan (`docs/roughs/library.md`) repeatedly hits the
second-order ceiling: predicate transformers are irrevocably schematic, the
μν engine carries per-instance monotonicity obligations, containers are
introduced explicitly as an escape hatch, and Tier C (functors between
definable categories, cohesion modalities) is macro-only. Concrete wanted
objects — e.g. the function-type constructor `Arrow(A, B, f) := ∀x. A(x) → B(f x)`
of signature `((ι),(ι),ι)` — are macro-encoded because depth-2 signatures are
unrepresentable. The signature index removes that ceiling.

## Core representation

**Signatures.**

```
Sig ::= ι | rel(Sig, …, Sig)     -- argument list may be empty
```

Terms remain untyped λ; only wires stratify. `ι` is the base sort. Today's
arity-n bubble becomes sort `rel(ι,…,ι)` (n copies). `rel()` is a
propositional wire. Signatures are finite and well-founded, so a wire of sort
σ can never plug into an argument port of sort σ nested within itself:
self-application (`R(R)`) remains syntactically absent, not side-condition
forbidden — the same stratification-by-construction consistency argument as
the current second-order system, generalized.

**Wires.** One concept:

```
Wire = { scope: RegionId, sig: Sig, endpoints: Endpoint[] }
```

Regions are `sheet` and `cut` only — the `bubble` kind is deleted. A wire of
sort `ι` is today's line of identity, unchanged. A wire of relational sort IS
the quantifier: ∃ at even cut-parity of its scope, ∀ at odd — the identical
polarity law across all signatures. No names, no order among same-scope
quantifiers, no quantifier regions.

**Atoms.** The atom node generalizes: a head port accepting a wire of sort
`rel(σ₁…σₙ)` and argument ports 1…n where port i accepts a wire of sort σᵢ.
The `binder: RegionId` field is deleted; the relation is designated by the
head-port wire connection. Arity and argument sorts derive from the head
wire's sig. Depth-1 atoms are today's atoms; depth-2 atoms are
`Arrow(A,B,f)`-style, where some argument wires are themselves relational.
Plugging one wire into several argument ports is ordinary splicing (this
subsumes `diagonalize` as a rule). Terminology: these are *atoms*
throughout — "application node" is banned as it collides with λ-term
application, which is untouched by this design.

**Bodies.** Bodies attach to wires and pin them, gated by polarity, uniformly:

- At `ι`: a λ-term body (`x = t`) — the existing equation machinery, unchanged.
- At `rel(σ₁…σₙ)`: a comprehension body — a subgraph with a
  signature-declared boundary (n stubs of sorts σ₁…σₙ, plus parameter
  attachments to outer wires of any sort).

A body's boundary may attach to any wire whose scope is at-or-outside the
target wire's scope. That single gate is the impredicative comprehension
schema at every signature, and it replaces the separate SO dependency gate:
same-region parameters are admitted, justified by same-polarity quantifier
commutation (∃x∃R ≡ ∃R∃x).

**Named refs.** `ref` nodes are unchanged in kind and extend to higher
signatures (a named def may have sort `((ι),(ι),ι)` etc.). Named definitions
remain only ever their own nodes.

## Semantic justification

The wire representation is the quotient of the bubble representation by three
sound equivalences: same-polarity quantifier commutation, scope
extrusion/retraction over non-occurring material, and renaming. Nothing
finer is collapsed: quantifier position relative to cuts (the semantically
meaningful part) is exactly the scope field.

Semantics interprets signatures recursively over the term domain D:

```
⟦ι⟧        = D
⟦rel σ⃗⟧   = (Π i, ⟦σᵢ⟧) → Prop
```

Full (standard) semantics, as the Lean development already uses at second
order. Comprehension at any signature may quantify over any signatures
(fully impredicative); consistent under the full model. Truth-track strength
rises from full second-order to full higher-order arithmetic over the λ-term
base. Every signature's domain is nonempty (λ-terms at `ι`; the empty
relation otherwise), which grounds vacuous intro/elim at both polarities.

## Rule set

Five signature-blind primitive move families; the cut-based structural rules
are untouched.

1. **Vacuous wire intro/elim.** A wire with no endpoints may be created or
   deleted at any scope, any signature, either polarity. Subsumes vacuous
   bubble moves.
2. **Body attach/detach.** Polarity-gated exactly as the existing equation
   gates at `ι`; the same gates govern comprehension bodies at relational
   sorts. Attaching a body is the actual quantifier instantiation — the
   analogue of pinning an `ι` wire with a term node.
3. **Fold/unfold at one occurrence.** An atom whose head wire carries a body
   may be replaced by a copy of the body with argument wires spliced onto the
   boundary stubs, and inversely. This is the *existing* named-relation
   fold/unfold move (plan 11e) generalized from `ref` nodes to atoms on
   bodied wires. It is definitional rewriting — never called β; β/η are
   reserved strictly for the term language, which this rule never touches.
4. **Wire join.** Two same-signature wires merge; scope = deepest common
   ancestor; gated like the existing congruence join. At relational sorts
   this asserts extensional equality. Leibniz equality at every signature is
   derivable, not primitive.
5. **Structural rules** (iteration/deiteration, insertion/erasure, double
   cut): unchanged and now genuinely binding-blind.

Derived (macro) forms of the old rules — the old test cases replay against
these to prove no power is lost:

- `comprehensionInstantiate` = attach body → unfold each occurrence → delete
  vacuous wire.
- `comprehensionAbstract` = the inverse composite.
- `diagonalize` = shared-wire splicing; not a rule at all.

Gained flexibility: instantiation no longer has to be all-or-nothing — a
quantifier's wire may persist, carrying its definition, with some occurrences
folded. An atom on a bodied wire behaves as a local anonymous named
definition.

## Well-formedness

- Signature equality at every port: head port sig = wire sig; argument port i
  accepts exactly σᵢ.
- Scope encloses every endpoint's node (existing wire law, all sorts).
- Ports partition exactly across wires (existing law).
- Body boundary attachments scoped at-or-outside the bodied wire's scope.
- Deleted invariants: `AtomBindersAreBubbles`, `AtomBindersEnclose`, all
  bubble-region checks.

## Lean architecture

**One binder context.** `Region.mk` currently introduces `localWires : Nat`
while SO binding is a separate `Item.bubble` pushing onto `RelCtx`. New core:
a region introduces `locals : List Sig` — one de Bruijn discipline for all
binding. The mutual inductive loses `Item.bubble`; `Item.atom` changes payload
(head reference of sort `rel σ⃗`, argument references of sorts σᵢ, replacing
`RelVar`); new `Item.relBody` mirrors `Item.equation` at relational sorts.
`RelCtx`/`RelVar` and `BinderContext` reconstruction are deleted.

**Semantics.** Environments are sig-indexed; the region clause is a single
`∃ env` over `locals`; the bubble clause disappears into it; the atom clause
evaluates the head environment value at the argument values.

**Soundness.** The wire-transport apparatus (`WireProvenance`,
`InterfaceTransport`, boundary transport) generalizes from Nat-indexed to
Sig-indexed — one apparatus for what were two binding systems. The 45k-line
`Soundness/Comprehension/` development (120 files) is replaced, not ported:
each of the five primitives follows the proof shape of its existing
`ι`-counterpart (equation intro/elim, congruence/fold-unfold via the Named*
modules, join, vacuous). Soundness of the old monolithic rules is inherited
by macro composition, not re-proven.

**Concrete side.** `CRegion` loses `bubble`; `CWire` gains `sig`;
`CNode.atom` gains a head port and loses `binder`; `checkWellFormed` swaps
binder invariants for sig-equality checks; elaboration builds sig contexts
by ordinary wire-context accumulation.

**Known fiddly point** (flagged, accepted): `Item.relBody`'s payload nests a
boundary-ed region inside an item — structurally similar to cuts nesting
regions, but the boundary indexing is new and is expected to be the hardest
part of the Lean core rewrite. It is the one-time price of
comprehension-as-equation.

## Rendering

Channels carry one thing each; every channel is uniform along the entire wire
(readable at any point, any length, any zoom — no per-length encodings):

1. **Color = order.** A short ordered ladder: terms one color, order-1
   relations a second, order-2 a third, etc. Canonical (no choices, no
   hashing, no renaming); in practice ≤4 rungs. This replaces
   colors-as-names with colors-as-sort, which is a canonical function of
   structure.
2. **Finer signature structure is read locally at atoms**: arity from port
   count (existing pips), argument sorts from the colors of the plugged-in
   wires. Order + arity + per-port appearance determines every practical
   signature without a lookup table.
3. **Rejected encodings**: signature-hash hues (collisions, false
   unrelatedness, unreadable arbitrariness), tick/depth marks (require
   countable clean arc length; fail on short stubs and crossings), semantic
   thickness (relative judgment, no absolute reading). **Held in reserve**:
   multi-stranding (k parallel strands for order k) as a monochrome/
   accessibility backup — not built now.
4. **Bodies render as single sealed nodes on the wire** — exactly as λ-term
   bodies are nodes at `ι` and named defs are only ever their own nodes.
   Internal diagrams are authored/inspected in the existing relation
   workspace; body content is never inlined into the host diagram; no
   bubble-like enclosure returns.
5. **Scope law transfers verbatim**: a wire's outermost extent reaches into
   its scope region; loose ends are their own homed bodies. Relational wires
   join the wire-physics system as additional wire species.

## Migration

Clean break, no compatibility layers:

- Diagram/proof JSON schemas change: no `bubble` regions, no `binder`
  fields, wires gain `sig`, atom head ports added, step payloads for the two
  SO rules replaced by the primitive-move payloads.
- Saved proofs and theory macros are re-authored against the new
  representation; existing theorems are re-derived in the new system (this
  doubles as the acceptance test).
- Deleted outright: the monolithic comprehension rule implementations, the
  proxy/host binder-spine machinery (`comprehension-dependencies.ts` and its
  Lean/spec counterparts), bubble rendering, binder-hue plumbing, open-binder
  chain matching, stub-bubble extraction.

## Testing and verification

- Each of the five primitives lands with its TS tests and its Lean soundness
  theorem before the next primitive starts.
- The old monolithic rules' test cases are replayed as macro composites to
  demonstrate conservativity over the old system.
- Integration gate: the Frege-arithmetic spike results (ℕ encoding,
  induction derivation) re-proven end-to-end in the new system.
- Higher-signature coverage from day one: `Arrow` at `((ι),(ι),ι)` and a
  transformer at `((ι),ι)` (Knaster–Tarski μ as a single internal theorem)
  as the depth-2 acceptance examples.

## Change inventory (from codebase survey, 2026-07-22)

**TS kernel** — `src/kernel/diagram/diagram.ts` (core types),
`regions.ts`, `boundary.ts`, `spawn.ts`, `builder.ts`, `diagram/json.ts`,
`canonical/explore.ts`, `subgraph/{match,extract,splice,occurrence-certificate}.ts`,
`rules/{comprehension,vacuous,doublecut}.ts`, `proof/json.ts`.
**Interaction/app** — `interaction/comprehension-dependencies.ts` (deleted),
`interaction/named-relation.ts`, `theories/macros.ts`, `app/edit.ts`,
`app/actions.ts`, `app/proof-front.ts`, `app/interact/{moves,spawn,proof-spawn}.ts`,
`app/relation-workspace*.ts`, `app/relation-transactions.ts`.
**View** — `view/{paint,engine,bend,constraints,relax}.ts`.
**Lean** — `Diagram/Core.lean`, `Diagram/Semantics.lean`,
`Theory/Signature.lean`, `Diagram/Concrete/{Core,WellFormed,Semantics}.lean`,
`Diagram/Concrete/Elaboration/`, `Rule/Step.lean`, `Rule/Comprehension*`
(replaced), `Rule/Soundness/` (Comprehension/ replaced; bubble cases removed
throughout), `Correspondence/StepTags.lean`, `Proof/`.
**Tests** — parallel suites throughout.

## Effort assessment

- **TS**: days of sessions; net-simplifying (proxy spines, open-binder
  chains, stub-bubble extraction, binder-hue plumbing all delete).
- **Lean**: the dominant cost — the core mutual inductive is the root of a
  ~248k-line development, so every proof file is touched at least
  mechanically (one fewer constructor), and the SO soundness development is
  replaced wholesale. Multiple weeks of sessions, mitigated by the five
  primitives having existing `ι` proof templates.
- **Rendering**: modest (color ladder, body nodes, wire species
  generalization).
- The signature index costs little over a hardcoded two-sort version (`Nat` →
  recursive `Sig` at the root) and avoids a second rewrite if higher orders
  are ever needed — which the library plan shows they are.
