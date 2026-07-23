# Drawn Definitions Design (supersedes the body-node mechanism)

**Date:** 2026-07-23
**Status:** Approved direction (design B, no-carrier), pending implementation.
Amends `2026-07-22-signature-indexed-wires-design.md` (whose Bodies section,
rule-set items 2–3, and sealed-node rendering law are superseded in place).
Full derivation record: `docs/roughs/definition-mechanism/` (requirements,
prior-art survey, four committed developments, fork analysis).

## Outcome

There is no definition object. No body node, no sealed content, no carrier
of any kind. A relational definition is ordinary drawn structure — the
constraint K(R,G) = ∀x⃗(R(x⃗) ↔ G(x⃗)) in cuts, atoms, and wires — and
every manipulation of definitions is an existing rule applied to that
structure, plus exactly two new rule families, both sig-generalizations of
existing ι rules. The kernel shrinks; the Lean core mutual inductive gains
nothing (`Item.relBody` is never born).

## Corrected foundations (replacing the mistyped "Bodies" law)

The superseded spec said "bodies attach to wires and pin them … at ι a
λ-term body" — a type error: there is no cross-sort pinning role. The
correct law is **functional determinacy**:

> A content node applies its content-relation to its port wires by
> presence. Its ports are the relation's coordinates. Fresh spawn is free
> exactly when the content determines one coordinate as a total function
> of the others — by β-totality at ι (the λ-node: y = t(x⃗); every term
> denotes), by comprehension at relational sorts (∃R.R ≐ G; every drawing
> denotes a relation).

Corollaries: wires are the only argument currency; a drawing becomes
applicable by reifying it to a wire (comprehension intro — always free);
there is no ι-sorted head anywhere (at ι the determined coordinate is the
output port); relations live on wires, nodes assert by presence; equality
is primitive only at ι (the λ-node IS an equation) and *derived* above ι —
every cost of this design traces to that deliberate foundational choice,
and the alternative (primitive higher-sort ≐, drawn as the "scroll") is
preserved as a reversible future option in
`docs/roughs/definition-mechanism/design-scroll.md`. Migration asymmetry
decided the fork: everything built here survives under a later scroll;
the reverse path wastes a Lean core constructor.

## The mechanism

**K(R,G)** for a wire R : rel(σ⃗): an outer cut holding the ∀x⃗ wires
(sorts σ⃗ — the definition's argument coordinates, always drawn), two
implication cut-pairs containing atoms of R and two copies of the content
G. Parameters are not a mechanism: atoms inside G sit directly on outer
wires; the mkDiagram scope invariant is the entire gate. A wire is *bare*
(pure quantifier), *constrained* (some K in scope), or *tautological*
(its only endpoints are its own K's two R-atoms — the state asserting
exactly ∃R.R ≐ G ≡ ⊤).

**Rules:**
1. **comprehensionIntro(scope, sig, G, params)** — fresh wire + freshly
   drawn K, ANY polarity (the comprehension axiom; replaces bodied vacuous
   one-for-one, orientation-uniformity transferring verbatim).
   **comprehensionElim(wire)** — inverse, in the tautological state;
   K-shape check = cut-skeleton walk + `exploreForm` equality of the two
   G copies.
2. **Relational congruence join** — rule 9's exact shape at relational
   sigs: two constrained wires whose contents match under a boundary
   correspondence (certificate = boundary-pinned canonical form) merge
   polarity-free; the redundant K then deiterates on the same certificate.
   This is the α-level of definitional equality, free via existing
   machinery.
3. Everything else is existing rules: constraint attach = **insertion**
   (its gate IS the old bodyAttach gate); detach = **erasure**; content
   transport = **iteration** of K along the wire (content is never redrawn
   and never teleported); occurrence swaps R(a⃗) ⇄ G(a⃗) are derived
   iterate–join–deiterate–DC sequences; universal instantiation with an
   existing relation = plain **wire join**; βη-level definitional
   rewriting = the ordinary calculus operating inside K, complete for
   derivable equivalences because K's two content copies sit at opposite
   parities (each direction of a directional proof applies at the copy
   where it is sound — both forward moves).

**The library layer (where all convenience lives — never the kernel):**
- Named definitions: assertion form = the existing ref/defId store
  (named nodes render as their own nodes, unchanged law). Each named
  definition auto-generates (macro) its **singleton companion**: a K whose
  content is a single ref atom (the existing `foldedComprehension` shape)
  — so the two-copy cost of K is O(1) refs per definition, never 2×|G|;
  heavy content lives once, in the store, composed by reference.
- **Eq_σ⃗** := the ambient higher-order definition ∀PQ(… P x⃗ ↔ Q x⃗ …) of
  sort rel(rel σ⃗, rel σ⃗), introduced once per signature in use; the swap
  lemma ∀R∀S∀x⃗(Eq(R,S) ∧ R(x⃗) → S(x⃗)) (and its symmetric twin) proven
  once from it. Thereafter every occurrence swap is ONE theorem citation
  — the amortization mechanism, replacing both the dead monolithic rules
  and any would-be kernel convenience rule. Depth-2 quantification
  earning its keep on the system's own machinery.

**Acceptance case (∃P.P, three moves):** comprehensionIntro(sheet, rel(),
G = blank) → double-cut elim on the ⊤→P half (the atom pops out asserted)
→ erase the spent half. The proof is the comprehension axiom plus one
double cut, which is what ∃P.P's truth consists of.

## Kernel inventory

**Dies:** the `body` node kind everywhere (diagram.ts, matcher, canonical,
json); `body.ts` (attach/detach — replaced by nothing; their gates were
insertion/erasure's); `fold.ts` (both flavors — fold/unfold survive as
derived sequences and cited lemmas); the bodied branch of `vacuous.ts`;
the planned Lean `Item.relBody`. **New:** `comprehension.ts`
(intro/elim); relational congruence join (rule-9 family extension).
**Survives, now central:** wire-join, iteration, insertion/erasure,
congruence at ι, the matcher/`exploreForm`/occurrence certificates (one
evidence format certifying K-shape, join discharge, and citations).

## Rendering and interaction

K is host-diagram content rendered by the ordinary pipeline — the
superseded "bodies render as sealed nodes / content never inlined" law is
void. Named (assertion-form) nodes keep their own-node rendering.
**Open user rulings:** (1) a view-level collapse affordance for
recognized K shapes (pure display; expands to real structure); (2)
K-shape drift diagnostics (drift is sound but derecognizes the
definition; the carrier made it impossible, here it must be visible).
Gestures are the primitives-only set: spawn (cascade), join drag,
iterate/deiterate, insertion/erasure, citation — nothing
comprehension-specific exists at any layer.

## Obligations and open items

- Verify the citation path at negative-parity occurrences (symmetric swap
  lemma; the citation machinery's polarity handling) before relying on it
  in the interaction design.
- Lean (Plan 2): one new soundness obligation (comprehension intro/elim
  over ordinary structure — the same budget line the superseded spec
  carried for bodied vacuous) plus the rule-9-template proof for
  relational congruence join; `Item.relBody` and its flagged difficulty
  are deleted from the plan.
- Implementation sequencing: deletion/refactor begins only after the
  in-flight junction-physics work lands (shared worktree, suite gates).
- The e2e and interaction-layer rebuilds (fix-list items) now target this
  design.
