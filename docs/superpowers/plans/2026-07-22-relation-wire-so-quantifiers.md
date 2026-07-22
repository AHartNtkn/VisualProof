# Relation Wires: Second-Order Quantifiers as Scoped Wires

**Status:** Design spec. Records the changes the refactor requires. NOT scheduled for implementation in the session that produced it; no code changes accompany it.

**Goal:** Replace the current representation of second-order quantifiers — `bubble` regions plus `atom` nodes carrying a `binder` region reference — with a second sort of wire ("relation wire"), so that an SO relation variable is represented exactly the way a first-order individual variable already is: one wire = one line of identity, carrying a `scope` and (for relations) an `arity`. This eliminates two forms of redundancy the bubble representation forces: (1) an arbitrary linear order among same-scope quantifier bubbles, and (2) an unbounded supply of distinct bubble identities/colors used purely as names.

**Tech stack:** TypeScript kernel (`src/kernel/**`), app/view layers (`src/app/**`, `src/view/**`, `src/interaction/**`, `src/theories/**`), Lean 4 formalization (`VisualProof/**`).

---

## 1. Motivation and the soundness linchpin

First-order variables are already nameless and orderless: a term wire *is* the variable, its identity is wire-identity, and its quantifier is read off its `scope` region's polarity. Second-order variables are the lone exception — they are `bubble` regions with `atom` occurrences pointing back via a `binder` field. That exception is what forces the redundancy:

- **Ordering.** Two bubbles at the same scope carry an implicit order (which region is "first"). But same-scope quantifiers have the same cut-depth, hence the same polarity, hence the same quantifier type, and same-type quantifiers commute. The order encodes nothing.
- **Names.** Distinguishing occurrences of different SO variables at the same scope requires distinct bubble identities (rendered as colors) — conceptually an infinite name set, exactly the thing the "port names are not semantic" law rejects for FO.

**The linchpin that makes the collapse sound.** `src/kernel/diagram/regions.ts:41-58`: `cutDepth` counts only `cut` regions, and `polarity` is `cutDepth % 2`. Bubbles are explicitly polarity-transparent ("Bubbles are quantifiers, not negations: they never affect parity, spec §2.1"). There is no ∀/∃ annotation anywhere on a bubble (`Region` for a bubble carries only `parent` and `arity`). Therefore an SO quantifier's type is *already* determined purely by cut-nesting, identically to a term wire. There is no annotation to preserve.

Consequently a bubble does exactly two jobs — declare an arity, and mark a position in the region tree — and both are precisely what a scoped wire does for FO. The refactor is a faithful re-encoding, not a change of logic:

- All cross-type quantifier ordering (the non-commuting ∃R∀x dependencies) is carried by the intervening `cut` regions, which this refactor never touches.
- Widening/narrowing a relation variable's scope over material that does not mention it is the valid equivalence `∃R.(ψ ∧ χ(R)) ≡ ψ ∧ ∃R.χ(R)` for R-free ψ. Because bubbles are polarity-transparent, moving a variable's scope from a bubble to that bubble's parent changes no cut-depth and no quantifier type.

## 2. Representation change

### 2.1 Regions (`src/kernel/diagram/diagram.ts`)

```
// before
export type Region =
  | { kind: 'sheet' }
  | { kind: 'cut'; parent: RegionId }
  | { kind: 'bubble'; parent: RegionId; arity: number }

// after
export type Region =
  | { kind: 'sheet' }
  | { kind: 'cut'; parent: RegionId }
```

The `bubble` constructor is deleted. Regions become purely the negation/scope tree.

### 2.2 Wires (`src/kernel/diagram/diagram.ts`)

Two sorts, disjoint by which ports they attach to:

```
// term wire: one first-order individual (unchanged meaning)
{ kind: 'term'; scope: RegionId; endpoints: Endpoint[] }        // output/freeVar/arg ports

// relation wire: one second-order relation variable
{ kind: 'relation'; scope: RegionId; arity: number; endpoints: Endpoint[] }   // head ports only
```

The `arity` lives on the relation wire, next to `scope` — the wire *is* the variable, so the arity is the variable's arity. (Term wires need no arity.) The existing single-shape `Wire` record gains a `kind` discriminant; `mkDiagram`'s wire map holds both sorts.

### 2.3 Occurrence node (today's `atom`) (`src/kernel/diagram/diagram.ts`)

```
// before
{ kind: 'atom'; region: RegionId; binder: RegionId }           // ports: arg 0..k-1, k from binder bubble

// after
{ kind: 'atom'; region: RegionId }                             // ports: head, arg 0..k-1
```

The occurrence node gets *simpler*:

- **`binder` is dropped.** A node's variable identity is now the relation wire its `head` port hangs on, not a stored region reference.
- **Arity leaves the node.** It is no longer read from a binder bubble; it is the `arity` of the relation wire the node's `head` port attaches to.
- **One new port kind, `head`.** Because binding is now a wire connection and this kernel is entirely port-based (every port attached to exactly one wire — `mkDiagram` partition check), the occurrence node needs a port for its relation wire to claim. `requiredPorts` for an atom becomes `[ { kind: 'head' }, arg 0, …, arg k-1 ]` with `k` derived from the attached relation wire.

`Port` gains `{ kind: 'head' }`; `portKey` maps it (e.g. `'head'`).

### 2.4 Constructor validation (`mkDiagram`)

- The `bubble` arity check and the `atom.binder` "binder is a bubble enclosing the atom" check are removed.
- New relation-wire checks, mirroring the existing term-wire checks: scope region exists; scope is an ancestor-or-equal of every endpoint node's region; every endpoint is a `head` port of an `atom`; all endpoint atoms have the wire's `arity` (their arg-port count is *derived from* the wire, so this is automatic once port derivation reads the wire).
- **Port-derivation ordering.** Today `requiredPorts` for an atom reads arity from the binder bubble (a region — available before wires are examined). Under the new model an atom's arg-port count is read from its relation wire. `mkDiagram` must therefore resolve relation-wire membership (which head port belongs to which relation wire, and that wire's arity) *before* computing each atom's required port set. This is a validation-ordering change, still fully context-free (the relation wire is in the same diagram).
- **Sort disjointness.** `head` ports attach only to relation wires; `output`/`freeVar`/`arg` ports attach only to term wires. Enforced in the partition pass.

## 3. Semantics contract

A **relation wire** `W = { scope: S, arity: k, endpoints: [head(n₁), …, head(n_m)] }` denotes a second-order quantifier binding a fresh `k`-ary relation variable `R`:

- **Quantifier type** = `polarity(S)` (positive ⇒ ∃R, negative ⇒ ∀R), exactly as for a term wire.
- **Occurrences** are exactly `n₁ … n_m`. Occurrence `n_j` asserts `R(a_{j,1}, …, a_{j,k})`, where `a_{j,i}` is the individual denoted by the term wire on `n_j`'s `arg i` port.
- **Scope** `S` must enclose (ancestor-or-equal) the region of every `n_j`.
- `m = 0` (no occurrences) is a vacuous quantifier: `∃R.φ ≡ φ` — see §7.1.

This is term-for-term parallel to the existing term-wire denotation (scope S, endpoints = ports of individual occurrences, quantifier type = `polarity(S)`), with "individual" replaced by "k-ary relation" and "argument/output/freeVar port occurrence" replaced by "head-port occurrence carrying k argument lines."

## 4. Well-formedness invariants (net)

1. Every `atom` has exactly one `head` port, attached to exactly one relation wire (falls out of the partition check once `head` is a required port).
2. A relation wire's `arity` equals the `arg`-port count of every atom it binds (automatic: atom arg-count is derived from the wire).
3. A relation wire's `scope` encloses every atom it binds (mirror of the term-wire scope check).
4. Sorts are disjoint: relation wires ↔ `head` ports; term wires ↔ `output`/`freeVar`/`arg` ports.
5. Region tree contains only `sheet` and `cut`.

## 5. Kernel rule inventory

### 5.1 `rules/comprehension.ts` (417 lines) — the heart; net simplification

- **`applyComprehensionInstantiate`.** Occurrences are found *directly* as the relation wire's endpoints, replacing the `atom.binder === bubbleId` scan (`:178-181`). The polarity gate tests `polarity(d, W.scope)` instead of `polarity(d, bubbleId)`. Arity comes from `W.arity`. **The entire bubble-dissolve block (`:194-211`) is deleted** — there is no region to dissolve and nothing to promote; after splicing at each occurrence you delete the relation wire and its occurrence nodes. The per-occurrence splice (`spliceSubgraphMapped` at each atom's region, arg wires + parameter attachments) is retained, sourced from wire endpoints.
- **`applyComprehensionAbstract`.** Creates a fresh relation wire (`scope = wrap.region`, `arity = comp.boundary.length`) and, for each occurrence, a fresh occurrence node whose `head` port lands on that wire and whose `arg i` port lands on the occurrence's argument-i wire. **The "wrap selection in a fresh bubble region" reparenting (`:374-394`) is deleted** — the relation wire need only enclose its occurrences via `scope`; selected content is not moved.
- **`validateBinderSpine` / open comprehension (`:24-98`, `binders` param).** This is the one non-trivial fork; see §7.2.
- **`diagonalize` (`:227-278`).** Operates on term-wire boundary merging; unaffected by the sort change. Retained.
- **`reparent` helper (`:104-110`).** The `atom` case loses `binder`: `{ kind: 'atom', region }`.

### 5.2 `rules/vacuous.ts` (87 lines) — deleted

Every line is bubble-as-region plumbing: `applyVacuousBubbleIntro` mints a bubble region and reparents a selection under it; `applyVacuousBubbleElim` dissolves an atom-free bubble region and promotes its contents. Neither has an analog when the SO variable is a wire. A vacuous SO quantifier is a contentless relation wire (§7.1), which needs no rule to create or destroy. The file is removed, not ported.

### 5.3 `rules/spawn.ts` — `spawnBoundRelationNode` re-pointed

The bound-relation spawn (`:57-70`) currently requires `binder` to be a bubble enclosing the spawn region and checks `bubble.arity`. It becomes: attach the spawned occurrence node's `head` port to the designated relation wire; require that wire's `scope` to enclose the spawn region; check the wire's `arity`. `requireSpawnPolarity` and the `ref`/named-relation spawn paths are unaffected.

### 5.4 `rules/doublecut.ts` — bubble branches drop out

The `reparent` `atom` case loses `binder` (`:15`). The region-copy loops currently special-case reparenting `bubble` regions (`:40`, `:82`); those branches vanish once regions are only `sheet | cut`. The elimination error message that names `bubble` (`:64`) simplifies. Net simplification.

### 5.5 `rules/reldef.ts` — `binderStubs` meaning shifts

Uses `extractSubgraph`'s `binderStubs` guard (`:71-72`). Under the wire model this becomes "atoms whose relation wire is scoped outside the selection" — i.e. relation-typed boundary stubs (§6.1). The `ref` arity handling is unaffected.

### 5.6 `rules/congruence.ts` — comments only

Logic references bubbles only in prose ("Bubbles may intervene — they are quantifiers"). Since relation wires create no regions, nothing "intervenes"; the walk over scope/region is unaffected. Comment update; verify no logic touches region kind.

### 5.7 `rules/headstrip.ts` — NOT AFFECTED (false positive)

`headstrip.ts`'s `binder`/`binders` (`:91`, `sa.binders`) is the **λ-term binder count** from `headSpine`, unrelated to SO binding. Do not touch. Recorded here so it is not swept into a mechanical rename.

## 6. Diagram-machinery inventory (`src/kernel/diagram/**`)

This is where the representation is threaded most deeply; changes here are structural, not cosmetic.

### 6.1 `subgraph/extract.ts` (~23 sites) and `subgraph/splice.ts` (~25 sites)

Extraction currently emits `binderStubs` for atoms whose `binder` bubble lies outside the extracted region. Under the wire model an atom whose relation wire crosses the selection boundary yields a **relation-typed boundary stub**, the SO analog of the existing term-wire attachment stubs. Splice must accept relation-typed boundary wires (with arity) alongside term-typed ones, and the comprehension `binderMap` threading (open binders) routes through here (§7.2). This is the largest machinery change.

### 6.2 `subgraph/match.ts` (~20 sites) and `subgraph/occurrence-certificate.ts` (~20 sites)

Matching/occurrence certification must treat relation wires and occurrence nodes as first-class, and must stop treating bubbles as region walls (there are none). Occurrence certificates gain a relation-wire dimension.

### 6.3 `canonical/explore.ts` (~19 sites) — where the win concretely lands

Canonicalization is what erases the arbitrary bubble ordering/naming today. Under the refactor, relation wires are canonicalized exactly like term wires (by structural position, not identity), so the bubble-ordering and bubble-identity canonicalization is *removed* and replaced by the (already existing) wire-canonicalization discipline. The `exploreForm` boundary-pinned fingerprint used by comprehension abstraction (`comprehension.ts:363-364`) must fold relation-wire boundaries into the same fingerprint.

### 6.4 `builder.ts`, `json.ts`, `spawn.ts`, `boundary.ts`

Construction helpers and (de)serialization: drop the `bubble` region kind and `atom.binder`; add relation wires (with `kind` + `arity`), the `head` port, and occurrence nodes. `boundary.ts`'s `DiagramWithBoundary` gains relation-typed boundary entries.

## 7. Open design decisions

### 7.1 Contentless relation wires (recommended: permit, inert)

The existing kernel already permits 0- and 1-endpoint *term* wires (`intro.ts:44` mints a singleton output wire for `∃x(x=t)`; `mkDiagram` imposes no minimum-endpoint count). By parallelism, permit 0-endpoint relation wires: a relation variable with no occurrences denotes `∃R.⊤` conjoined in — harmless, inert, unsound of nothing. This is what makes `vacuous.ts` unnecessary rather than merely relocated: "vacuous SO quantifier" is a contentless wire, and adding/removing one is (at most) generic inert-wire hygiene, not a bespoke bubble-region rule. **Decision to confirm:** whether any generic "erase inert wire" cleanup is wanted at all, or whether contentless wires simply never arise from construction/rules and need no handling.

### 7.2 Open comprehension / the binder spine (recommended: fold into relation-typed attachments; MUST verify)

`validateBinderSpine` (`comprehension.ts:24-98`) exists because, in the bubble world, a comprehension body `G` that references outer SO variables represents those references as **nested proxy bubble regions** at the pattern root, matched positionally to host bubbles that enclose the instantiation site. In the wire world, an SO variable is a wire, not a nested region — so an open SO reference in `G` is naturally a **relation-typed boundary stub**, handled by the same mechanism as the existing (term-typed) parameter `attachments`. The recommended resolution: the separate binder-spine structure collapses into relation-typed boundary attachments, and `validateBinderSpine`'s "ordered single-child root-prefix of nested bubbles" apparatus is deleted.

**This is the one place the refactor is not obviously mechanical.** Before treating it as settled, the implementation-design pass must verify that every property the binder spine currently enforces (arity agreement per binder; target properly encloses the instantiated variable; the exact outer-to-inner nesting/positional matching; no stray node/wire content on spine containers) is either (a) reproduced by relation-typed attachment validation, or (b) genuinely unnecessary once outer SO references are wires. Do not delete `validateBinderSpine` until each of its guards is accounted for.

## 8. App / interaction / view inventory

Construction and rendering move from "make/draw a bubble enclosure" to "make/draw a relation wire." Affected (per grep for `bubble`/`binder`/`atom`):

- **Construction / editing:** `app/relation-workspace.ts`, `relation-workspace-draft.ts`, `relation-transactions.ts`, `define.ts`, `edit.ts`, `actions.ts`, `tactics.ts`, `copy-planner.ts`, `abstraction-matches.ts`, `hittest.ts`, `proof-front.ts`; `interact/construct.ts`, `interact/moves.ts`, `interact/spawn.ts`, `interact/proof-spawn.ts`; `interaction/comprehension-dependencies.ts`, `interaction/named-relation.ts`.
- **Rendering / physics:** `view/paint.ts`, `engine.ts`, `tromp.ts`, `relax.ts`, `bend.ts`, `index.ts`. A relation wire is a hyperedge touching many occurrence nodes at their `head` port; the layout/physics engine must route and draw it as a second wire color (per "wires are physical objects" / "two colors" intent), rather than drawing a bubble boundary. Mechanical but real; consistent with the existing wire-physics model.
- **Theories:** `theories/frege.ts`, `theories/macros.ts` build SO structure and must emit relation wires + occurrence nodes.

## 9. Lean inventory (`VisualProof/**`) — dominant cost, accepted

Scale: ~244k lines; **215 of 362 files mention `bubble`, 271 mention `binder`**; `Rule/` ≈ 169k lines, `Diagram/` ≈ 70k. `bubble` is a constructor of the central `Region`/`Diagram` inductive on which the soundness development is built, so this is not a rename:

- Redefine the `Region`/`Diagram` inductive (drop `bubble`; restructure the atom node to drop its binder and gain a `head` port; add the relation-wire sort with arity).
- Re-establish well-formedness, semantics (`Diagram/Semantics.lean`, `Rule/Comprehension/Semantics.lean`), and every rule-soundness proof that goes through comprehension/instantiation/abstraction, spawn (bound relation), double-cut, and the structural rules (`Rule/Soundness/**`).
- Rework the subgraph/splice/extract/match concrete machinery (`Diagram/Concrete/Subgraph/**`) for relation-typed boundaries.
- Regenerate correspondence fixtures (`Correspondence/**`).

It is one interlocking proof development and parallelizes poorly. A separate Lean impact survey against this spec is the way to turn "weeks-to-months" into a firmer number.

## 10. What does NOT change

- **Cuts, polarity, negation.** `cut` regions, `cutDepth`, and `polarity` are untouched; all quantifier ordering that matters is already carried by cuts.
- **Term wires** and first-order individuals: representation and rules unchanged.
- **`headstrip.ts` binders** (λ-binder counts): unrelated; do not touch (§5.7).
- **`diagonalize`**, `ref`/named-relation folding arity, and `requireSpawnPolarity`: unaffected by the sort change.
- **The logic itself.** Provability and soundness are preserved; this is a faithful re-encoding of the same second-order system, justified by bubble polarity-transparency (§1). Second-order remains the ceiling — relation wires bind relations over individuals; relations-over-relations would need a further sort, exactly as the bubble system's atoms already imply.

## 11. Non-goals

- No change to the underlying logic, rule set (beyond the encoding), or expressiveness.
- No third-order extension.
- No implementation in the originating session — this spec fixes the target; sequencing (representation design → Lean impact survey → TS refactor → Lean refactor) is decided separately.
