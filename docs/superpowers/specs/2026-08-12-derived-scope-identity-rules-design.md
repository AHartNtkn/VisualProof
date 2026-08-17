# Identity rules under derived scope

Status: draft for ratification. Nothing here is implemented; no code changes
accompany this document.

This finalizes the identity rules for the refactor that deletes stored wire
scope and derives it from incidences. The rules are three, derived in §3
from the three semantic facts identity apparatus carries — per-wire
quantifier data, per-region equality relations, and nothing else:
**vacuity** (⊤-apparatus is free), **presentation invariance** (equality
has no syntax), and **identification** (the one-point principle). Each is
stated in its strongest sound form (user ruling: interaction strength
outranks axiomatic parsimony; §8), each is an ungated equivalence, and each
preserves every surviving wire's derived scope. Everything gated about
equality — asserting it, discarding it, substituting through it, and moving
a quantifier — stays in the existing insertion/erasure, iteration, and
join/sever families, whose gates are unchanged.

Two amendments to the earlier proposal. First: collapse no longer deletes
the identity node — keeping it (shrunk by the absorbed ports) makes the
survivor's scope preservation a theorem instead of a side condition; the
full "node vanishes" collapse remains a macro. Second (2026-08-12 review
ruling): **every wire has at least two ends, and a wire end is a node** — a
one-incidence wire is a line from a point to nowhere, geometrically
impossible and therefore unrepresentable — which re-derives the stub,
fusion, exposure, and detach statements of §3 and the remnant handling in
§5. Both open questions from the proposal are resolved below (§11): nullary
identities are typed, and quantifier relocation is derived from join/sever,
not an identity rule.

## 1. Representation

Definitions used throughout:

- An **incidence** of a wire is either an endpoint on a node (atom, ref, or
  identity port) or an entry in the diagram's ordered boundary. A node
  endpoint's region is the node's region; a boundary entry's region is the
  root.
- **derivedScope(w)** = the deepest common ancestor (DCA) of the regions of
  all of w's incidences. `deepestCommonAncestor` already exists
  (`src/kernel/diagram/regions.ts:24`); it extends to a set by folding.
- "R lies **under** S" means S is an ancestor-or-equal of R (the existing
  `isAncestorOrEqual(S, R)`), i.e. R is inside S's subtree.
- A wire is **visible** at region R when R lies under derivedScope(w). This
  is the same condition the kernel checks today against stored scope.

Changes:

- `Wire` becomes `{ sig, endpoints }`. The `scope` field is deleted.
- `IdentityDiagramNode.arity` ranges over all naturals. The `arity ≥ 2`
  validation (`diagram.ts:212`) is deleted. `requiredPorts` already returns
  `[]` for arity 0 with no change.
- Identity ports remain index-addressed in storage but are semantically
  unordered (already law, 2026-07-25 spec); canonicalization quotients port
  permutation on identity nodes.
- The semantic authority is the diagram **with its ordered boundary**
  (today's `DiagramWithBoundary`); a closed diagram is the empty-boundary
  case. Derived scope is a function of that pair, because boundary entries
  are incidences. The `mkDiagramWithBoundary` requirement that boundary wires
  be root-scoped (`boundary.ts:28`) is deleted: a boundary incidence is at
  the root, so the DCA of any boundary wire's incidences is the root by
  construction.
- **Every wire has at least two ends** (2026-08-12 ruling, this review). A
  drawn wire runs from one point to another; a wire end IS a node, so a
  non-loop wire with one incidence is geometrically impossible and must be
  unrepresentable. This is the kernel form of the standing loose-ends law
  (2026-07-04: dangling ends are their own nodes). Validation: incidence
  count (endpoints plus boundary entries) ≥ 2. Duplicate ports count
  separately — a wire attached twice to one node is a loop, which is
  drawable. The old endpoint-free wire is replaced by the nullary identity
  (§2); the old one-endpoint wire is replaced by the wire plus its end node,
  a pin — making today's renderer-synthesized free-tip bodies
  (`engine.ts:308`) real, one for one. The old "wire scope must enclose
  every endpoint" check is deleted — derived scope is an ancestor of every
  incidence by construction.

## 2. What an identity node means

An identity node at region R with signature σ attached to the wire set W
contributes content to R, read by R's cut parity like any node:

| arity | attached wires | contributed content at R |
|---|---|---|
| 0 | none | ∃x:σ.⊤ — a floating existential, the former endpoint-free wire. Its truth uses the standing inhabited-domain assumption (`PreModel.inhabited`, Model.lean), the same assumption ungated vacuous elimination already relies on. |
| 1 | one wire w | x_w = x_w, i.e. ⊤. Its whole effect is the incidence: it holds w's derived scope at least as high as R. |
| ≥2 | w₁…wₖ | the wires' values are all equal (n-ary all-equal), as in the 2026-07-25 design. |

A unary identity used only to hold a wire's scope is called a **pin** below.
Duplicate ports (one node attached twice to the same wire) are legal and
semantically idle; presentation invariance (§3)
interconverts them with the single-port form.

Two consequences worth stating plainly:

- A wire whose incidences are all deep except a pin at R has its existential
  quantifier at R. This is the semantic replacement for today's
  scope-above-endpoints wires and for the renderer's synthesized dangling-end
  bodies: the ∃ dot becomes a real node.
- A floating existential is content, never normalized away (2026-07-30
  ruling). Nullary and unary identities inherit that protection: no rule in
  this document fires eagerly. Eager normalization is deleted entirely
  (§7, §9).

## 3. The three identity rules

Derived from what identity apparatus means, not accreted (2026-08-12 review
rework). The apparatus in a diagram carries exactly three independent
semantic facts:

1. **per wire** — its sig, its derived scope, and its non-identity
   attachments (the quantifier, and what it feeds);
2. **per region R** — the equivalence relation generated on wires by the
   identity nodes homed at R (what is asserted equal, and where);
3. **nothing else** — node count, port multiplicity, points, pins, and
   stubs are either scope-carrying (fact 1) or denote ⊤.

A transformation is free — ungated, direction-free at any polarity — exactly
when it changes none of the three facts. The freedoms those facts leave open
are the rules, one per freedom, each in its strongest sound form:

**Vacuity (⊤ is free).** Exactly three primitive shapes, each an
insert/delete equivalence with directly checkable conditions and no shape
search: a **point** (an arity-0 identity node of any sig, at any region,
no conditions); a **stub** (a fresh wire from a fresh port on an existing
identity node to a fresh arity-1 far point, the far point at-or-under the
node's region — the one soundness line: the fresh quantifier is born
where the equality justifying it lives, since a fresh wire quantified
above its equality is the standing counterexample ∃w@S ¬(w = x), which is
not ⊤); and a **pin** (a fresh arity-1 identity node on an existing wire,
anywhere the wire is visible; detach only where the wire's derived scope
stays put and two ends remain). Every larger piece of ⊤-apparatus — the
bare two-pin wire (point, then stub), multi-pin shapes, equated clusters —
is a COMPOSITION of these plus identification exposure, checked one
primitive at a time; the general "any ⊤-shaped assembly appears and
vanishes freely" statement is a THEOREM about the closure of the
primitives (§6's decomposition corollary), never a kernel acceptance
condition. (2026-08-14 amendment: an earlier revision made the kernel
accept whole assemblies through an absorption-fixpoint checker; that
checker internally computed exactly this decomposition and threw it away,
so it was retired for the primitives it was simulating.)

**Presentation invariance (equality has no syntax).** Two
configurations of identity nodes at one region R, of one sig, over the same
wire set — every node covering at least one wire, every wire of the set
holding at least one port in both, every wire keeping at least two ends —
that generate the same equivalence relation, are interchangeable in one
step. Which nodes, how many, and with what port multiplicities present the
relation is syntax, not content. The every-node-covers-a-wire condition is
the rule's licence line, not bookkeeping: a wireless node is a point,
∃x:σ.⊤ — content sound by inhabitedness — and its appearance and
disappearance belong exclusively to vacuity (2026-08-14: the
implementation accepted points on either side, since a coverage-empty node
passes a same-wire-set check vacuously; refused now, keeping §8's
"vacuity is the only source and sink of nullary nodes" true and the Lean
presentation lemma free of the inhabitedness axiom).

**Identification (one-point).** A wire quantified exactly at the
region where it is equated to a survivor is the survivor, mentioned twice:
its mentions may transfer to the survivor and the wire vanish, or split off
it. The equating node outlives the move (its port on the survivor is what
makes scope preservation a theorem rather than a side condition).

Everything with logical force — changing a relation, moving a quantifier —
changes fact 1 or fact 2 and is therefore outside all three rules; it lives
in the gated families of §4, unchanged. One diagram edit may be licensed by
more than one rule (a stub grows under vacuity, and equally as an
identification split of a freshly pinned mention); the rules are truths a
step cites, not mechanisms that partition the moves.

A kernel step cites one rule and its parameters, and each rule's
conditions are mechanically checkable with no search (three fixed schemas
for I; union-find relation equality for II; the co-scope check for III).
For vacuity the worked instances below ARE the rule — one subsection per
primitive; for the other two rules they are readings at gesture size with
conditions specialized and soundness citations spelled out. They carry
plain names (point, stub, pin, contract, fusion, collapse) used by the
rest of this document and by the interaction layer.

### Vacuity, worked

**Point introduction / elimination.** Add or remove a nullary identity node
of any well-formed sig at any region. No side conditions; touches no wire.
Soundness: ∃x:σ.⊤ ≡ ⊤ under domain inhabitedness, and conjoining or
removing ⊤ inside any context is an equivalence. This restates today's
`applyVacuousIntro`/`applyVacuousElim` (`rules/vacuous.ts`), which currently
create and delete endpoint-free wires; those wires no longer exist. The
Q / Shift+Q gestures commit it with σ = ι and σ = rel([]).

**Stub growth / retraction.** A **stub** is a fresh wire ending in a fresh
single-port point. Growth: given any identity node ι at R, any arity, mint
a fresh wire w of ι's sig and a fresh point p at any region R′ under R;
w's two ends are a new port on ι and p's port. Retraction: the reverse, on
any wire whose only incidences are one ι-port and the single port of a
point at R′ under R (boundary wires never retract: a boundary entry is a
third incidence). Soundness: at arity 0 both sides read ∃x:σ.⊤ at R — the
point, and the drawn segment x=x ∧ x=x; at arity ≥ 1 the stub reads
∃w@R (w = class ∧ ⊤@R′) ≡ ⊤, witnessed by any class member. R′-under-R is
vacuity's absorbability condition in the flesh: it keeps w's quantifier at R,
where the equality that justifies it lives; a point outside R would home
the quantifier above the equality (∃w@S ¬(w=x) fails in a two-element
domain), and moving a quantifier is §4.4's gated business.
derivedScope(w) = DCA(R, R′) = R by construction; w has two ends from
birth; the arity-0 instance draws as a segment between two point glyphs —
exactly how the renderer draws a bare wire today (two synthesized free-tip
bodies), now semantic. This is the growth point twice over: point-then-
grow spawns a quantifier a user can start attaching things to, and growth
on a wired node pulls a fresh equal-to-the-class wire out in one gesture.

**Pin attach / detach.** Attach a nullary node to an existing wire w
(arity 0 → 1), or remove a unary node's port from its wire (1 → 0).
Attach requires w visible at the node's region — then the new incidence
cannot move any scope. Detach requires the wire's derived scope unchanged
by the removal AND at least two incidences remaining (§1's floor — the
last-but-one end is as undetachable as a load-bearing pin). Composing
point introduction with attach places a pin on w at any region where w is
visible — always available; this is the "pin first" preparation the
preconditions in §5 assume. What detach refuses is the point of the
statement: a pin whose removal would let the wire's scope fall IS the
quantifier's position, and only the gated relocation derivation (§4.4)
may move it.

### Presentation invariance, worked

**Duplicate / contract.** Add another port of a node onto a wire it already
holds, or remove one of several such ports. Both presentations generate the
same relation; contract additionally requires the wire to keep two ends and
the node's remaining port keeps the region incidence, so every DCA is
fixed.

**Fusion / fission.** Fusion: any finite set of identity nodes at one
region R, same sig, whose sharing graph is connected (nodes as vertices, an
edge where two share a wire), merges into one node at R carrying the union
of the ports — multiplicities preserved, so shared wires end up as loops on
the fused node, and no wire's end count changes; contract tidies loops
afterwards when its guard allows. Fission: one node splits into any
port-partition over nodes at R whose sharing graph is connected — every
part linked to the rest through wires holding ports on both sides
(duplicate first when a linking wire has only one port). Soundness:
transitivity of equality through the spanning wires, all conjuncts read at
one region. The spanning wire is what makes both directions
presentation-preserving: without it, fusion would invent a cross-equality between the
classes (strengthening) and fission would silently drop a membership
(weakening) — those two moves exist only as §4.1's gated class operations.
The port-union formulation replaces the draft's wire-set union, which
collapsed multiplicities and could leave a shared wire one-ended — fusing
the two end points of a bare segment would have stranded the wire with a
single port, an undrawable object under §1. Every wire involved keeps at
least one port at R on some resulting node; every DCA is fixed. This is
the explicit form of the canonicalizer's `fuseIdentities`
(`canonical/identity.ts:93`). Fusing nodes at *different* regions is not
free: moving equality content between regions is the ordinary
iteration/deiteration/erasure business of §4.

### Identification, worked

**Collapse / exposure.** Collapse: given ι at R with attached wires W, a
designated survivor s ∈ W, and a nonempty absorbed set A ⊆ W∖{s} where
each a ∈ A has derivedScope(a) = R (equivalently: every incidence of a
other than its ports on ι lies under R): every non-ι incidence of every
a ∈ A — endpoints and, when R is the root, boundary entries — transfers to
s; ι's ports on A are removed; the wires in A are deleted; ι survives,
attached to (W∖A), including s. Exposure: the reverse — given ι at R
attached to s (pin first if needed), a fresh wire w′, and a nonempty set E
of s's incidences whose regions all lie under R: add a port of ι on w′ and
transfer E from s to w′. E nonempty is §1's floor (w′'s ends are its
ι-port plus E); the empty-E form the draft allowed is struck on geometric
grounds only — ∃y@R (y = x) is still an equivalence, and its drawable form
arrives by exposing one real under-R incidence, e.g. a pin s already
carries. Soundness: the one-point rule ∃y@R (y = x ∧ Φ(y)) ≡ Φ(x), an
equivalence at any polarity — the citation both prior identity specs
carry; the absorbed wire's quantifier must sit exactly at R for the rule
to eliminate it, which is what the co-scope condition says in incidence
terms. Scope preservation is a theorem, not a condition: the survivor
keeps its port on ι, so R stays in its incidence set, and for any region
set X with R ∈ X, DCA(X) = DCA((X ∖ subtree(R)) ∪ {R}) — members under R
contribute nothing beyond R itself. Collapse only adds under-R incidences
to s; exposure only removes under-R incidences from s.

**The amendment.** The earlier proposal (and today's `collapseIdentity`,
`canonical/identity.ts:64`) deletes the node and merges everything at once.
Deleting the node removes the R incidence from the survivor, and then the
survivor's scope can fall — which forced a survivor-scope side condition
and, in the eager normalizer, is outright wrong once scope is derived.
Keeping the node makes preservation automatic. The old full collapse is the
macro: collapse all of W∖{s} (identification) → contract ι's spare ports
on s (presentation) → detach (vacuity, which now correctly refuses when the
leftover pin is load-bearing) → eliminate the point (vacuity).

### Closure property

**Theorem (to be pinned by tests and by the Lean port):** every step
licensed by the three rules preserves the derived scope of every wire that
exists on both sides, and is exactly invertible by a step of the same rule.
The identity rules therefore never move a quantifier. Quantifier movement
exists in the system only as §4.4's join/sever derivations, where it is
explicitly gated.

## 4. Gated equality operations — not identity rules, and how they compose

These stay in their existing families with their existing gates. Under
derived scope their statements change only as §5 notes.

### 4.1 Asserting and discarding equality

`applyIdentityInsertion` (`rules/identity.ts:28`) is unchanged in substance:
insert an identity node of arity ≥ 2 on distinct wires visible at a negative
region (forward; positive backward). Visibility means each added port sits
under each wire's derived scope, so insertion is automatically
scope-preserving. Discarding is ordinary erasure of the node at positive
parity, now under the erasure precondition of §5. The finer port-level moves
are derived:

- **Extend a class** (add wire w to an existing node ι at R, arity ≥ 1, w
  distinct from its wires): insert a fresh binary identity on {w, m} at R for
  any m already attached to ι (negative gate), then fuse (presentation). Net gate:
  negative, as it must be — the class grows.
- **Shrink a class** (remove one wire w from ι, keeping ι otherwise):
  fission (presentation) into ι₁ on W∖{w} plus a binary ι₂ on {m, w} (sharing m),
  then erase ι₂ (positive gate). Net gate: positive.

These derivations replace any temptation to gate port-level moves
individually: the ungated port moves are exactly the ones vacuity and
presentation invariance license.

### 4.2 Substitution — an equivalence, now derived ungated

Leibniz substitution only looks like an implication; x=y ∧ P(x) ⇌
x=y ∧ P(y) is symmetric, and under these rules it derives with no gate at
all (2026-08-12 review finding):

1. iterate the identity node into the use region (equivalence; the
   identity must dominate the site, the classical condition);
2. exposure (identification): split P's mention of a off the survivor onto
   a fresh wire equated to the class at the use region;
3. collapse (identification): absorb that fresh wire onto b — its only
   other mention is P's port at the use region, so the co-scope condition
   holds by construction;
4. deiterate the copied node (equivalence, justified by the original).

This supersedes the 2026-07-29 derivation (iterate → gated sever →
collapse), which predates exposure; a gated step inside a derivation of an
equivalence was a seam, and it is gone. The sever route stays sound and
remains what old retargeted theory steps may compile to, but the ungated
composite is canonical. As before, the landing is explicit — the proof
records the identification steps; the diagram never changes behind the
proof's back.

### 4.3 Conversion between shared-wire and node form

Both directions are identification plus cleanup, at any polarity, because both
forms of an unconditional co-located equality are equivalent (the
2026-07-25 "one notion, two syntactic forms" reading survives; only the
*eagerness* dies). Splice keeps creating identity nodes at the application
region when several boundary positions land on distinct host wires; they
now persist until a recorded collapse absorbs them.

### 4.4 Quantifier relocation

Resolved: **derived, not primitive** — from the join/sever family, whose
gates already sit in the right place.

- **Outward** (raise derivedScope(w) from S to an ancestor S′): grow a
  fresh two-pin segment at S′ (vacuity) and `applyWireJoin` it with w as the
  inner wire; the spare pins then detach (vacuity — their guards pass: the
  merged wire keeps an S′ pin and its real ends). Join's gate is the inner
  wire's scope, negative forward (`wire-quantifier.ts:148`), and the merged
  wire's derived scope is DCA(S, S′) = S′ automatically.
- **Inward** (let scope fall to the DCA of a chosen incidence subset):
  `applyWireSever` moving those incidences onto the fresh wire, whose scope
  parameter materializes as a pin (§5), then retract/eliminate or re-merge
  the remainder as the proof requires. Sever's gate is the chosen scope's
  polarity, positive forward (`wire-quantifier.ts:61`).

A dedicated relocation primitive (or the ∃-dot drag gesture) can be added
later as a macro over exactly these steps; nothing in this document blocks
it, and nothing requires it.

## 5. Obligations on every other rule

The kernel-wide invariant, stated once: **an incidence-changing rule either
(a) provably preserves every surviving wire's derived scope, (b) carries a
hard precondition that it does, or (c) carries an explicit scope parameter
whose value above the natural DCA materializes as a pin.** Silent quantifier
movement is thereby impossible; declared movement exists only where a rule's
own statement is about scope (join, sever). "Pin first" (vacuity) is always
available to satisfy a class-(b) precondition, because a pin at the current
derived scope is always visible there.

Per rule, against the current inventory (`src/kernel/rules/`):

| Rule | Class | What changes |
|---|---|---|
| erasure (`erasure.ts`) | (b′) | `removeSubgraphParts` keeps touching wires with endpoints filtered; losing an endpoint can drop a DCA or the two-end floor. 2026-08-17 amendment (from the Lean soundness pass — `Erasure.residue`): the rule CAPS instead of refusing — every surviving touching wire is completed with pins at its pre-removal derived scope, so no quantifier moves and no wire drops below two ends. The cap is a no-op on already-held wires, so proofs recorded under the old pin-first discipline replay unchanged. A wire wholly inside the selection dies with it — no residue. |
| insertion (negative splice) | (a) | Adds incidences at-or-under the host region where the attached host wires are visible; DCAs cannot move. |
| iteration (`iteration.ts:20`) | (a) | Copies attach to the same host wires at a descendant region: incidences added under existing ones. |
| deiteration (`iteration.ts`) | (b′) | Removes the copy's endpoints; caps exactly as erasure does (the Lean twin: `Iteration.uncopyResidue` — a pin for each wire whose quantifier support the copy's mentions gave it). |
| double-cut intro (`doublecut.ts:27`) | (c) | Reparenting moves the selection's incidences two cuts deeper, while today no wire's stored scope changes — every quantifier stays outside the new double cut ("pass through the empty annulus"). Restated faithfully: every wire whose derived scope the reparenting would change receives a pin at its old derived scope. Such a wire's old scope is necessarily `sel.region` (its incidences all move, and their DCA cannot exceed the selection's region), the pin is visible there, and the deposit is the rule's declared scope transport — sound because an even crossing over an empty annulus is an equivalence, and the annulus is empty at creation. Wires scoped inside a selected subtree move whole and need nothing. |
| double-cut elim (`doublecut.ts:59`) | (a) | The annulus-emptiness check "no wires scoped there" becomes "no nodes there" — a pin in the annulus is a node and blocks, which is correct: it marks a quantifier living in the annulus. Promoted content moves two cuts up together; pass-through wires keep their outside incidences. |
| wireJoin (`wire-quantifier.ts:116`) | declared | Merged incidence set's DCA = DCA of the two derived scopes; the outer-scope survival and the comparable-scopes check are now computed, not stored. Gate unchanged (inner scope negative forward). |
| wireSever (`wire-quantifier.ts:50`) | (c) | The `scope` input survives as an explicit parameter, materialized by the completion clause below: each side of the split (fresh wire and remainder) is completed with pins at its declared scope — the fresh wire's chosen scope, the remainder's old derived scope — until it has two ends. That covers the draft's cases (scope above the moved DCA; `keep = ∅`'s husk, now a bare two-pin segment; a single moved endpoint, whose fresh wire needs its second end). Gate unchanged (chosen scope positive forward). |
| vacuousIntro/Elim (`vacuous.ts`) | replaced | Restated as vacuity's point introduction/elimination; endpoint-free wires no longer exist. |
| cutWrap / cutAbsorb (`wire-content.ts:32,72`) | (c)/(b)+(c) | Both create a successor wire that today carries `scope: old.scope` verbatim; the successor clause below reproduces that. Wrap puts each fresh end in a cut under the old end's region: a multi-end wire's end-DCA is unchanged, a single-end wire's would fall one cut — the successor clause deposits the pin that keeps it. Absorb lifts each end to its cut's parent: the end-DCA can only rise, so it carries the precondition that the successor's incidence DCA still lies under the old derived scope — the derived-scope form of today's "no wire scoped in the end's cut" check (`wire-content.ts:95`), and the case it excludes (a wire quantified exactly in the dissolving cut) is a genuine one-cut quantifier move, which belongs to §4.4, not to an equivalence. |
| parallelSplit / parallelFuse | (a) | Fresh wires' ends sit at the old ends' regions; with pin transfer (split: pins duplicate onto both halves; fuse: pins merge) scopes are preserved. Pin duplication is sound: ⊤ content copies freely. |
| endsDelete / endsSpawn (`wire-content.ts:273,306`) | (c)/(b) | Delete removes every applied end and completes the wire with pins at its old derived scope — reaching two ends, so the endpoint-free husk (today's output) becomes the bare two-pin segment, removable by vacuity. The removed end nodes' argument wires lose endpoints — precondition as for erasure, pin first. Spawn adds ends at chosen sites (sites under the wire's derived scope — preserving) and removes completion pins only via vacuity's detach, under its guards. Gates unchanged. |
| arityShift / arityUnshift (`wire-args.ts:107,143`) | (a) | Shift's per-site fresh wires have their sole incidence at the site — derived scope lands there with no stored field. Unshift's side condition ("attached wire scoped at the site, endpoints exhausted by the occurrence") is computed on derived scope, same meaning. |
| argPermute / argDuplicate / argContract | (a) | Endpoint rearrangement at fixed nodes and regions. |
| argDrop / argExtend (`wire-args.ts:312,352`) | (b)/(a) | Drop removes one endpoint per site from the position's wires — erasure-style precondition. Extend attaches to per-site visible wires (`wire-args.ts:404`) — preserving. Gates unchanged, including the ungated case when all sites share one attachment wire visible at the acted wire's scope (`uniformVisibleAttachment`, `wire-args.ts:300`), whose witness comment already carries its justification; "visible at the acted wire's scope" is computed on derived scope. |
| applyFormal / abstractFormal | (a)/(c) | Apply-formal deletes the acted wire (instantiation): its pins are ⊤ content on a dying quantifier and are deleted with it — the one successor-less case, and the deletion is free. Abstract-formal creates the fresh wire with a chosen scope: parameter materializes as a pin when above the new ends' DCA. |
| identityLeaf / identityAbstract (`wire-args.ts:601,672`) | (a)/(c) | Leaf turns each end into an identity node at the end's region, attaching arg wires there — visible, preserving; the acted wire dies as in apply-formal. Abstract's `scope` parameter materializes as a pin, like sever. Gates unchanged. |
| refLeaf/refAbstract, refSpawn/atomSpawn, fold/unfold | (a)/(c) | Spawns create fresh wires whose incidences are the spawned ports (scope = spawn region, no field needed; `diagram/spawn.ts:22,68`). refLeaf deletes the acted wire outright like apply-formal (`wire-args.ts:809`) — its pins die freely; refAbstract's caller-supplied scope (`wire-args.ts:912`) materializes as a pin like abstract-formal. Fold/unfold splice bodies: unfold's fresh wires take mapped pattern scopes (`splice.ts:214`), realized by their copied incidences; splice-created alias identities persist (§4.3); fold's occurrence check compares derived scopes where it compares stored ones (`fold.ts:126`). |

Two blanket clauses:

- **Successor and remnant completion.** Wherever a rule replaces a wire by
  a successor covering the same value (cut-wrap/absorb, parallel
  split/fuse, arity-shift, permute/duplicate/contract) or leaves a remnant
  (sever's two sides, ends-delete), the 2026-07-29 side condition "fresh
  wires are co-scoped with the old wire" materializes as one clause: pins
  (arity-1 identity endpoints) transfer to the successor at their regions,
  and the wire is then **completed with pins at its declared scope** — the
  old derived scope unless the rule has an explicit scope parameter — until
  two conditions hold: its incidence DCA equals the declared scope, and it
  has at least two ends (§1). If realizing the declared scope would require
  the DCA to fall (only cut-absorb can ask this), the rule is inapplicable
  — precondition, per that row. Split duplicates pins onto both halves (⊤
  content copies freely); fuse merges them. Arity-≥2 identity endpoints
  remain blocked by the existing applied-ends requirement (`appliedEnds`),
  except in merge, exactly as today. Apply-formal and identity-leaf delete
  the acted wire outright — a dying quantifier's pins are ⊤ content and die
  with it, freely.
- **Selection semantics.** `SubgraphSelection.wires` ("top-level wires") and
  `selectionContents`' internal/touching split (`selection.ts`) read derived
  scope where they read stored scope today. No behavioral redefinition.

Future rules (the drawn-definitions comprehension pair) inherit the same
invariant; their design already places all created incidences at the
application region.

Construction mode (`src/app/edit.ts`, explicitly not rules) writes scopes
directly today: `joinWires` writes the DCA of the merged scopes (:172),
`severEndpoint` copies the original scope to both pieces (:229),
`reparentNode` narrows a stale scope to a DCA (:353), `wrap` and
`dissolveRegion` re-home enclosed wires. Every one of these becomes a
non-operation or a pure incidence edit: derived scope already computes the
value these lines write. `addIdentity` (:121) keeps its visibility check and
its deliberate gatelessness.

## 6. Validation and authority changes

`validateRawDiagram` keeps: root/cut-tree checks, node sig checks, port
existence/sig/uniqueness checks. It changes:

1. identity arity: any natural (delete the ≥ 2 floor).
2. delete the wire-scope existence and enclosure checks (`diagram.ts:234,264`).
3. add: every wire has ≥ 2 incidences (§1's two-end floor). For a bare
   `Diagram` that means ≥ 2 endpoints; the boundary-bearing authority
   counts boundary entries as ends and performs the combined check. A
   definition formal exposed at one boundary position therefore carries a
   root pin as its second end (its drawn form: the wire from the frame
   exit to the ∃ point).
4. `mkDiagramNormalized`, `DiagramNormalization`, `wireImage`,
   `captureDiagramNormalizations`, and `withoutDiagramNormalizationCapture`
   are deleted with the eager normalizer; `mkDiagram` = validate + freeze.
   Every call site that consumed a wire image now has stable ids by
   construction — no rule ever renames a wire it does not delete.

The Lean mirror tracks the same changes, and its scope-bearing surfaces are
known (inventoried 2026-08-12): the `scope` field (`Concrete/Diagram.lean:22`),
`WireScopesEnclose` and `boundary_is_root_scoped`
(`Concrete/WellFormed.lean:128,159`), selection ownership by scope
(`Concrete/Subgraph/Selection.lean:46`), scope-survival in removal
(`Concrete/Subgraph/Remove.lean:201`), extraction re-scoping
(`Concrete/Subgraph/Extract.lean:801`), step boundary transport via
root-scopedness (`Concrete/Step/Core.lean:104`), and — the structural one —
`wire_scope_eq` in `Concrete/Isomorphism.lean:138`, which makes stored scope
isomorphism-relevant data. Under derived scope that field and that
isomorphism component are deleted: isomorphism becomes purely structural, and
the information it carried survives as the pin nodes themselves, which any
isomorphism must already map. "Root-scoped" in step transport becomes
derived-root-scoped, computable. The soundness statement for each rule is one
of the citations already in this document (⊤-conjunction and inhabitedness;
transitivity; one-point).

Vacuity's Lean obligations follow the 2026-08-14 amendment. Per primitive
and direction, a small equivalence lemma: applying a point, stub, or pin
insert (or its delete) to a well-formed diagram yields a diagram whose
interpretation is equivalent at every valuation, with every surviving
wire's derived scope unchanged (point: ⊤-conjunction under inhabitedness;
stub: ∃x (x = class) ≡ ⊤ witnessed by any member, the at-or-under
condition placing the fresh quantifier at the equality's region; pin:
x = x). Then ONE decomposition corollary replaces the retired monolithic
assembly theorem: for any assembly A over diagram d satisfying the old
generic conditions (each connected component touches at most one existing
item; the absorption fixpoint empties A's wires), there is a finite
sequence of primitive vacuity steps and identification-exposure steps
whose composite, applied to d, is isomorphic to d ∪ A — so the generic
rule's semantic correctness follows from the per-primitive lemmas plus
the identification lemma by induction on the sequence, and the large
direct proof is retired. The witness sequence is the accepting fixpoint
run read backwards: a bare-⊤ absorption reversed is point-then-stub (plus
pin attaches for extra ends), and an equated absorption with transfer
reversed is an identification exposure.

Two TypeScript surfaces mirror this exactly: the canonical-form key currently
includes stored wire scope (`canonical/explore.ts:175-177`) and drops it the
same way, and the matcher's wire-compatibility check
(`subgraph/match.ts:327`) — exact scope equality for non-boundary pattern
wires, enclosure for boundary wires — is computed on derived scope with the
same meaning. The matcher and canonicalizer already treat identity ports as
an unordered incidence set (`explore.ts:180`, `match.ts:66`), so the
port-permutation quotient of §1 is current behavior, not new work.

A supporting observation for deleting the eager normalizer: `fuseIdentities`
renumbers every port of the fused node (`canonical/identity.ts:103,123`), so
today any holder of an identity endpoint across a `mkDiagram` call may hold a
stale index — the wire-image transport exists to launder exactly this. With
no eager rewriting, identity ports are stable like every other id.

## 7. The old normalizer, replayed as explicit steps

Completeness against what is being deleted — each eager rewrite of
`canonical/identity.ts` is a composition of rule steps, and nothing else was
eager:

| Eager rewrite (deleted) | Explicit replay |
|---|---|
| `dropIdentity` — node with one incident wire vanishes | Contract each duplicate port (presentation), detach (vacuity), eliminate the point (vacuity). Where a step refuses — the incidence was scope-supporting, or the node is one of the wire's two ends — the old rewrite was producing a wire that either meant something else or could not be drawn at all (its output was a one-endpoint wire); the refusal is the fix, and the node stays as the end or pin it really is. |
| `collapseIdentity` — one-point merge, node deleted | Collapse all absorbed wires (identification), contract, detach, eliminate — §3's macro, with the same caveat: a load-bearing pin survives. |
| `fuseIdentities` — same-region fusion | Fusion (presentation invariance), verbatim. |

Diagrams formerly identified silently are now distinct and connected by
recorded reversible steps. Canonicalization keeps only structural isomorphism
(including identity-port permutation).

## 8. Primitive core

The rules are deliberately NOT minimal (user ruling, 2026-08-12): each is
stated at its full strength, because convenience of interaction outranks
axiomatic parsimony — a condition must be a soundness or drawability
requirement, never bookkeeping for a smaller axiom set. What this section
records instead of independence is the primitive core: the effects no
composition of the other rules and gated families reaches, which is why
each rule must exist.

- **Vacuity:** the only source and sink of nullary nodes, and — through stub
  growth at arity 0 — the only birth of a wire from a bare point: exposure
  needs an attached wire to expose from, fusion a shared wire to fuse
  through, and a bare point has neither. (Higher-arity stub growth equals
  the composition point → pin attach → exposure and is kept in-rule as
  strength.)
- **Presentation invariance:** the only ungated re-presentation. The gated route to fusion's
  effect (§4.1 extend + shrink) needs a negative and a positive gate at the
  same region — unavailable in any single parity — so an ungated rule is
  required for what is semantically an equivalence.
- **Identification:** the only ungated wire merge. The other wire-merger is join,
  which is gated and demands comparable scopes, so it cannot express the
  co-located ∃y (y = x ∧ Φy) ≡ Φx move at positive parity.

Wire-set bookkeeping, for orientation (a correction is folded in here: an
earlier revision claimed the wire count changes only under stub steps —
false, collapse deletes absorbed wires and exposure mints the carved-off
one): presentation invariance never creates, deletes, merges, or splits a
wire; identification merges and splits wires already equated to one
another; vacuity creates and deletes wires outright, equated (stubs on a
class) or not (bare segments).

## 9. Consequences for matching, theorem checking, and rendering

- **Matching / occurrence certificates:** wire-scope equality tests become
  derived-scope tests; identity nodes are ordinary content to match (they
  already are). No matcher proposes identity moves; it validates, as ruled.
- **Theorem declaration:** `checkTheorem`'s dual replay meets on canonical
  forms; identity configurations now count. Two derivations that used to be
  silently normalized into agreement must end with the same explicit
  identity steps. Existing theorem stores and `examples/frege.json` replay
  through migration (§10), which inserts those steps.
- **Rendering:** the renderer stops synthesizing end bodies entirely —
  free tips (`engine.ts:308`), scope dangles, and centroid stand-ins. Under
  the two-end floor every drawn wire end is a real node (a pin or other
  port), one for one with the bodies the renderer fakes today; pins and
  nullary points draw like any node with the existing point glyph. Physics
  gains nothing new to fake.

## 10. Migration

Deterministic, per stored diagram, in dependency order:

1. Endpoint-free internal wire → nullary identity at its stored scope, same
   sig (vacuity's point).
2. Every other wire: compute the DCA of its endpoint regions plus root for
   each boundary entry. Add pins at the stored scope until both hold: the
   incidence DCA equals the stored scope, and the wire has at least two
   ends. (One clause covers every case: singleton wires gain their end pin
   — the renderer's free-tip body made real, one for one; scope-above-DCA
   wires, including double-cut intro's, gain their scope pin;
   single-position boundary formals gain their root pin.)
3. Delete `wire.scope`; delete the eager normalizer and wire-image
   transport; apply §5's rule restatements and §6's validation changes.
4. Proof histories: wherever a recorded step's replay formerly triggered an
   eager rewrite, splice the §7 replay's explicit steps into the history.
   Serialized step schemas keep their `scope` fields — on `vacuousIntro`
   (now the point step's region), `wireSever`, `abstractFormal`,
   `identityAbstract`, `refAbstract` (`proof/json.ts`) — because those are
   rule inputs, not stored state; only the diagram-side `wire.scope` leaves
   the format. Theory scripts and fixture builders that write scopes
   (`src/theories/`, `diagram/builder.ts`) migrate mechanically by rule 2.
5. Acceptance theorem, checked over every stored diagram and both replay
   suites (frege, arithmetic): for every surviving wire,
   `derivedScope(convert(D), w) = D.wires[w].scope`, and every migrated
   history replays to a diagram structurally isomorphic to today's replay
   output modulo the now-explicit identity nodes it preserves.

## 11. Resolved decisions

1. **Nullary identities are typed** (carry sig). They replace typed
   endpoint-free wires, keep the color ladder rendering, and stub growth
   needs the sig. Untyped truth points would need a separate sig-transport
   story the moment they grow a wire.
2. **Quantifier relocation is not an identity rule.** It is derived from
   join/sever (§4.4), whose gates already encode the correct directional
   logic. This keeps the closure property of §3 — identity rules never move
   quantifiers — as a one-line kernel invariant.
3. **Every wire has two ends, and an end is a node** (user ruling,
   2026-08-12 review). A one-incidence wire is a line from a point to
   nowhere — geometrically impossible, so unrepresentable, not merely
   invalid. This re-derived the stub statement (two-ended segment, not a
   one-ported wire), fusion (port union, not wire-set union), exposure
   (nonempty transfer), detach (two ends remain), and the completion clause
   of §5. It is the kernel form of the 2026-07-04 loose-ends law, and it
   makes the renderer's synthesized free-tip bodies real nodes one for one.
4. **Strongest sound form, always** (user ruling, 2026-08-12 review): "the
   general design philosophy for the rule set has been the strongest
   versions of each rule which are still sound — mainly because we want
   convenience of interaction." Minimality restrictions are struck wherever
   they are not soundness or drawability lines: stub growth acts at every
   arity, fusion/fission on any connected set of co-regional nodes in one
   step. The conditions that remain each earn their place: the stub's
   under-R point placement and fusion's spanning wires are soundness
   (quantifier position; transitivity), detach's guards are soundness plus
   the two-end floor, collapse's co-scope condition is the one-point rule's
   own hypothesis.
5. **Three rules, no second rule list, no coined tier** (2026-08-12
   review rework, after the reviewer observed that generalized stub growth
   and exposure produce the same shapes and that the earlier five-rule
   carving read as accretion — it was, and its numbering has been deleted
   from this document; a draft's "law" tier-name for the three rules is
   likewise deleted as an unnecessary coinage). Kernel steps cite one of
   the three rules and its parameters. The worked instances of §3 carry
   only plain descriptive names (point, stub, pin, contract, fusion,
   collapse) and are readings of the rules, not rules of their own.
   Overlapping licenses between rules are accepted.
6. **No automatic pin deposits inside unrelated rules.** Preconditions plus
   pin-first composition, except where a rule's own scope parameter (sever,
   abstract-formal, identity-abstract, double-cut intro's selected wires,
   ends-delete's husk) is the declared quantifier position — there the pin
   is the parameter made flesh. Convenience composites (pin-then-erase as
   one gesture) live above the kernel, per the standing convenience law.

## 12. Supersessions

- 2026-07-25 identity-node design: the "Normalization rules (eager, silent)"
  section is superseded by §3/§7 (the three rewrites survive as explicit
  rule-step compositions); Rule 4 (insertion/erasure) unchanged; Rule 5 was
  already superseded by the 2026-07-29 derivation, which §4.2 amends to an
  explicit landing. "Ports are unordered" survives as a representation
  invariant.
- 2026-07-29 primitive wire-quantifier rules: all nine pairs survive with
  §5's restatements (pin transfer, sever/abstract scope-parameter
  materialization, ends-delete completion). Vacuous intro/elim, its tenth
  member, is replaced by vacuity's point instance.
- The refactor proposal that preceded this document: its migration table row
  "multi-wire equality" was already withdrawn (it named the existing n-ary
  identity); its one-point side condition on the survivor is removed by the
  identification amendment; everything else is carried through unchanged.
