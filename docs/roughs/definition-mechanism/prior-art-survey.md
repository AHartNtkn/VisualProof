# Prior-art survey: graphical definitions, local substitution, higher-order structure

Scope: mechanisms in diagrammatic logics / graph-based computation that handle
(D) **definitions / boxes / content**, (S) **substitution-with-locality**, and
(H) **higher/second-order structure**. Each entry maps onto the brief's four
requirements. Scores are 1–4 (4 = strong fit), scored terse.

The four requirements (abbrev):
- **R1 Wire-mediated substitution w/ graphical continuity** (local, arg-wire
  contact; never a teleport-copy).
- **R2 Drawn form derived from semantics** (no black boxes).
- **R3 The multi-wire family is the concept** (exposes content coordinates as
  wires; no privileged single-wire corner).
- **R4 Equational theory with real discharge power** (α free, βη derivable).

Verification note: every quote below carries a URL. Where a primary PDF could
not be text-extracted by the fetch tool (three PDFs returned binary/403), the
claim is drawn from the publisher/arXiv abstract or the search engine's
extracted snippet and is **explicitly labelled** as such. Nothing here is
presented as a verified primary quote unless it is one.

---

## 1. Linear-logic proof nets: exponential boxes and the "box-free" program

**What it is.** Proof nets are the graph syntax of linear logic. The
`!`-modality (exponential) is drawn as a **box**: a rectangle around a subnet,
the unit of duplication and erasure. Cut-elimination against the box performs:
weakening → erase box (garbage), contraction → **duplicate the whole box**,
dereliction → **open the box** and cut its body in.

**How substitution/copying is drawn.** As a *global* box operation. From the
search summary of the MELL literature: *"The box is the unit for erasing and
duplicating fragments of proof nets. It imposes synchronization, limits
sharing, and impedes a completely local view of computation… The graph
reduction rules involve boxes and are **not local**."*
(search-summary, [SEP Linear Logic](https://plato.stanford.edu/entries/logic-linear/);
[Exponentials as Substitutions, arXiv:2205.15203](https://arxiv.org/pdf/2205.15203)).
The title of Girard's own paper names the tension:
**"Linear logic without boxes"** ([IEEE LICS 1992](https://ieeexplore.ieee.org/document/185535/)).

**Equational theory.** Cut-elimination = the equational theory; confluent,
strongly normalising for MELL. Danos–Regnier correctness criterion decides
which graphs are proofs. Recent work (Accattoli; Kesner et al.) reads *"the
cost of cut elimination"* by treating **exponentials as substitutions**
(arXiv:2205.15203, title).

**Mapping.** R1 **1** (box copy is non-local — the exact failure mode the
brief's "teleport" complaint names). R2 **3** (box = `!`-promotion, a genuine
modality, so the region *means* something). R3 **2** (box exposes its
`?Γ`-context wires, but the body is opaque until opened). R4 **4** (mature
cut-elimination theory). *Lesson: the box has real meaning but non-local
duplication — the very reason the field spent 30 years trying to remove it.*

---

## 2. Interaction nets & optimal reduction (Lamping / sharing graphs)

**What it is.** Interaction nets (Lafont) are graph-rewrite systems where
agents interact **only at principal ports**; every rule rewrites exactly two
agents meeting at their principal ports, touching nothing else — rewriting is
**local and strongly confluent by construction**. Lamping's sharing graphs
implement Lévy-optimal λ-reduction inside this discipline.

**How substitution/copying is drawn — AS A LOCAL MOVE.** There is **no box**.
Duplication is deferred and performed incrementally by **fan** nodes; the
bookkeeping to keep fans consistent across nesting levels uses **brackets** and
**croissants** (level up/down markers). From the search summary:
*"Sharing graphs include fans, brackets (both open and close brackets), and
croissants as nodes, where the level of a node can be dynamically incremented
or decremented by open brackets (croissants) and close brackets"*
(search-summary of [Asperti–Guerrini / Geometry of Optimal Lambda Reduction](https://www.researchgate.net/publication/220997121_The_Geometry_of_Optimal_Lambda_Reduction)).
Substitution never materialises content at a distance: a β-redex rewrites two
adjacent agents; copying happens lazily as fans **slide along wires**.

**Equational theory.** λβ (and βη via read-back); Lévy-optimal = provably
fewest parallel β-steps. **The cost:** the "oracle"/bracket–croissant
accounting is famously intricate and its complexity is not benign
(search-summary, [Complexity of Optimal Reduction, Laretto](https://iwilare.com/the-complexity-of-optimal-reduction-and-sharing-graphs.pdf)).

**Mapping.** R1 **4** (the canonical realisation of purely-local, wire-mediated
substitution). R2 **3** (fan = a copy operator with meaning; brackets/croissants
are bookkeeping without independent semantics — the demerit). R3 **4** (a fan
literally *is* "sharing a family across a wire"). R4 **3** (λ-calculus theory;
but equality obscured by level bookkeeping). *Lesson: locality is achievable but
you pay in level-bookkeeping nodes that have no logical reading — a direct
warning for any fan-like copy mechanism we adopt.*

---

## 3. Melliès' functorial boxes; string-diagram λ-calculus (Ghica–Zanasi)

**Functorial boxes (Melliès).** A box in a string diagram is derived from
semantics: it **depicts a functor** transporting an *inside world* (its source
category) to an *outside world* (its target category); lax/oplax/strong
monoidal functors and the exponential `!` (a comonad) get boxes with prescribed
opening rules. From the publisher abstract (PDF fetch 403; abstract via
[Springer](https://link.springer.com/chapter/10.1007/11874683_1) and
[search-summary](https://www.researchgate.net/publication/221558328_Functorial_Boxes_in_String_Diagrams)):
*"string diagrams may be extended with a notion of functorial box depicting a
functor transporting an inside world (its source category) to an outside world
(its target category)."* This is the **gold standard for R2**: the membrane is
not rendering convenience — it is a functor, and its open/close rules are
functoriality.

**Hierarchical hypergraphs for λ (Ghica–Zanasi).** Primary quote (arXiv
abstract, [2305.18945](https://arxiv.org/abs/2305.18945)): they build
*"a graph syntax — more precisely, a hierarchical hypergraph syntax"* for
higher-order computation and *"rationally reconstruct a syntax from the
categorical model,"* claiming it is *"an improvement over the conventional
linear term syntax."* Abstraction/binding is a **box** (hierarchy); sharing and
weakening are **explicit copy/delete (comonoid) nodes**; program transformations
(closure conversion, AD) are **local graph rewrites**. Companion: string-diagram
rewriting for closed/traced categories (Alvarez-Picallo et al.).

**Mapping (functorial boxes).** R1 **2** (opening is functoriality, principled,
but still a region operation, not obviously arg-wire-local). R2 **4** (best in
survey — the box *is* a functor). R3 **2**. R4 **3**.
**Mapping (Ghica–Zanasi).** R1 **3** (rewrites are local DPO moves; sharing via
comonoid nodes). R2 **4** (syntax *derived from* the CCC model — precisely the
brief's "drawn form derived from semantics"). R3 **3** (copy nodes expose the
family; box exposes bound coordinates). R4 **3** (equational theory = the CCC
laws, βη).

---

## 4. Peirce's existential graphs beyond Beta; Sowa's conceptual graphs

**Existential graphs (the native tradition).** Primary quotes,
[SEP "Peirce's Logic"](https://plato.stanford.edu/entries/peirce-logic/):
lines of identity — *"any line of identity whose outermost part is evenly
enclosed refers to **something**, and any one whose outermost part is oddly
enclosed refers to **anything**"* (CP 4.458); reading is **endoporeutic**
(outside-in); rules by area parity — *"E-areas (even cuts): erase any graph;
draw graphs present in same/outer areas; O-areas (odd cuts): erase duplicate
graphs; draw any graph; Double cuts may be added/removed around any graph
portion."* The three systems are *"Alpha, Beta, and Gamma… propositional,
first-order, and modal logic."* **Gamma** adds **broken cuts** (modality) and
**tinctures**; the SEP notes Gamma is where second-order/metalanguage lived but
Peirce left it **unfinished** (search-summary,
[Gamma graph calculi, Synthese](https://link.springer.com/article/10.1007/s11229-017-1390-3);
[Bellucci–Pietarinen](https://philpapers.org/rec/SCHEEG-3)). **Crucially: Peirce
never gave a graphical *definition/abstraction with a discharge rule*** — the
exact gap the brief is filling. Modern reconstructions (Dau; Bellucci–
Pietarinen; Ma–Pietarinen on Gamma) formalise soundness of the existing rules
but do not add a comprehension/definition device.

**Sowa's conceptual graphs — the one EG-tradition device that DOES define.**
Search-summary ([Sowa & Way 1986; jfsowa.com/cg](http://www.jfsowa.com/cg/cgonto.htm)):
each type in the catalogue carries *"a definition… consisting of a
**lambda-abstraction**"*; graphs are manipulated by six canonical rules
(*"copy, join, iteration, restriction, simplification,"* detachment). Defined
types are unfolded/folded by **type expansion / type contraction** — expansion
splices the definition's λ-graph in place of the concept; contraction folds it
back. This is precisely the **"unfold = splice-copy of content at an atom"**
shape the brief *rejected* — the EG tradition's own definition mechanism is the
teleport-copy.

**Mapping (EG core).** R1 n/a for defs (no def mechanism). R2 **4** (cuts =
negation, lines = identity — the brief's own semantic anchors). R3 n/a. R4 **3**
(insertion/erasure = sound+complete for FOL). 
**Mapping (Sowa defined types).** R1 **2** (expansion = splice a copy — the
rejected move). R2 **3**. R3 **3** (λ-abstraction names the definitional
coordinates as formal parameters). R4 **2** (canonical-rule equivalence; no βη).

---

## 5. Term-graph rewriting & sharing (jungles; equational term graphs)

**What it is.** Terms drawn as DAGs so equal subterms are **shared**. *Jungles*
(Hoffmann–Plump) are *"acyclic hypergraphs that represent sets of terms… so
that equal subterms can be shared"* and give *"a compromise between term
rewriting and graph rewriting"* (search-summary,
[Jungle evaluation, Springer](https://link.springer.com/chapter/10.1007/3-540-50325-0_5)).
**Equational term graphs** (Ariola–Klop) add cycles = recursion/`letrec`:
*"an equational framework for term graph rewriting with cycles, where the notion
of homomorphism is phrased in terms of **bisimulation**… Equational Logic
induces a notion of **copying and substitution** on term graphs, or systems of
recursion equations… hidden or nameless nodes… can be used only once"*
(search-summary, [Ariola–Klop, Fundamenta Informaticae 1996](https://journals.sagepub.com/doi/abs/10.3233/FI-1996-263401)).

**How definitions unfold locally.** A definition = a **shared node** (or a
`μ`/`letrec` binding). Unfolding is a **local edge redirection**: point the
use-edge at a fresh copy of the body, or at the body directly (sharing).
Equality of two definitions is decided by **functional bisimulation**; the
bisimilarity class is a complete lattice, and orthogonal systems are confluent
even with copying and hidden nodes (search-summary, same source).

**Mapping.** R1 **3** (unfold = local redirection, not a distant materialisation
if kept shared). R2 **2** (a share-node has no *logical* reading — it is a data
optimisation). R3 **2**. R4 **4** (a real equational theory: bisimulation as
graph-α-equality + confluent rewriting = exactly the "α-iso free, βη derivable"
discharge the brief wants, done combinatorially).

---

## 6. Bigraphs (Milner)

**What it is.** A bigraph superposes two orthogonal structures on **one shared
node set**: a **place graph** (a forest — *nesting/locality*) and a **link
graph** (a hyper-graph — *connectivity*), which are *"otherwise independent."*
Primary-ish quotes (search-summary of
[Milner, UCAM-CL-TR-580](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-580.pdf)):
*"a node represents locality — we call this nesting structure its place graph…
ports connected by links… we call this linked structure, independent of
locality, its link graph. The place graph and the link graph share a node set,
but are otherwise independent."* Reaction rules rewrite bigraphs; there is a
spatial logic ([Conforti–Macedonio–Sassone](https://link.springer.com/chapter/10.1007/11523468_62)).

**Why it is here.** This is the **structural mirror of the spec's own
architecture**: the spec makes *cuts = regions (nesting)* and *wires =
connectivity (identity)* two orthogonal layers on one graph — exactly
place/link. A "definition content region" (place) with "argument wires" (link)
crossing it is the bigraphical decomposition, and it gives a **principled reason
the content is a region AND the arg wires are real links** (attacking the
body-node's "argument wires are missing" defect).

**Mapping.** R1 **2** (reaction is local but there is no substitution calculus
per se). R2 **3** (place/link both have clean meanings; not tuned to logic). R3
**2**. R4 **2** (bisimulation congruence from reaction rules; no logical
discharge). *Transferable as an architecture, not a proof theory.*

---

## 7. ZX-calculus / !-boxes (bang boxes) — a literal "membrane with content"

**What it is.** ZX is a complete graphical calculus with **local** rewrite rules
between diagrams denoting the same linear map. A **!-box** ("bang box") is a
marked region of a diagram denoting a **whole family** indexed by n ≥ 0.

**How the membrane and its content are drawn / rewritten LOCALLY.** Primary
quote (arXiv:1204.6695 abstract, fetched):
*"certain marked subgraphs, called !-boxes ('bang boxes'), on both sides of a
rule can be **copied any number of times or removed**"* — this expresses
*"infinite families of rewrite rules."* Instantiation is explicit: the paper
shows *"how pattern graphs and pattern rewrite rules can be **instantiated to
concrete string graphs and rewrite rules**."* Operationally the !-box has local
ops COPY/KILL/EXPAND/MERGE acting only on the marked region and the wires
crossing its boundary (search-summary,
[Kissinger !-Logic thesis](https://www.cs.ox.ac.uk/people/aleks.kissinger/papers/quick-thesis.pdf),
PDF not text-extractable — labelled unverified at primary source).

**Equational theory — the key part.** A !-box **rewrite rule is sound iff it is
sound for every concrete instantiation** (each n). So a rule *over families*
gets discharged by the underlying (finite) equational theory instantiated at
each arity — a genuine equational theory *for the family-carrying membrane
itself*. This is exactly the thing the brief says the rejected body-node lacked
("no equational theory for relational content").

**Mapping.** R1 **3** (COPY/EXPAND are local rewrites on the marked region +
its crossing wires — not a teleport; but expansion still replicates content). R2
**3** (membrane = "content that fans out to a family" — a *meaning*, matching
directions A/D; it is the content-visible membrane, not a black box). R3 **4**
(**best in survey**: a !-box literally *is* "the family is the concept," the
content indexed by arity with its boundary wires exposed). R4 **3** (soundness-
by-instantiation = real discharge over families; completeness is fragment-
dependent).

---

## 8. Deep inference / calculus of structures; subatomic logic

**What it is.** Inference rules apply **arbitrarily deep inside a formula**
(*"contrary to traditional proof systems where inference rules only deal with
the outermost structure"* — search-summary,
[CoS / Guglielmi](https://en.wikipedia.org/wiki/Calculus_of_structures)).
**Locality:** *"every contraction and cut instance can be **locally transformed
into their atomic variants** by a local procedure of polynomial size"* — a
property the sequent calculus lacks. **Atomic flows** are *"diagrams that forget
much of the syntactic structure… and only retain causal relations between
atoms"* (search-summary,
[Atomic Flows, arXiv:0709.1205](https://arxiv.org/pdf/0709.1205)). **Subatomic**
logic represents *"every rule as an instance of a single inference rule scheme"*
by looking inside atoms
([Subatomic Proof Systems, arXiv:1703.10258](https://arxiv.org/pdf/1703.10258)).

**Why it is here.** The brief mandates **primitive-only gestures** (each proof
step one small visible local move) and **no comprehension-specific machinery**.
Deep inference is the proof-theoretic embodiment of exactly that: **contraction
(= copying) reduced to atomic, local steps**, and a *uniform* rule scheme rather
than special-case rules. It licenses "substitution as a sequence of primitive
local moves" and the "one uniform mechanism" demand.

**Mapping.** R1 **4** (all rewriting is deep-and-local; copying = atomic
contraction). R2 **3** (atomic flows give a geometric trace with meaning). R3
**2**. R4 **3** (full propositional/predicate normalisation theory).

---

## 9. Geometry of Interaction as wire-mediated, substitution-FREE execution

**What it is.** GoI evaluates a λ-term by fixing its graph and **passing a token
along wires**; the answer is the path the token traces. No β-copy ever happens.
Primary quote (arXiv:1803.00427 abstract, fetched): the DGoIM is *"a machine
combining **token passing and graph rewriting**."* Search-summary: token-passing
GoI *"decomposes higher-order computation into local token actions… handle[s]
duplicated computation by repeating the same moves of a token on the **fixed
graph**"* ([DGoIM](https://arxiv.org/abs/1803.00427)).

**Why it is here.** This is the **purest realisation of "wire-mediated, no
teleport"**: a definition need never be copied at all — a token routes *through*
it, and repeated use = repeated traversal. If instantiation can be modelled as
routing rather than copying, R1's "graphical continuity, never a copy at a
distance" is satisfied maximally.

**Mapping.** R1 **4** (substitution-free; identity carried entirely by wire
traversal). R2 **2** (a token machine is an operational device, not a drawn
semantics *of definitions*). R3 **1**. R4 **2** (correctness = soundness wrt
evaluation, not an equational discharge calculus).

---

## 10. Definitions-as-extensions / definitional reflection (graphical?)

Schroeder-Heister's **definitional reflection** treats a definition as a set of
clauses with *dual* left/right rules (unfold on both sides), a principled
"definition = its introduction+elimination" story that avoids a
comprehension-specific axiom. **However**: I found **no graphical/diagrammatic
formulation** of it. Its transferable idea — a definition is discharged by
*symmetric* fold/unfold rules on both polarities — is strongly resonant with the
brief's "backward = flipped polarity, shared implementation," but this is a
**known-but-not-evaluated** thread (proof-theoretic, term-level only in the
sources found). Sources: standard references (Hallnäs; Schroeder-Heister),
**not fetched** — flagged unverified.

---

## Requirements matrix (mechanism × R1–R4)

| Mechanism | R1 local sub | R2 form←semantics | R3 family=concept | R4 discharge |
|---|---|---|---|---|
| 1. LL exponential boxes | 1 | 3 | 2 | 4 |
| 2. Interaction nets / sharing graphs | **4** | 3 | **4** | 3 |
| 3a. Functorial boxes (Melliès) | 2 | **4** | 2 | 3 |
| 3b. Hierarchical-hypergraph λ (Ghica–Zanasi) | 3 | **4** | 3 | 3 |
| 4a. Existential graphs (core) | n/a | **4** | n/a | 3 |
| 4b. Sowa CG defined types | 2 | 3 | 3 | 2 |
| 5. Equational term graphs (Ariola–Klop) | 3 | 2 | 2 | **4** |
| 6. Bigraphs (place/link) | 2 | 3 | 2 | 2 |
| 7. ZX !-boxes | 3 | 3 | **4** | 3 |
| 8. Deep inference / subatomic | **4** | 3 | 2 | 3 |
| 9. GoI token machine | **4** | 2 | 1 | 2 |

("Not checked" cells: none left blank except where a mechanism has no analogue
of the requirement — marked n/a, not skipped.)

---

## Most transferable ideas (shortlist, max 5)

1. **ZX !-box + soundness-by-instantiation** (§7). The specific move: draw the
   definition as a **content-visible membrane denoting an arity-indexed family**
   (directions A/D), and **discharge equations over it by instantiating at each
   concrete arity** and using the underlying finite theory. This is a
   ready-made, *equipped-with-an-equational-theory* version of the rejected
   body-node — content visible, family-is-the-concept, real discharge. Best
   answer to R3+R4 together.

2. **Sharing/fan node from interaction nets** (§2). The move: model a
   definition's use as a **fan/share node** so instantiation is a **local
   fan-interaction that slides along the argument wire**, never a distant copy
   (R1). Adopt the mechanism but **heed the bracket/croissant warning**: any
   level-bookkeeping nodes we add have no logical reading and are pure cost —
   design them out or justify them.

3. **Functorial/comonadic box** (§3a). The move: justify the membrane as a
   **functor box** (`!` = a "definition-holding" comonad), so its boundary
   crossing and open/close rules are **functoriality, not rendering** — the R2
   gold standard, and a principled reply to "the curve must *mean* something."

4. **Equational term graphs: definition = μ/letrec node, equality =
   bisimulation** (§5). The move: a defined relation is a **shared/`μ` node whose
   sole rule is local unfolding**; equality of two definitions is discharged by
   **functional bisimulation of their content graphs** — i.e. graph-α-equality
   for free via canonical form, exactly the brief's "α-iso free" requirement,
   plus confluent rewriting for the βη layer (R4).

5. **Bigraph place/link orthogonality** (§6). The move: treat the definition as
   a **place-graph region** (nesting = the content held apart from assertion,
   the "graphical λ") with **argument wires as link-graph edges crossing it** —
   giving a principled structural account of why content is a region *and* the
   arg wires are real, present links (fixing the body-node's "missing argument
   wires" defect). Architecture, not proof theory.

*(Deliberately combinable: 1+3 = a functorially-justified, family-denoting
membrane; 2+4 = local unfold with bisimulation discharge; 5 supplies the
region/link skeleton for all of them. Deep inference §8 is the meta-constraint:
whatever we pick, the user's "primitives only" law wants copying decomposed into
atomic local steps.)*

---

## Scope disclosure

**Evaluated (primary source or arXiv/publisher abstract checked):** LL
exponential boxes; interaction nets / sharing graphs; Melliès functorial boxes
(abstract only — PDF 403); Ghica–Zanasi hierarchical hypergraphs (abstract);
existential graphs core (SEP, direct quotes); ZX !-boxes / pattern graphs
(arXiv:1204.6695 abstract, direct quote); DGoIM token GoI (arXiv abstract,
direct quote); equational term graphs / jungles (abstracts); bigraphs (tech-
report abstract); deep inference / subatomic (abstracts).

**Primary quote NOT independently extractable (labelled unverified above):**
Kissinger !-Logic thesis PDF (binary); Melliès functorial-boxes PDF (403);
Bonchi–Gadducci–Kissinger–Sobocinski–Zanasi *String Diagram Rewrite Theory I*
PDF (binary) — its DPO-of-hypergraphs / **convexity** soundness result
(substitution as a **local double-pushout rewrite**, sound+complete for SMC
laws) is cited only from the search-engine snippet of
[arXiv:2012.01847](https://arxiv.org/pdf/2012.01847) and
[arXiv:1602.06771](https://arxiv.org/pdf/1602.06771); treat as unverified at
primary source. This DPO-with-interfaces framework is the rigorous backbone for
"substitution = local graph rewrite" and deserves a direct read before it is
relied on.

**Known but NOT evaluated:**
- Girard's *Geometry of Interaction* original operator-algebra papers (only the
  token-machine reading was checked).
- Danos–Regnier correctness criterion / "nouvelle syntaxe" box-free proof nets
  in primary form (only summarised).
- **Definitional reflection** (Schroeder-Heister, Hallnäs) — no graphical
  formulation found; term-level only.
- Dau's / Bellucci–Pietarinen's full formal Gamma reconstructions and any
  modern **second-order existential graph** proposals (Ma & Pietarinen on Gamma
  completeness) — cited via summary, not read in full.
- Hughes' / proof-net "combinatorial proofs" (a box-free canonical form for
  classical logic) — adjacent and relevant, not searched.
- Lamping/Gonthier–Abadi–Lévy GoI-for-optimal-reduction original papers (read
  only via the Asperti–Guerrini survey summary).
- Interaction-net *locality* stated from Lafont's own paper — quoted only from
  search summary (nLab pages 404'd during the session).
</content>
</invoke>
