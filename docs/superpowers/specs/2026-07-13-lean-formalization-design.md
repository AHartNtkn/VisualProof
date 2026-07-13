# VisualProof Lean Formalization — Design Specification

**Date:** 2026-07-13  
**Status:** approved architecture, written specification awaiting user review

## 1. Outcome

VisualProof will have a canonical Lean 4 formalization of:

1. intrinsically scoped untyped lambda terms and beta-eta conversion;
2. the combinatorial syntax and well-formedness of diagrams;
3. diagrams with ordered, possibly aliased boundaries;
4. classical second-order semantics over beta-eta classes of closed lambda terms;
5. all 25 serialized `ProofStep` forms accepted by the TypeScript kernel;
6. proof, theorem, citation, and theory soundness;
7. exact finite occurrence matching, with executable soundness and completeness theorems; and
8. a durable coverage boundary connecting the Lean rule inventory to TypeScript.

The formalization proves rule soundness, not general deductive completeness. Completeness is claimed only for the exact finite occurrence matcher against its declarative specification. Untyped beta-eta equality and fuel-bounded search retain explicit undecided or exhausted outcomes.

## 2. Controlling Semantics

The formalization implements the confirmed VisualProof semantics:

- Individuals are closed untyped lambda terms modulo beta-eta equivalence.
- A sheet asserts its contents.
- Items juxtaposed in one region form a conjunction.
- A cut negates the contents of its child region.
- A wire introduces one individual at its scope region. Descendants may refer to it.
- A bubble introduces one relation of its declared arity. Its descendants may apply it.
- A term node asserts that its output individual equals the beta-eta class of its lambda term after substituting its incident input individuals.
- A bound-relation atom applies its bubble's relation to its ordered argument wires.
- A named-relation reference applies the denotation assigned by a verified theory definition.
- A bubble or wire is represented compositionally by an existential binder. Universal readings arise from negation in enclosing cuts; quantifier force is not duplicated as stored syntax.
- Graphical layout, geometry, physics, interaction state, display names, and identifier spelling have no denotation.

Lean's `Prop` provides full, impredicative second-order quantification over relations of type `(Fin n → Individual) → Prop`.

## 3. Architectural Decision

The system uses the approved hybrid intrinsic/extrinsic architecture.

### 3.1 Intrinsic semantic core

The intrinsic representation makes scope and arity correct by construction. Its types contain no browser identifiers.

Conceptually:

```lean
inductive Term (bound : Nat) (free : Type)
  | bvar : Fin bound → Term bound free
  | port : free → Term bound free
  | lam  : Term (bound + 1) free → Term bound free
  | app  : Term bound free → Term bound free → Term bound free

abbrev RelCtx := List Nat

structure RelVar (ctx : RelCtx) (arity : Nat) where
  index : Fin ctx.length
  hasArity : ctx.get index = arity

mutual
  structure Region (outerWires : Nat) (relations : RelCtx) where
    localWires : Nat
    items : List (Item (outerWires + localWires) relations)

  inductive Item (wires : Nat) (relations : RelCtx)
    | equation : Fin wires → Term 0 (Fin wires) → Item wires relations
    | atom : RelVar relations n → (Fin n → Fin wires) → Item wires relations
    | named : NamedRel signature n → (Fin n → Fin wires) → Item wires relations
    | cut : Region wires relations → Item wires relations
    | bubble : (n : Nat) → Region wires (n :: relations) → Item wires relations
end
```

The final Lean definitions may improve notation and universe parameters but must preserve this responsibility model.

Consequences:

- de Bruijn indices make lambda binders well scoped;
- `RelVar` makes an atom's binder both in scope and arity-correct;
- `Fin wires` makes every term port and atom argument refer to an available line of identity;
- region-local wire binders make a wire accessible exactly to its descendants;
- sharing a wire variable represents a hyperedge;
- an unused local variable represents a bare wire; and
- malformed references do not inhabit the intrinsic type.

Lists provide finite conjunction syntax, not semantic order. Renaming and permutation theorems prove denotation invariant under reordering items and local variables.

Under the locked Lean 4.30 + Std surface, structural bijections use one
project-owned record:

```lean
structure FiniteEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y
```

It is the sole representation of wire and item-occurrence bijections. Identity,
inverse, composition, and block extension are proved from these fields; no
cardinality casts or alternate equivalence representation is used.

### 3.2 Concrete finite graphs

The concrete representation mirrors the normalized mathematical content of the
TypeScript kernel without copying its string-keyed partial-record shape. Region,
node, and wire identifiers are separate `Fin` types over stored counts, and their
tables are total functions. Missing identifiers are therefore rejected at the
serialization boundary and are unrepresentable in this layer.

Term nodes store a free-port count and a term whose free variables are
`Fin freePortCount`; endpoints still use an extrinsic `free index` port so invalid
port occurrences remain checkable. Bound atoms identify a concrete binder region.
Named references store a natural-number definition position and asserted arity so
resolution remains contextual. Wires are scoped hyperedges with lists of endpoint
occurrences; endpoint order is not semantic, and empty lists represent bare wires.

A separate `Concrete.WellFormed signature` proposition establishes:

- one rooted region tree;
- the designated root as the unique sheet and termination of every parent chain there;
- enclosing bubble binders for bound atoms;
- named-reference existence and arity agreement in the supplied signature;
- enclosing wire scopes;
- valid endpoint ports;
- no duplicate endpoint occurrence within a wire or across wires; and
- total coverage of every required node port.

One structured checker decides exactly this proposition and returns either a named
`WFError` or the proof. Both directions are proved:

```lean
theorem checkWellFormed_sound :
  checkWellFormed signature d = .ok h → d.WellFormed signature

theorem checkWellFormed_complete :
  d.WellFormed signature → ∃ h, checkWellFormed signature d = .ok h
```

Parent ancestry is backed by a bounded path or decreasing-rank certificate, so no
consumer follows parent links under an unencoded acyclicity assumption. Checked
consumers accept an explicit proof or `CheckedDiagram signature`; no Boolean,
normalizing constructor, or constructor-provenance convention is a second
validation authority.

Concrete graphs retain explicit ports, incidence, named-reference identities, and identifier-independent finite structure because matching depends on them.

### 3.3 Checked elaboration

`Concrete.elaborate` consumes a concrete graph plus a well-formedness proof and produces an intrinsic diagram. It:

1. traverses the proved region tree;
2. introduces every wire at its scope, including endpoint-less bare wires;
3. uses exact incidence to replace each output, free, and argument port by its
   unique lexical wire variable;
4. uses binder-enclosure evidence to convert concrete bubble identity to a typed
   `RelVar`;
5. resolves named relation positions to `NamedRel`; and
6. erases all concrete identifiers and nonsemantic collection orders.

Concrete graphs have no independent semantic interpreter. Their denotation is
defined only by checked elaboration into the core:

```lean
def Concrete.denote
  (model) (d : ConcreteDiagram) (h : d.WellFormed) : Prop :=
  Core.denote model (d.elaborate h)
```

Required theorems:

```lean
theorem elaborate_proof_irrelevant
  (h₁ h₂ : d.WellFormed) :
  d.elaborate h₁ = d.elaborate h₂

theorem elaborate_iso
  (hiso : Concrete.Isomorphic d₁ d₂) :
  Core.Isomorphic (d₁.elaborate hiso.leftWF) (d₂.elaborate hiso.rightWF)

theorem iso_denotation
  (hiso : Core.Isomorphic d₁ d₂) :
  Core.denote model d₁ ↔ Core.denote model d₂
```

`Concrete.Isomorphic` contains bijections on the three concrete identifier sorts
that preserve root, region ownership and kinds, bubble arities, positional term
shape, binders, wire scope, endpoint occurrences modulo endpoint order, and any
ordered boundary pins. Canonical strings and hashes are not definitions of this
relation.

The intrinsic core is the semantic authority. The concrete layer is a checked finite presentation, not a second logic.

## 4. Lambda Calculus

### 4.1 Conversion relation

Lean defines beta and eta one-step reductions on intrinsically scoped terms, their compatible closure, and beta-eta equivalence as the reflexive-symmetric-transitive closure. It proves equivalence and congruence under lambda, application, renaming, and capture-avoiding substitution.

Eta contraction includes its standard nonoccurrence condition. Substitution and lifting are defined structurally and tested by the beta law, identity substitutions, and composition laws.

### 4.2 Individuals

```lean
abbrev ClosedTerm := Term 0 Empty
def Individual := Quotient betaEtaSetoid
```

Term-node evaluation substitutes representatives of input individuals into an open term and returns the resulting quotient class. Well-definedness proofs show that the result is independent of chosen representatives.

The abstract evaluator interface is a lawful beta-eta-respecting algebra for free
term substitution, not an arbitrary function:

```lean
structure LambdaModel where
  Carrier : Type
  eval : {n : Nat} → Term 0 (Fin n) → (Fin n → Carrier) → Carrier
  eval_port : eval (.port i) env = env i
  eval_bindFree :
    eval (term.bindFree substitution) env =
      eval term (fun i => eval (substitution i) env)
  betaEta_sound : BetaEta a b → eval a env = eval b env
```

Arbitrary free-port naturality is derived from `eval_port` and `eval_bindFree`;
it is not a redundant structure field. This law is the authority for wire
renaming and aliasing, while `eval_bindFree` is also the authority for later
fusion and fission. The canonical quotient evaluator proves the structure laws
from representative independence and substitution associativity.

### 4.3 Certificates and bounded search

The formal relation is not defined by the search algorithm. A conversion certificate is a pair of finite reduction paths to a common term. The checker is executable and has the theorem:

```lean
theorem checkCertificate_sound :
  checkCertificate left right cert = true → BetaEta left right
```

Fuel-bounded normalization returns `equal`, `differentNormalForms`, or `exhausted`. No theorem converts `exhausted` into inequality, and no global completeness theorem is stated.

## 5. Open Diagrams and Boundaries

An open diagram distinguishes external boundary-wire classes from wires locally quantified at its root.

```lean
structure OpenDiagram (arity : Nat) where
  externalClasses : Nat
  boundary : Fin arity → Fin externalClasses
  boundary_surjective : Function.Surjective boundary
  body : Region externalClasses []
```

Repeated values of `boundary` represent repeated boundary incidences, such as a binary relation body exposing the same line in both positions. Root-scoped wires absent from the TypeScript boundary become local root wires rather than external classes.

For arguments `args : Fin arity → Individual`, open-diagram denotation existentially chooses one value for each external class, requires it to agree with every boundary position, then denotes the body. This makes aliasing semantic rather than representational.

Splicing is capture-avoiding substitution of boundary classes by host wire variables. The central substitution theorem is:

```lean
theorem denote_splice :
  denote (splice host site pattern arguments) ↔
  denoteContext host site (denoteOpen pattern arguments)
```

A selection at a region contains whole direct child subtrees, direct nodes, and
explicitly selected wires scoped at that region whose endpoints are selected.
Selection closure derives all descendant regions/nodes, internally owned wires,
and touching wires. Extraction turns touching wires into root-scoped boundary
stubs in a fixed incidence order and turns externally enclosing binders into an
outermost-first chain of stub bubbles with aligned binder attachments. Repeated
boundary incidences preserve wire alias classes.

Removal drops the selected content while retaining outside endpoints. Splicing
validates attachment enclosure and binder kind, arity, and enclosure before
performing the boundary pushout; repeated incidences of one pattern wire identify
their host attachments. The semantic theorem is stated over the intrinsic
conjunction frame obtained by elaboration, rather than an untyped placeholder
`site`. Extracting a lawful selection, removing it, and splicing the extraction
back reconstructs the original host up to structural isomorphism. These theorems
support iteration, comprehension, relation definitions, and theorem citation.

## 6. Semantic Context and Polarity

A diagram context is a diagram with one typed hole and a recorded cut depth. Filling preserves scope and boundaries.

Lean proves by induction on the context:

```lean
theorem context_mono
  (even : ctx.cutDepth % 2 = 0)
  (h : denote a → denote b) :
  denote (ctx.fill a) → denote (ctx.fill b)

theorem context_anti
  (odd : ctx.cutDepth % 2 = 1)
  (h : denote a → denote b) :
  denote (ctx.fill b) → denote (ctx.fill a)
```

Equivalence is substitutive at every depth. These are metatheorems, not user-facing proof steps. They are the sole authority for polarity gates, backward reasoning, and theorem citation.

## 7. Named Relations and Theories

Named relation definitions are conservative, ordered definitions. Each definition may refer only to earlier definitions. This independently selects the append-only dependency-DAG semantics stated by the project and rules out recursive or cyclic notation with no determined denotation.

The Lean theory context stores each name, arity, body, and proof that references resolve to earlier entries. Its interpretation is defined by structural recursion over that order.

The TypeScript verifier currently checks reference existence and arity but not dependency acyclicity. Integration must migrate it to the same ordered-DAG rule; accepting cyclic definitions would leave fold/unfold without a guaranteed interpretation and therefore cannot remain as a competing path.

Relation fold and unfold are then definitional equivalences, proved from the definition environment and `denote_splice`.

## 8. Rule Surface and Soundness

Lean defines one `StepTag` constructor for each serialized TypeScript `ProofStep` tag. Payloads refer to concrete finite indices, patterns, certificates, or verified theory entries as appropriate.

`applyStep` is executable and returns `Except StepError ConcreteDiagram`. Every successful result is well formed. Its semantic theorem is polarity-directed:

```lean
theorem applyStep_sound
  (ok : applyStep ctx orientation d step = .ok d') :
  DirectedEntailment orientation step d d'
```

`DirectedEntailment` expands to the implication or equivalence required by the rule's direction and the containing context's polarity. It never hides the denotation behind structural equality.

The complete coverage surface is:

| TypeScript tag | Semantic basis | Required result |
|---|---|---|
| `openTermSpawn` | negative-context insertion | directed soundness |
| `relationSpawn` | negative-context insertion of a defined atom | directed soundness |
| `boundRelationSpawn` | negative-context insertion of a bound atom | directed soundness |
| `wireJoin` | identity strengthening with scoped quantifier movement | directed soundness |
| `erasure` | positive-context weakening | directed soundness |
| `wireSever` | existential weakening of identity | directed soundness |
| `iteration` | conjunction contraction and boundary-preserving copy | equivalence |
| `deiteration` | inverse justified by an exact occurrence | equivalence |
| `doubleCutIntro` | double-negation introduction | equivalence in classical logic |
| `doubleCutElim` | double-negation elimination | equivalence in classical logic |
| `conversion` | beta-eta quotient equality | equivalence |
| `congruenceJoin` | functionality of term interpretation | equivalence |
| `anchoredWireSplit` | duplication of a closed equality witness | equivalence |
| `anchoredWireContract` | contraction of beta-eta-equal closed witnesses | equivalence |
| `headStrip` | rigid-head decomposition under beta-eta confluence | entailed conjunct addition |
| `closedTermIntro` | inhabited individual domain and reflexive equation | equivalence |
| `fusion` | one-point existential substitution | equivalence |
| `fission` | inverse one-point expansion | equivalence |
| `comprehensionInstantiate` | full second-order instantiation | directed soundness |
| `comprehensionAbstract` | second-order existential generalization | directed soundness |
| `theorem` | contextual application of a verified implication | directed soundness |
| `vacuousIntro` | quantification of an absent relation variable | equivalence |
| `vacuousElim` | elimination of an unused relation binder | equivalence |
| `relUnfold` | named-relation definitional equality | equivalence |
| `relFold` | inverse named-relation definitional equality | equivalence |

Rule proofs factor through shared lemmas for weakening, contraction, alpha-renaming, substitution, one-point quantification, double negation, beta-eta congruence, relation quantification, and context polarity. No rule is proved by replaying the TypeScript implementation or assuming its desired conclusion.

### 8.1 Head-strip obligation

Head stripping receives a dedicated lambda-calculus theorem: beta-eta-equivalent head-normal forms with equal binder counts, equal rigid heads, and equal spine lengths have pairwise beta-eta-equivalent corresponding arguments after prefix closure. The theorem is derived from confluence and preservation of a rigid head; it is not accepted as an informal comment.

If this theorem fails under the exact implemented side conditions, implementation stops and the rule or its gate is repaired. The formalization must not postulate injectivity.

## 9. Proof and Theory Soundness

`Proof`, `Action`, and `Theorem` mirror the logical structure rather than UI history. Allocation reservations and placements remain outside the semantic object.

Lean proves:

```lean
theorem replay_sound :
  replay ctx start steps = .ok finish →
  denote start → denote finish

theorem backward_replay_sound :
  replay ctx goal backSteps .backward = .ok reduced →
  denote reduced → denote goal

theorem checkedTheorem_sound :
  checkTheorem ctx theorem = .ok verified →
  denoteOpen verified.lhs ⟶ denoteOpen verified.rhs

theorem verifiedTheory_sound :
  verifyTheory theory = .ok verified →
  ∀ theorem ∈ verified, SemanticallyValid theorem
```

Meet-in-the-middle composition uses isomorphism invariance and transitivity. Boundary survival is represented in the theorem type or checker result, so identifier destruction and resurrection cannot certify unrelated statements.

## 10. Exact Occurrence Matching

### 10.1 Declarative specification

`Occurrence pattern host site` contains finite maps for regions, nodes, and wires plus proofs of:

- the pattern root maps to the selected host region;
- region, node, and wire maps preserve kinds and are injective where structural identity requires it;
- child-region parentage and bubble arities are preserved;
- nested pattern regions correspond exactly to their host images;
- effective-root items use subset semantics;
- term nodes match by name-blind de Bruijn shape in exact mode;
- relation atoms preserve binder maps and argument positions;
- named references preserve definition identity and arity;
- wire scope, endpoint incidence, and port positions commute with the maps;
- internal wires remain internal;
- ordered boundary incidences map to the reported attachments, including intrinsic aliases;
- supplied open binders map to the exact specified host binders; and
- no mapped item escapes a binder or region scope.

This relation is independent of the search algorithm.

### 10.2 Executable exact matcher

The first verified implementation enumerates finite candidate sites and finite injective assignments without heuristic pruning. Wires with endpoints are determined and checked by port incidence; bare wires are enumerated canonically. Deduplication affects output multiplicity only, not existence.

Required theorems:

```lean
theorem exactMatcher_sound :
  occurrence ∈ exactMatcher pattern host options →
  Occurrence pattern host options occurrence

theorem exactMatcher_complete :
  Occurrence pattern host options occurrence →
  ∃ found ∈ exactMatcher pattern host options,
    Occurrence.equivalent found occurrence

theorem exactMatcher_decides :
  (exactMatcher pattern host options).isEmpty ↔
  ¬ ∃ occurrence, Occurrence pattern host options occurrence
```

An optimized refinement/symmetry-breaking matcher may replace the exhaustive reference only after proving extensional equivalence. A fallback that exhaustively enumerates unresolved permutations is mandatory unless orbit equivalence itself is proved.

### 10.3 Beta-eta and exploration boundaries

The beta-eta matcher accepts only certificate-checked node matches, so returned occurrences remain sound. Its result records undecided comparisons and optional exploration exhaustion.

Completeness may be stated only conditionally:

```lean
theorem betaEtaMatcher_complete_of_decided
  (allRelevantPairsDecided : ...)
  (searchComplete : result.status = .complete) : ...
```

Neither condition may be hidden inside a vacuous hypothesis or inferred from absence of a match.

## 11. TypeScript Correspondence

Lean owns the canonical list of step tags and emits a machine-readable inventory. A repository check parses the discriminants of TypeScript's `ProofStep` union and requires exact set equality with the Lean inventory.

The check proves coverage of the public rule surface; it does not claim to prove TypeScript operational equivalence. Differential fixtures compare TypeScript elaboration, exact matching, and representative rule applications with Lean's executable reference on serialized finite examples. Any mismatch is a failure to investigate, never an accepted compatibility mode.

Where the formalization exposes an unsound or under-specified TypeScript gate, the TypeScript path is repaired or removed in the same goal. No adapter preserves an accepted-but-uninterpretable behavior.

## 12. Module Layout

The Lean package lives at repository root so the oracle is exactly `lake build`:

```text
lean-toolchain
lakefile.toml
VisualProof.lean
VisualProof/
  Lambda/
    Syntax.lean
    Rename.lean
    Substitute.lean
    Reduction.lean
    Confluence.lean
    Quotient.lean
    Certificate.lean
  Diagram/
    Core.lean
    Boundary.lean
    Rename.lean
    Semantics.lean
    Context.lean
    Isomorphism.lean
    Concrete.lean
    Elaborate.lean
    Subgraph.lean
  Theory/
    Signature.lean
    Definition.lean
    Semantics.lean
  Rule/
    Step.lean
    Structural.lean
    Equational.lean
    Comprehension.lean
    Named.lean
    Soundness.lean
  Proof/
    Replay.lean
    Theorem.lean
    Theory.lean
  Matcher/
    Specification.lean
    Exact.lean
    BetaEta.lean
  Correspondence/
    StepTags.lean
  Audit.lean
```

Modules may be split further when proof size demands it, but responsibilities may not be recombined into implementation-shaped monoliths.

The package uses Lean 4.30.0 and `Std` only. It introduces no network-fetched dependency. Adding a dependency later requires evidence that it reduces trusted or duplicated machinery without changing the selected semantics.

## 13. Errors and Failure States

- Concrete elaboration returns explicit errors for every failed well-formedness obligation.
- Rule application returns a typed error identifying the failed side condition.
- Certificate checking distinguishes malformed paths from valid nonjoining paths.
- Exact matching is total and finite.
- Bounded beta-eta matching distinguishes `noMatch`, `undecided`, and `exhausted`.
- Theory verification rejects unresolved, arity-mismatched, forward, recursive, and cyclic named references.
- No error path returns a success-shaped fallback diagram or theorem.

## 14. Validation and Completion Evidence

Lean proof development is theorem-driven, not test-driven. A mathematical
obligation is first stated at its owning module; while developing the proof, the
statement may temporarily use `sorry` so Lean can validate that the proposition is
well-formed. The completed task replaces every such admission with a checked proof.
Initial package setup is validated by compilation, not by manufacturing an import
failure. Separate Lean test modules must not duplicate propositions already owned
by named theorems.

The authoritative checks are:

1. `lake build` from repository root.
2. A repository scan rejecting `sorry`, `admit`, `decreasing_by sorry`, and project `axiom` declarations.
3. `#print axioms` auditing the public soundness, theory, and matcher theorems.
4. An explicit allowlist documenting Lean's classical and quotient foundations: `Classical.choice`, `propext`, and `Quot.sound` when they actually occur. No custom axiom is permitted.
5. Exact set equality between Lean `StepTag` names and TypeScript `ProofStep` discriminants.
6. Named theorems in their owning modules covering well-formedness rejection, boundary aliasing, scope, every rule family, matcher positive/negative cases, open binders, and bare wires; executable checks are retained only for decidable computation or cross-language integration not already expressed by those theorems.
7. Differential Lean/TypeScript fixtures for the concrete correspondence boundary.
8. `npm test` and `npm run typecheck` after integration.

Completion requires a coverage table mapping each of the 25 TypeScript tags to:

- its Lean constructor;
- executable applier or checker;
- semantic soundness theorem;
- required shared metatheorems; and
- validation command.

Passing builds or executable checks without these theorems is insufficient. A theorem about well-formedness or structural round trips cannot stand in for semantic validity.

## 15. Implementation Order

Implementation proceeds in dependency order:

1. package scaffold and intrinsic lambda calculus;
2. intrinsic diagram syntax, boundaries, and semantics;
3. context polarity, renaming, substitution, and isomorphism;
4. concrete graphs, well-formedness, and elaboration;
5. named-definition DAG semantics;
6. structural and equational rule soundness;
7. comprehension, theorem citation, and proof/theory soundness;
8. exact matcher specification, executable implementation, and proofs;
9. beta-eta conditional matcher results;
10. TypeScript inventory, verifier migration, and differential validation; and
11. full axiom, placeholder, coverage, Lean, and TypeScript audit.

Each stage must build and expose theorem-bearing behavior. Temporary scaffolding may not become a second semantic path.

## 16. Non-Goals

- Proving general completeness of VisualProof's deductive calculus.
- Deciding untyped beta-eta equivalence.
- Formalizing rendering, physics, UI interaction, animation, or layout.
- Verifying JavaScript, the browser runtime, or the TypeScript compiler.
- Preserving cyclic relation definitions or any other accepted state lacking the selected semantics.
- Treating canonical source labels, fingerprints, snapshots, or generated paperwork as logical proof.
