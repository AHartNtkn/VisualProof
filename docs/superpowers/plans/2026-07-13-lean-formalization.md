# VisualProof Lean Formalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a root-level Lean 4 package that formally defines VisualProof diagrams and semantics, proves all 25 serialized proof-step forms sound, proves the exact occurrence matcher sound and complete, and keeps TypeScript coverage synchronized.

**Architecture:** Use an intrinsically scoped semantic core and a finite extrinsic graph layer. Checked elaboration erases concrete identifiers into the core; all denotation flows through that elaboration. Rules execute on finite concrete graphs and are proved sound through the intrinsic semantics. Matching is specified independently as a finite occurrence embedding and decided by an exhaustive verified reference matcher.

**Tech Stack:** Lean 4.30.0, Lake 5, Lean `Std`, TypeScript 5.5+, Node 20+, Vitest 2.

## Global Constraints

- The Lean package is rooted at `lean-toolchain`, `lakefile.toml`, `VisualProof.lean`, and `VisualProof/` in the repository root.
- Use Lean 4.30.0 and `Std` only; add no network-fetched Lean dependency.
- Lean is the canonical mathematical authority. Concrete and TypeScript layers may not define competing semantics.
- Cover exactly the 25 discriminants in `src/kernel/proof/step.ts`.
- Prove semantic validity, not only well-formedness preservation, replay equality, or round trips.
- Do not claim general deductive completeness or decidability of untyped beta-eta equivalence.
- Exact matcher completeness applies only to the declarative finite exact-occurrence relation.
- Use no `sorry`, `admit`, `decreasing_by sorry`, or project `axiom` declarations.
- Acknowledge only foundational dependencies actually reported by `#print axioms`; the intended allowlist is `Classical.choice`, `propext`, and `Quot.sound`.
- Repair or remove any TypeScript path that accepts a state without the selected semantics; do not add compatibility aliases or fallbacks.
- Preserve rendering, physics, UI, and unrelated user work.
- Develop Lean obligations theorem-first: state each named theorem before proving it; a local transient `sorry` may validate the statement, but no `sorry` or other admission may enter a completed task or commit.
- Validate initial package setup by compilation; do not manufacture a failing import or synthetic RED test.
- Do not create separate Lean test modules for propositions already expressed by definitions and named theorems. Retain executable checks only for decidable computation, elaboration/API boundaries, or cross-language integration not already proved in Lean.

## Locked File Map

### Root package and audit

- `lean-toolchain`: pins `leanprover/lean4:v4.30.0`.
- `lakefile.toml`: defines library `VisualProof` and executables `visualproof_step_tags` and `visualproof_match_fixtures`.
- `VisualProof.lean`: imports the supported public surface.
- `VisualProof/Audit.lean`: prints axioms for public completion theorems.

### Lambda calculus

- `VisualProof/Lambda/Syntax.lean`: intrinsically scoped terms and free-variable maps.
- `VisualProof/Lambda/Rename.lean`: bound and free renaming.
- `VisualProof/Lambda/Substitute.lean`: capture-avoiding substitution and laws.
- `VisualProof/Lambda/Reduction.lean`: beta/eta steps, compatible closure, equivalence, confluence, and rigid-head decomposition.
- `VisualProof/Lambda/Quotient.lean`: beta-eta quotient and canonical lambda model.
- `VisualProof/Lambda/Certificate.lean`: executable reduction-path certificate checking.

### Diagrams and theories

- `VisualProof/Diagram/Core.lean`: intrinsic regions, items, relation contexts, and named signatures.
- `VisualProof/Diagram/Boundary.lean`: open diagrams, ordered aliases, and boundary assignments.
- `VisualProof/Diagram/Rename.lean`: wire/relation renaming and substitution.
- `VisualProof/Diagram/Semantics.lean`: the sole diagram denotation.
- `VisualProof/Diagram/Context.lean`: typed holes, polarity, monotonicity, and antitonicity.
- `VisualProof/Diagram/Isomorphism.lean`: item/wire renaming and denotation invariance.
- `VisualProof/Diagram/Concrete.lean`: finite regions, nodes, wires, endpoints, and well-formedness.
- `VisualProof/Diagram/Elaborate.lean`: checked concrete-to-core elaboration.
- `VisualProof/Diagram/Subgraph.lean`: selections, extraction, removal, splicing, and their semantic laws.
- `VisualProof/Theory/Signature.lean`: typed named-relation references.
- `VisualProof/Theory/Definition.lean`: ordered acyclic definitions.
- `VisualProof/Theory/Semantics.lean`: recursively interpreted verified theories.

### Rules and proofs

- `VisualProof/Rule/Step.lean`: 25-tag `StepTag`, payloads, orientation, errors, and dispatcher.
- `VisualProof/Rule/Structural.lean`: spawn, wire, erasure, iteration, double-cut, and vacuity rules.
- `VisualProof/Rule/Equational.lean`: conversion, congruence, anchored wires, head strip, closed introduction, fusion, and fission.
- `VisualProof/Rule/Comprehension.lean`: abstraction, instantiation, and diagonal boundaries.
- `VisualProof/Rule/Named.lean`: fold, unfold, and theorem citation.
- `VisualProof/Rule/Soundness.lean`: the global successful-application soundness theorem.
- `VisualProof/Proof/Replay.lean`: actions and forward/backward replay.
- `VisualProof/Proof/Theorem.lean`: theorem checking and citation validity.
- `VisualProof/Proof/Theory.lean`: complete theory verification soundness.

### Matcher and correspondence

- `VisualProof/Matcher/Specification.lean`: declarative exact occurrence embeddings.
- `VisualProof/Matcher/Exact.lean`: exhaustive executable exact matcher and two-direction proof.
- `VisualProof/Matcher/BetaEta.lean`: certificate-backed tri-state matching and conditional completeness.
- `VisualProof/Correspondence/StepTags.lean`: canonical step-tag inventory.
- `VisualProof/Correspondence/StepTagsMain.lean`: JSON-line tag emitter.
- `VisualProof/Correspondence/MatchFixturesMain.lean`: deterministic matcher fixture emitter.
- `scripts/check-lean-step-tags.mjs`: exact Lean/TypeScript tag-set check.
- `scripts/check-formalization.mjs`: build, placeholder, axiom, correspondence, and fixture audit.
- `tests/kernel/formal/correspondence.test.ts`: TypeScript differential checks.
- `package.json`: exposes `formal:check` and includes it in the full formal oracle.
- `src/kernel/proof/store.ts`: enforces ordered acyclic relation definitions if the formal audit confirms the current verifier gap.
- `tests/kernel/proof/store.test.ts`: rejects forward, self, and cyclic relation references.

---

### Task 1: Root package and intrinsically scoped lambda syntax

**Files:**
- Create: `lean-toolchain`
- Create: `lakefile.toml`
- Create: `VisualProof.lean`
- Create: `VisualProof/Lambda/Syntax.lean`
- Create: `VisualProof/Lambda/Rename.lean`
- Create: `VisualProof/Lambda/Substitute.lean`

**Interfaces:**
- Consumes: no prior Lean code.
- Produces: `Lambda.Term`, `Term.mapFree`, `Term.renameBound`, `Term.substBound`, `Term.bindFree`, `Term.lift`, and substitution/renaming laws used by every later task.

- [ ] **Step 1: Pin the toolchain and create the package scaffold**

Create `lean-toolchain` with exactly:

```text
leanprover/lean4:v4.30.0
```

Create `lakefile.toml` with:

```toml
name = "visualproof"
version = "0.1.0"
defaultTargets = ["VisualProof"]

[[lean_lib]]
name = "VisualProof"
```

- [ ] **Step 2: Implement the intrinsic term grammar**

Create `VisualProof/Lambda/Syntax.lean` under namespace `VisualProof.Lambda` with this public type:

```lean
inductive Term (bound : Nat) (free : Type u) : Type u
  | bvar : Fin bound → Term bound free
  | port : free → Term bound free
  | lam : Term (bound + 1) free → Term bound free
  | app : Term bound free → Term bound free → Term bound free
  deriving DecidableEq, Repr

abbrev ClosedTerm := Term 0 Empty
```

Define `mapFree`, `renameBound`, and `freeSupport` by structural recursion. `freeSupport` takes `[DecidableEq α]` and preserves first occurrence.

- [ ] **Step 3: Implement capture-avoiding renaming and substitution**

Create `Rename.lean` and `Substitute.lean` with these exact public signatures:

```lean
def Term.lift : Term n α → Term (n + 1) α
def Term.renameBound (ρ : Fin n → Fin m) : Term n α → Term m α
def Term.traverseBound [Applicative F]
  (σ : Fin n → F (Term m α)) : Term n α → F (Term m α)
def Term.substBound (σ : Fin n → Term m α) : Term n α → Term m α
def Term.substBoundOption
  (σ : Fin n → Option (Term m α)) : Term n α → Option (Term m α)
def Term.bindFree (σ : α → Term n β) : Term n α → Term n β

theorem Term.mapFree_id (t : Term n α) : t.mapFree id = t
theorem Term.mapFree_comp (f : α → β) (g : β → γ) (t : Term n α) :
  (t.mapFree f).mapFree g = t.mapFree (g ∘ f)
theorem Term.substBound_id (t : Term n α) :
  t.substBound Term.bvar = t
theorem Term.bindFree_id (t : Term n α) :
  t.bindFree Term.port = t
theorem Term.bindFree_assoc
  (t : Term n α) (f : α → Term n β) (g : β → Term n γ) :
  (t.bindFree f).bindFree g = t.bindFree (fun x => (f x).bindFree g)
```

State each theorem at its owning module before proving it. A transient local `sorry`
may be used only to confirm that Lean accepts the statement. Prove each theorem by
induction on `t`; the lambda case uses the lifted substitution induced by
`Fin.cases`. Remove every admission before verification or commit.

Export the complete algebra consumed by reduction and quotient semantics from the
owning modules rather than rebuilding it privately downstream:

```lean
theorem Term.renameBound_id
theorem Term.renameBound_comp
theorem Term.lift_renameBound
theorem Term.renameBound_substBound
theorem Term.substBound_renameBound
theorem Term.renameBound_substBoundOption
theorem Term.substBoundOption_renameBound
theorem Term.substBound_comp
theorem Term.lift_substBound
theorem Term.renameBound_bindFree
```

The exact dependent arguments must express composition/naturality across differing
bound scopes. Add the narrow free-binding/substitution interchange lemma required by
the quotient construction if it is not derivable from these statements and
`bindFree_assoc`; keep that law in `Substitute.lean`, not in a reduction consumer.
`substBound` and `substBoundOption` must be instantiations of the single
`traverseBound` recursion; the reduction module may not own a second recursive
substitution engine for eta unlift.
The two Option naturality theorems must expose both directions needed by eta
provenance: mapping a renaming over a successful partial substitution, and applying
partial substitution after a source renaming.

- [ ] **Step 4: Make the public import compile**

Create `VisualProof.lean` importing the three lambda modules. Run:

`lake build`

Expected: PASS with target `VisualProof` built.

- [ ] **Step 5: Commit the lambda syntax slice**

```bash
git add lean-toolchain lakefile.toml VisualProof.lean VisualProof/Lambda
git commit -m "feat(formal): add intrinsically scoped lambda syntax"
```

### Task 2: Beta-eta equivalence, quotient individuals, and certificates

**Files:**
- Create: `VisualProof/Lambda/Reduction.lean`
- Create: `VisualProof/Lambda/Quotient.lean`
- Create: `VisualProof/Lambda/Certificate.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `Term`, lifting, renaming, and substitution from Task 1.
- Produces: `OneStep`, `BetaEta`, `Individual`, `LambdaModel`, `canonicalModel`, `ReductionPath`, `checkCertificate`, `checkCertificate_sound`, confluence, and `rigidHead_args`.

- [ ] **Step 1: State the beta-eta and certificate obligations**

State named theorems in `Reduction.lean` and `Certificate.lean` before proving
them. The certificate module includes named computation theorems using:

```lean
def idTerm : ClosedTerm := Term.lam (Term.bvar 0)
def constId : ClosedTerm := Term.app (Term.lam (Term.bvar 0)) idTerm

theorem constId_beta : BetaEta constId idTerm := by
  exact BetaEta.step (OneStep.beta rfl)

theorem validCertificate_accepts : checkCertificate constId idTerm
    { left := [{ path := [], kind := .beta }], right := [] } = true := by
  rfl
```

Also state a named theorem that a certificate whose first path segment is invalid
returns `false`. A transient `sorry` may be used to validate these statements, but
must be removed before the task build and commit.

- [ ] **Step 2: Define reduction and equivalence independently of search**

In `Reduction.lean`, define compatible beta and eta contraction:

```lean
inductive OneStep : Term n α → Term n α → Prop
  | beta : body.substBound (Fin.cases arg Term.bvar) = out →
      OneStep (Term.app (Term.lam body) arg) out
  | eta : etaContract body = some fn → OneStep (Term.lam body) fn
  | lam : OneStep a b → OneStep (Term.lam a) (Term.lam b)
  | appFn : OneStep a b → OneStep (Term.app a x) (Term.app b x)
  | appArg : OneStep a b → OneStep (Term.app x a) (Term.app x b)

inductive BetaEta : Term n α → Term n α → Prop
  | refl : BetaEta a a
  | step : OneStep a b → BetaEta a b
  | symm : BetaEta a b → BetaEta b a
  | trans : BetaEta a b → BetaEta b c → BetaEta a c
```

Prove `BetaEta` is an equivalence and a congruence under `lam`, `app`, renaming, and substitution. Define parallel reduction and prove the diamond property; derive Church-Rosser for `BetaEta`.

- [ ] **Step 3: Prove the rigid-head theorem required by head stripping**

Define `Head`, `HeadSpine`, `headSpine`, and prefix closure. Prove:

```lean
theorem rigidHead_args
  (ha : headSpine a = some sa)
  (hb : headSpine b = some sb)
  (heq : BetaEta a b)
  (hbinders : sa.binders = sb.binders)
  (hhead : sa.head.Corresponds sb.head)
  (hlen : sa.args.length = sb.args.length) :
  ∀ i (hi : i < sa.args.length),
    BetaEta (prefixClose sa.binders (sa.args.get ⟨i, hi⟩))
      (prefixClose sb.binders (sb.args.get ⟨i, hlen ▸ hi⟩))
```

The proof must use Church-Rosser and preservation of a rigid head under reduction. Do not introduce injectivity as an axiom.

- [ ] **Step 4: Build the quotient individual domain and canonical model**

In `Quotient.lean`, define:

```lean
def betaEtaSetoid : Setoid ClosedTerm where
  r := BetaEta
  iseqv := betaEta_equivalence

def Individual := Quotient betaEtaSetoid

structure LambdaModel where
  Carrier : Type
  eval : {n : Nat} → Term 0 (Fin n) → (Fin n → Carrier) → Carrier
  eval_port : ∀ {n} (i : Fin n) (env : Fin n → Carrier),
    eval (.port i) env = env i
  eval_bindFree : ∀ {n m} (term : Term 0 (Fin n))
      (substitution : Fin n → Term 0 (Fin m))
      (env : Fin m → Carrier),
    eval (term.bindFree substitution) env =
      eval term (fun i => eval (substitution i) env)
  betaEta_sound : ∀ {n} {a b : Term 0 (Fin n)} {env : Fin n → Carrier},
    BetaEta a b → eval a env = eval b env

def canonicalModel : LambdaModel
```

Implement `canonicalModel.eval` by finite quotient induction over the environment,
substituting closed representatives and taking the quotient. Prove representative
independence, `eval_port`, and `eval_bindFree` from the owning substitution laws.
Prove the syntactic identity between `mapFree` and binding renamed ports, then
derive arbitrary-function `LambdaModel.eval_mapFree`; do not store naturality as a
fourth model field.

- [ ] **Step 5: Implement and prove certificate checking**

In `Certificate.lean`, define path segments matching the TypeScript reducer,
executable `stepAt`, and these certificate types:

```lean
inductive RedexKind | beta | eta
inductive PathSegment | fn | arg | body
structure ReductionStep where
  path : List PathSegment
  kind : RedexKind
abbrev ReductionPath := List ReductionStep
structure Certificate where
  left : ReductionPath
  right : ReductionPath

def checkPath (start : Term n α) (path : ReductionPath) : Option (Term n α)
def checkCertificate (left right : Term n α) (cert : Certificate) : Bool
theorem checkPath_sound : checkPath start path = some finish → BetaEta start finish
theorem checkCertificate_sound :
  checkCertificate left right cert = true → BetaEta left right
```

Prove path soundness by induction on the path and certificate soundness through the common endpoint.

- [ ] **Step 6: Run and commit**

Run: `lake build`

Expected: PASS, including the beta, eta, rigid-head, valid-certificate, and forged-certificate theorems.

```bash
git add VisualProof.lean VisualProof/Lambda
git commit -m "feat(formal): define beta-eta quotient and certificates"
```

### Task 3: Intrinsic diagrams, boundaries, and named signatures

**Files:**
- Create: `VisualProof/Theory/Signature.lean`
- Create: `VisualProof/Diagram/Core.lean`
- Create: `VisualProof/Diagram/Boundary.lean`
- Create: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: intrinsic `Term`.
- Produces: `RelVar`, `NamedRel`, `Region`, `Item`, `OpenDiagram`, `BoundaryAssignment`, wire/relation renaming, and capture-avoiding boundary substitution.

- [ ] **Step 1: Define the intrinsic syntax and state its scope/arity obligations**

In the owning modules, state named construction or well-formedness theorems for a
cut, a binary bubble atom, an ancestor wire used under a cut, a bare local wire,
and an aliased binary boundary. Public-constructor `#check`s are permitted only
when they validate elaboration/API shape not represented by a proposition.

The aliased boundary example must have `externalClasses := 1` and `boundary := fun _ => 0`.

- [ ] **Step 2: Implement typed relation contexts and intrinsic regions**

In `Signature.lean` and `Core.lean`, expose:

```lean
abbrev RelCtx := List Nat

structure RelVar (ctx : RelCtx) (arity : Nat) where
  index : Fin ctx.length
  hasArity : ctx.get index = arity

structure NamedRel (signature : List Nat) (arity : Nat) where
  index : Fin signature.length
  hasArity : signature.get index = arity

mutual
  inductive Region (signature : List Nat) (outer : Nat) (rels : RelCtx)
    | mk (local : Nat) (items : List (Item signature (outer + local) rels))

  inductive Item (signature : List Nat) (wires : Nat) (rels : RelCtx)
    | equation : Fin wires → Lambda.Term 0 (Fin wires) → Item signature wires rels
    | atom : RelVar rels n → (Fin n → Fin wires) → Item signature wires rels
    | named : NamedRel signature n → (Fin n → Fin wires) → Item signature wires rels
    | cut : Region signature wires rels → Item signature wires rels
    | bubble : (n : Nat) → Region signature wires (n :: rels) → Item signature wires rels
end
```

Keep constructors total; do not add raw binder IDs to the core.

- [ ] **Step 3: Implement ordered boundaries and alias consistency**

In `Boundary.lean`, define:

```lean
structure OpenDiagram (signature : List Nat) (arity : Nat) where
  externalClasses : Nat
  boundary : Fin arity → Fin externalClasses
  boundary_surjective : Function.Surjective boundary
  body : Region signature externalClasses []

structure BoundaryAssignment (d : OpenDiagram signature arity) (D : Type) where
  args : Fin arity → D
  classes : Fin d.externalClasses → D
  agrees : ∀ i, classes (d.boundary i) = args i
```

Prove an assignment exists exactly when aliased positions carry equal arguments.

- [ ] **Step 4: Implement renaming and substitution**

In `Diagram/Rename.lean`, define `Region.renameWires`, `Region.renameRelations`, `OpenDiagram.substituteBoundary`, and identity/composition laws. Boundary substitution must use `BoundaryAssignment.classes`; it may not infer aliasing from a list position.

- [ ] **Step 5: Build and commit**

Run: `lake build`

Expected: PASS for all intrinsic scope, arity, bare-wire, ancestor-wire, and boundary-alias theorems.

```bash
git add VisualProof.lean VisualProof/Diagram VisualProof/Theory/Signature.lean
git commit -m "feat(formal): add intrinsically scoped diagrams"
```

### Task 4: Diagram semantics, contexts, and isomorphism invariance

**Files:**
- Create: `VisualProof/Diagram/Semantics.lean`
- Create: `VisualProof/Diagram/Context.lean`
- Create: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `LambdaModel`, intrinsic diagrams, and boundaries.
- Produces: `Relation`, `RelEnv`, `NamedEnv`, `denoteRegion`, `denoteOpen`, `DiagramContext`, `context_mono`, `context_anti`, `Core.Isomorphic`, and `iso_denotation`.

- [ ] **Step 1: State the semantic characterization theorems**

In `Semantics.lean`, state named theorems showing:

- blank region denotes `True`;
- two items denote conjunction;
- cut denotes negation;
- a local bare wire is existentially quantified;
- `bubble 1` quantifies over all unary predicates;
- an aliased boundary rejects unequal arguments; and
- double cut is equivalent under classical logic.

The statements may temporarily use `sorry` while the interpreter interface is
formed; remove every admission before the task build and commit.

- [ ] **Step 2: Define the only semantic interpreter**

In `Semantics.lean`, define:

```lean
def Relation (D : Type) (n : Nat) := (Fin n → D) → Prop

def RelEnv (D : Type) : RelCtx → Type
  | [] => PUnit
  | n :: rest => Relation D n × RelEnv D rest

def NamedEnv (D : Type) (signature : List Nat) :=
  ∀ n, NamedRel signature n → Relation D n

mutual
  def denoteRegion (model : LambdaModel) (named : NamedEnv model.Carrier signature)
      (env : Fin outer → model.Carrier) (rels : RelEnv model.Carrier relCtx) :
      Region signature outer relCtx → Prop
  def denoteItem (model : LambdaModel) (named : NamedEnv model.Carrier signature)
      (env : Fin wires → model.Carrier) (rels : RelEnv model.Carrier relCtx) :
      Item signature wires relCtx → Prop
end

def denoteOpen (model : LambdaModel) (named : NamedEnv model.Carrier signature)
    (d : OpenDiagram signature arity) (args : Fin arity → model.Carrier) : Prop
```

`denoteRegion` existentially chooses local-wire values and conjoins `items`. `cut` is negation; `bubble` existentially chooses a relation; an equation compares model evaluation to the output wire.

- [ ] **Step 3: Prove context polarity once**

In `Context.lean`, define a typed single-hole context whose indices record the
outer and hole scopes separately:

```lean
inductive DiagramContext (signature : List Nat) :
    (outerWires holeWires : Nat) → (outerRels holeRels : RelCtx) → Type

def DiagramContext.cutDepth :
  DiagramContext signature outerWires holeWires outerRels holeRels → Nat

def DiagramContext.fill :
  DiagramContext signature outerWires holeWires outerRels holeRels →
  Region signature holeWires holeRels → Region signature outerWires outerRels

theorem context_mono
  (hEven : ctx.cutDepth % 2 = 0)
  (hab : ∀ holeEnv holeRelEnv,
    denoteRegion model named holeEnv holeRelEnv a →
    denoteRegion model named holeEnv holeRelEnv b) :
  denoteRegion model named env rels (ctx.fill a) →
  denoteRegion model named env rels (ctx.fill b)

theorem context_anti
  (hOdd : ctx.cutDepth % 2 = 1)
  (hab : ∀ holeEnv holeRelEnv,
    denoteRegion model named holeEnv holeRelEnv a →
    denoteRegion model named holeEnv holeRelEnv b) :
  denoteRegion model named env rels (ctx.fill b) →
  denoteRegion model named env rels (ctx.fill a)
```

Prove both simultaneously by induction on the context path; only the cut constructor swaps implication direction.

- [ ] **Step 4: Prove permutation and alpha invariance**

In `Isomorphism.lean`, define generalized mutually indexed region/item/item-sequence
isomorphism under an ambient finite wire equivalence. Lean 4.30 + Std does not
expose a general bundled `Equiv`, so define and use exactly one owned
`FiniteEquiv` record with forward/inverse functions and both inverse laws; prove
identity, inverse, composition, application, and extensionality once. Each region carries a
separate local-wire equivalence extended blockwise, so inherited and local wires
cannot mix. Equations move their output and term ports together; atom argument
positions and relation binders remain fixed; cuts and bubbles recurse.

Expose `ItemSeq.length` and dependent `ItemSeq.get` as eliminators over the sole
authoritative sequence. Represent conjunct permutation by an equivalence of
occurrence positions with recursively compatible items, never by converting to a
`List Item` or defining a second syntax. Prove generalized denotation invariance
under corresponding environments using the derived `LambdaModel.eval_mapFree`,
then specialize `Core.Isomorphic` to identity inherited wiring and prove
`iso_denotation`.

- [ ] **Step 5: Build and commit**

Run: `lake build`

Expected: PASS for all semantic characterization and context/isomorphism theorems.

```bash
git add VisualProof.lean VisualProof/Diagram
git commit -m "feat(formal): define diagram semantics and polarity"
```

### Task 5: Concrete graphs, well-formedness, elaboration, and subgraph algebra

**Files:**
- Create: `VisualProof/Diagram/Concrete.lean`
- Create: `VisualProof/Diagram/Elaborate.lean`
- Create: `VisualProof/Diagram/Subgraph.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: intrinsic diagrams, renaming, boundary substitution, semantics, and isomorphism.
- Produces: `ConcreteDiagram`, `ConcreteDiagram.WellFormed`, `ConcreteDiagram.elaborate`, `ConcreteDiagram.denote`, proof irrelevance, concrete isomorphism preservation, `Selection`, `extract`, `remove`, `splice`, and `denote_splice`.

- [ ] **Step 1: State adversarial well-formedness and elaboration theorems**

In `Concrete.lean` and `Elaborate.lean`, state named acceptance/rejection theorems
for a valid nested bubble/cut graph and invalid graphs covering a second sheet,
parent cycle, missing binder, binder escape, arity mismatch, missing endpoint port,
duplicate port incidence, and nonenclosing wire scope. State identifier-permutation
invariance as a named theorem. These statements precede their proofs; transient
admissions must be removed before build and commit.

- [ ] **Step 2: Implement total finite graph data**

In `Concrete.lean`, define:

```lean
inductive CRegion (regions : Nat)
  | sheet
  | cut (parent : Fin regions)
  | bubble (parent : Fin regions) (arity : Nat)

inductive CPort
  | output
  | free (index : Nat)
  | arg (index : Nat)

structure CEndpoint (nodes : Nat) where
  node : Fin nodes
  port : CPort

inductive CNode (regions : Nat)
  | term (region : Fin regions) (term : Lambda.Term 0 Nat)
  | atom (region binder : Fin regions)
  | named (region : Fin regions) (definition arity : Nat)

structure CWire (regions nodes : Nat) where
  scope : Fin regions
  endpoints : List (CEndpoint nodes)

structure ConcreteDiagram where
  regionCount nodeCount wireCount : Nat
  root : Fin regionCount
  regions : Fin regionCount → CRegion regionCount
  nodes : Fin nodeCount → CNode regionCount
  wires : Fin wireCount → CWire regionCount nodeCount

structure OpenConcreteDiagram where
  diagram : ConcreteDiagram
  boundary : List (Fin diagram.wireCount)
```

Define `WellFormed` as a structure containing each named invariant and `checkWellFormed : ConcreteDiagram → Except WFError d.WellFormed`. Prove checker soundness; do not use a Boolean accepted without a theorem.

After `WellFormed`, define:

```lean
abbrev CheckedDiagram (signature : List Nat) :=
  { d : ConcreteDiagram // d.WellFormed signature }

structure OpenConcreteDiagram.WellFormed
    (signature : List Nat) (d : OpenConcreteDiagram) : Prop where
  diagram : d.diagram.WellFormed signature
  boundary_root_scoped : ∀ wire ∈ d.boundary,
    (d.diagram.wires wire).scope = d.diagram.root
```

- [ ] **Step 3: Implement checked elaboration**

In `Elaborate.lean`, traverse the proved region tree. At each region, enumerate wires whose scope is that region, extend the lexical wire environment, turn term free positions into their incident wire variables, and turn atom binders into `RelVar` witnesses.

Expose:

```lean
def ConcreteDiagram.elaborate (signature : List Nat)
    (d : ConcreteDiagram) (h : d.WellFormed signature) :
  Region signature 0 []

def ConcreteDiagram.denote (model : LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (d : ConcreteDiagram) (h : d.WellFormed signature) : Prop :=
  denoteRegion model named Fin.elim0 PUnit.unit
    (d.elaborate signature h)

theorem elaborate_proof_irrelevant
    (d : ConcreteDiagram) (h₁ h₂ : d.WellFormed signature) :
  d.elaborate signature h₁ = d.elaborate signature h₂
```

Concrete denotation must be this definition, not a second interpreter.

- [ ] **Step 4: Implement selection, extraction, and splicing**

In `Subgraph.lean`, define selections by finite sets of top-level child regions, nodes, and scoped wires. `extract` returns an `OpenDiagram`, ordered attachment classes, and open relation-binder stubs. `splice` validates enclosure and binder maps before extending the host.

Prove:

```lean
theorem denote_splice :
  denote (splice host site pattern args binderMap ok) ↔
  denoteContext host site (denoteOpen canonicalModel named pattern args)

theorem remove_splice_inverse :
  Concrete.Isomorphic
    (remove (splice host site pattern args binderMap ok) insertedSelection)
    host
```

- [ ] **Step 5: Build and commit**

Run: `lake build`

Expected: PASS for the complete well-formedness rejection matrix, identifier permutation, and splice laws.

```bash
git add VisualProof.lean VisualProof/Diagram
git commit -m "feat(formal): elaborate finite graphs into semantics"
```

### Task 6: Ordered named-relation theory semantics

**Files:**
- Create: `VisualProof/Theory/Definition.lean`
- Create: `VisualProof/Theory/Semantics.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: `OpenDiagram`, `denoteOpen`, and named signatures.
- Produces: `Definition`, `VerifiedDefinitions`, `verifyDefinitions`, `interpretDefinitions`, `definition_equation`, and typed lookup for fold/unfold.

- [ ] **Step 1: State ordered-DAG acceptance and rejection theorems**

State named theorems accepting an empty definition and a definition referring to an
earlier entry, and rejecting an unknown reference, arity mismatch, forward
reference, self-reference, and a two-definition cycle. Locate each theorem beside
the verifier or semantic definition it characterizes.

- [ ] **Step 2: Define ordered definitions and verification**

Expose:

```lean
structure RawDefinition where
  arity : Nat
  body : OpenConcreteDiagram

abbrev RawDefinitions := List RawDefinition

inductive DefinitionError
  | unknownReference (definition node : Nat)
  | arityMismatch (definition node expected actual : Nat)
  | forwardReference (definition node target : Nat)

structure Definition (priorSignature : List Nat) where
  arity : Nat
  body : OpenDiagram priorSignature arity

inductive VerifiedDefinitions : List Nat → Type
  | empty : VerifiedDefinitions []
  | snoc {signature : List Nat}
      (prior : VerifiedDefinitions signature)
      (definition : Definition signature) :
      VerifiedDefinitions (signature ++ [definition.arity])

structure SomeVerifiedDefinitions where
  signature : List Nat
  value : VerifiedDefinitions signature

def verifyDefinitions : RawDefinitions → Except DefinitionError SomeVerifiedDefinitions
```

Verification processes definitions in order and resolves every named index against the current prefix. Because later entries are unavailable to the body type, self and cyclic references are unrepresentable after verification.

- [ ] **Step 3: Define semantics by recursion over the DAG**

Implement:

```lean
def interpretDefinitions {signature : List Nat}
    (defs : VerifiedDefinitions signature) : NamedEnv Individual signature
```

For each appended definition, its relation is `denoteOpen` under the already interpreted prefix. Prove `definition_equation` stating lookup of the new name equals its body's denotation.

- [ ] **Step 4: Build and commit**

Run: `lake build`

Expected: PASS for ordered definitions and all rejection examples.

```bash
git add VisualProof.lean VisualProof/Theory
git commit -m "feat(formal): define acyclic relation theories"
```

### Task 7: Structural rule execution and soundness

**Files:**
- Create: `VisualProof/Rule/Step.lean`
- Create: `VisualProof/Rule/Structural.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: concrete subgraph algebra, context polarity, and theory lookups.
- Produces: `Orientation`, `StepTag`, structural step payloads, typed `StepError`, structural appliers, well-formedness preservation, and per-rule semantic theorems.

- [ ] **Step 1: Lock the 25-tag enumeration and state structural obligations**

In `Step.lean`, declare the canonical tag enumeration up front:

```lean
inductive StepTag
  | openTermSpawn | relationSpawn | boundRelationSpawn | wireJoin
  | erasure | wireSever | iteration | deiteration
  | doubleCutIntro | doubleCutElim | conversion | congruenceJoin
  | anchoredWireSplit | anchoredWireContract | headStrip | closedTermIntro
  | fusion | fission | comprehensionInstantiate | comprehensionAbstract
  | theorem | vacuousIntro | vacuousElim | relUnfold | relFold
  deriving DecidableEq, Repr
```

State named success/refusal theorems for polarity cases, incomparable wire scopes,
binder escape during iteration, unjustified deiteration, dirty double-cut annulus,
and nonvacuous bubble elimination. The semantic theorem statements precede the
applier proofs and may be transiently admitted only during local development.

- [ ] **Step 2: Implement structural payloads and appliers**

Define the `Step` sum with one payload per `StepTag`, preserving the TypeScript fields while replacing raw strings with finite indices. Implement:

```lean
def applyOpenTermSpawn
def applyRelationSpawn
def applyBoundRelationSpawn
def applyWireJoin
def applyErasure
def applyWireSever
def applyIteration
def applyDeiteration
def applyDoubleCutIntro
def applyDoubleCutElim
def applyVacuousIntro
def applyVacuousElim
```

Each function consumes and returns `CheckedDiagram signature`, using
`Except StepError (CheckedDiagram signature)`. Fresh IDs extend finite
vectors; they are not semantic inputs.

- [ ] **Step 3: Prove structural soundness from shared semantic lemmas**

Prove one theorem per tag with successful application as its premise. Factor the proofs through:

```lean
theorem negative_insertion_sound
theorem positive_erasure_sound
theorem identity_join_sound
theorem identity_sever_sound
theorem iteration_sound
theorem doubleCut_equiv
theorem vacuousRelation_equiv
```

Use `context_mono` or `context_anti` for every polarity gate. `deiteration` must consume an exact occurrence witness, not a Boolean match result without proof.

- [ ] **Step 4: Build and commit**

Run: `lake build`

Expected: PASS for every structural success/refusal theorem and all twelve structural soundness theorems.

```bash
git add VisualProof.lean VisualProof/Rule/Step.lean VisualProof/Rule/Structural.lean
git commit -m "feat(formal): prove structural rules sound"
```

### Task 8: Equational rule execution and soundness

**Files:**
- Create: `VisualProof/Rule/Equational.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: beta-eta certificates, rigid-head theorem, subgraph algebra, and concrete semantics.
- Produces: appliers and semantic theorems for conversion, congruence join, anchored split/contract, head strip, closed introduction, fusion, and fission.

- [ ] **Step 1: State positive, inverse, and refusal theorems per equational family**

Cover forged conversion certificates, mismatched shared free wires, cut-shielded output scopes, open anchored witnesses, moved endpoints outside availability, head mismatch, non-head-normal terms, open closed-term introduction, self fusion, multi-endpoint fusion, and binder-open fission paths.

Locate these named theorems beside the owning appliers and semantic results.

- [ ] **Step 2: Implement executable equational appliers**

Implement:

```lean
def applyConversion
def applyCongruenceJoin
def applyAnchoredWireSplit
def applyAnchoredWireContract
def applyHeadStrip
def applyClosedTermIntro
def applyFusion
def applyFission
```

Conversion accepts only `checkCertificate = true`. Head strip calls a decidable head-spine checker whose output carries the premises required by `rigidHead_args`. Fusion and fission use capture-avoiding term substitution from Task 1.

- [ ] **Step 3: Prove equational soundness**

Expose and prove:

```lean
theorem conversion_equiv
theorem congruenceJoin_equiv
theorem anchoredWireSplit_equiv
theorem anchoredWireContract_equiv
theorem headStrip_entails
theorem closedTermIntro_equiv
theorem fusion_equiv
theorem fission_equiv
```

`headStrip_entails` must derive argument equations through `rigidHead_args`; if its exact executable gate does not supply the theorem premises, stop and tighten the gate rather than assuming injectivity.

- [ ] **Step 4: Build the complete equational theory**

Run: `lake build`

Expected: PASS, including conversion, anchored split/contract, fusion/fission, and all semantic soundness theorems.

- [ ] **Step 5: Commit**

```bash
git add VisualProof.lean VisualProof/Rule
git commit -m "feat(formal): prove equational rules sound"
```

### Task 9: Comprehension, named rewriting, proof replay, and global step soundness

**Files:**
- Create: `VisualProof/Rule/Comprehension.lean`
- Create: `VisualProof/Rule/Named.lean`
- Create: `VisualProof/Rule/Soundness.lean`
- Create: `VisualProof/Proof/Replay.lean`
- Create: `VisualProof/Proof/Theorem.lean`
- Create: `VisualProof/Proof/Theory.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: all prior semantic, theory, subgraph, and rule theorems.
- Produces: comprehension/definition/theorem appliers; `applyStep`; `applyStep_sound`; replay, theorem, and verified-theory soundness.

- [ ] **Step 1: State adversarial comprehension and theorem obligations**

Cover positive abstraction, negative instantiation, backward gate reversal, zero occurrences, diagonal arguments `R(x,x)`, parameter sharing, open binder ancestry, overlapping abstraction occurrences, mismatched pinned boundaries, relation fold/unfold, boundary destruction during theorem replay, and citation at both polarities.

State named theorems for these cases in their owning comprehension, named-rule,
replay, and theorem modules before implementing their proofs.

- [ ] **Step 2: Implement comprehension and diagonal boundaries**

Define `diagonalize` as the quotient of boundary positions generated by intrinsic aliases and call-site aliases. Implement `applyComprehensionInstantiate` and `applyComprehensionAbstract` with explicit occurrence proofs, nonoverlap, parameter enclosure, and open-binder ancestry.

Prove:

```lean
theorem comprehensionInstantiate_sound
theorem comprehensionAbstract_sound
theorem diagonalize_denotation
```

Use full relation quantification in `Prop`; do not restrict comprehension bodies to atomic or first-order patterns.

- [ ] **Step 3: Implement fold, unfold, and theorem citation**

`applyRelUnfold` and `applyRelFold` consume a verified ordered definition and exact occurrence proof. `applyTheorem` consumes a `VerifiedTheorem`, direction, orientation, and pinned-boundary occurrence. Prove all three through `definition_equation`, `denote_splice`, and context polarity.

- [ ] **Step 4: Implement replay and theorem verification**

Expose:

```lean
def applyStep : ProofContext signature → Orientation →
  CheckedDiagram signature → Step signature →
  Except StepError (CheckedDiagram signature)

theorem applyStep_sound :
  applyStep ctx orientation d step = .ok d' →
  DirectedEntailment ctx orientation step d d'

def replay : ProofContext signature → Orientation →
  CheckedDiagram signature → List (Step signature) →
  Except ProofError (CheckedDiagram signature)

theorem replay_sound
theorem backward_replay_sound
def checkTheorem : ProofContext → RawTheorem → Except ProofError VerifiedTheorem
theorem checkedTheorem_sound
def verifyTheory : RawTheory → Except ProofError VerifiedTheory
theorem verifiedTheory_sound
```

`applyStep_sound` must exhaust all 25 constructors. Boundary survival is checked after each constituent step and represented in `VerifiedTheorem`.

- [ ] **Step 5: Build and commit**

Run: `lake build`

Expected: PASS for all comprehension, definition, replay, backward, citation, and theory theorems. The 25-constructor `applyStep_sound` proof must be structurally exhaustive; the correspondence audit independently proves exact tag-set equality.

```bash
git add VisualProof.lean VisualProof/Rule VisualProof/Proof
git commit -m "feat(formal): prove proof and theory soundness"
```

### Task 10: Declarative occurrence embeddings and exact verified matcher

**Files:**
- Create: `VisualProof/Matcher/Specification.lean`
- Create: `VisualProof/Matcher/Exact.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: well-formed concrete diagrams, finite indices, exact term shape, boundaries, and subgraph selections.
- Produces: `Occurrence`, `CandidateOccurrence.Equivalent`, `exactMatcher`, `exactMatcher_sound`, `exactMatcher_complete`, and `exactMatcher_decides`.

- [ ] **Step 1: State the exact matcher contract before search code**

In `Specification.lean`, state named positive and negative characterization
theorems for root-subset semantics, exact nested regions, boundary order, repeated
boundary identity, bare boundaries with supplied attachments, open binder chains,
named reference identity, atom binder preservation, wire scope, multi-endpoint
wires, and a symmetric sibling graph requiring a nonidentity assignment.

- [ ] **Step 2: Define the declarative occurrence relation**

In `Specification.lean`, define:

```lean
structure MatchOptions (pattern : OpenConcreteDiagram) (host : ConcreteDiagram) where
  inRegion : Option (Fin host.regionCount)
  attachments : Option (Fin pattern.boundary.length → Fin host.wireCount)
  openBinders : List (Fin pattern.diagram.regionCount × Fin host.regionCount)

structure CandidateOccurrence (pattern : OpenConcreteDiagram)
    (host : ConcreteDiagram) where
  site : Fin host.regionCount
  regionMap : Fin pattern.diagram.regionCount → Fin host.regionCount
  nodeMap : Fin pattern.diagram.nodeCount → Fin host.nodeCount
  wireMap : Fin pattern.diagram.wireCount → Fin host.wireCount

structure Occurrence (pattern : OpenConcreteDiagram) (host : ConcreteDiagram)
    (options : MatchOptions pattern host)
    (candidate : CandidateOccurrence pattern host) : Prop where
  root_maps_to_site : candidate.regionMap pattern.diagram.root = candidate.site
  regions_preserved : RegionsPreserved pattern host candidate.regionMap options
  nodes_preserved : NodesPreserved pattern host candidate.regionMap candidate.nodeMap candidate.wireMap options
  wires_preserved : WiresPreserved pattern host candidate.regionMap candidate.nodeMap candidate.wireMap options
  nested_exact : NestedRegionsExact pattern host candidate.regionMap candidate.nodeMap candidate.wireMap
  root_subset : EffectiveRootSubset pattern host candidate.regionMap candidate.nodeMap candidate.wireMap
  boundary_preserved : BoundaryPreserved pattern host candidate.wireMap options.attachments
  open_binders_preserved : OpenBindersPreserved pattern host candidate.regionMap options.openBinders
```

Define `CandidateOccurrence.Equivalent` by equal host footprint and boundary attachments so automorphic assignments may deduplicate.

- [ ] **Step 3: Implement exhaustive finite enumeration**

In `Exact.lean`, enumerate candidate sites, injections for region and node maps, and determined/finite wire maps using `List.ofFn` over `Fin` domains. Filter only by decidable projections of the fields in `Occurrence`. Bare wires receive finite canonical bijections; no heuristic pruning is allowed in the reference algorithm.

Return finite raw candidates; soundness is proved separately:

```lean
def exactMatcher (pattern host options) :
  List (CandidateOccurrence pattern host)
```

- [ ] **Step 4: Prove soundness and completeness**

Prove soundness from filter membership. Prove completeness by showing that the finite enumeration contains the maps from any declarative occurrence, then that filtering retains them. Deduplication concludes with `CandidateOccurrence.Equivalent`.

```lean
theorem exactMatcher_sound :
  found ∈ exactMatcher pattern host options →
  Occurrence pattern host options found

theorem exactMatcher_complete :
  Occurrence pattern host options witness →
  ∃ found ∈ exactMatcher pattern host options,
    CandidateOccurrence.Equivalent found witness

theorem exactMatcher_decides :
  (exactMatcher pattern host options).isEmpty ↔
  ¬ ∃ witness, Occurrence pattern host options witness
```

- [ ] **Step 5: Build and commit**

Run: `lake build`

Expected: PASS for the complete matcher matrix, including the symmetric nonidentity assignment.

```bash
git add VisualProof.lean VisualProof/Matcher
git commit -m "feat(formal): prove exact matcher complete"
```

### Task 11: Certificate-backed beta-eta matcher boundaries

**Files:**
- Create: `VisualProof/Matcher/BetaEta.lean`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: exact occurrence specification, exact matcher, and certificate soundness.
- Produces: `NodeVerdict`, `MatchStatus`, `BetaEtaMatchResult`, `betaEtaMatcher_sound`, and `betaEtaMatcher_complete_of_decided`.

- [ ] **Step 1: State decided, undecided, and exploration-exhausted theorems**

State named theorems for a beta-redex match with a valid certificate, a forged
certificate, a pair whose bounded normalizer exhausts, and a search whose explicit
exploration budget exhausts before a later occurrence.

- [ ] **Step 2: Implement honest result states**

Define:

```lean
structure NormalFormsDiffer (left right : Lambda.Term n α) : Prop where
  leftNormal : IsNormal left
  rightNormal : IsNormal right
  distinct : left ≠ right

structure ExhaustionDetail where
  side : String
  fuel : Nat

structure UndecidedPair where
  patternNode : Nat
  hostNode : Nat
  detail : ExhaustionDetail

def BetaEtaOccurrence (pattern : OpenConcreteDiagram)
    (host : ConcreteDiagram) (options : MatchOptions pattern host)
    (candidate : CandidateOccurrence pattern host) : Prop :=
  StructuralOccurrenceExceptTerms pattern host options candidate ∧
  ∀ patternNode hostNode,
    candidate.nodeMap patternNode = hostNode →
    MatchingTermNodes pattern.diagram host patternNode hostNode →
    BetaEta (patternTerm pattern.diagram patternNode)
      (hostTerm host hostNode)

inductive NodeVerdict
  | match (certificate : Certificate) (sound : checkCertificate left right certificate = true)
  | noMatch (normalFormsDiffer : NormalFormsDiffer left right)
  | undecided (detail : ExhaustionDetail)

inductive MatchStatus | complete | exhausted

structure BetaEtaMatchResult where
  status : MatchStatus
  matches : List SoundOccurrence
  undecided : List UndecidedPair
  explorationSteps : Nat

structure SoundOccurrence where
  candidate : CandidateOccurrence pattern host
  occurrence : BetaEtaOccurrence pattern host options candidate
  nodeCertificates : EveryTermNodeCarriesCertificate candidate

def EveryRelevantConvertiblePairCertified
    (pattern host result) : Prop :=
  ∀ pair, RelevantConvertiblePair pattern host pair →
    ∃ cert, pair ∉ result.undecided ∧
      checkCertificate pair.left pair.right cert = true
```

Every returned node comparison must carry `checkCertificate_sound`; undecided pairs are never silently treated as proof of inequality.

- [ ] **Step 3: Prove unconditional soundness and conditional completeness**

```lean
theorem betaEtaMatcher_sound :
  found ∈ (betaEtaMatcher pattern host options).matches →
  BetaEtaOccurrence pattern host options found

theorem betaEtaMatcher_complete_of_decided
  (hstatus : result.status = .complete)
  (hdecided : EveryRelevantConvertiblePairCertified pattern host result) :
  BetaEtaOccurrence pattern host options witness →
  ∃ found ∈ result.matches, found.Equivalent witness
```

The theorem statement must mention both completion hypotheses visibly.

- [ ] **Step 4: Build and commit**

Run: `lake build`

Expected: PASS while preserving distinct undecided and exhausted theorems.

```bash
git add VisualProof.lean VisualProof/Matcher
git commit -m "feat(formal): bound beta-eta matcher completeness"
```

### Task 12: TypeScript correspondence and definition-DAG migration

**Files:**
- Create: `VisualProof/Correspondence/StepTags.lean`
- Create: `VisualProof/Correspondence/StepTagsMain.lean`
- Create: `VisualProof/Correspondence/MatchFixturesMain.lean`
- Create: `scripts/check-lean-step-tags.mjs`
- Create: `scripts/check-formalization.mjs`
- Create: `tests/kernel/formal/correspondence.test.ts`
- Modify: `lakefile.toml`
- Modify: `package.json`
- Modify: `src/kernel/proof/store.ts`
- Modify: `tests/kernel/proof/store.test.ts`
- Modify: `VisualProof.lean`

**Interfaces:**
- Consumes: canonical Lean `StepTag`, verified exact matcher, ordered definitions, and the TypeScript `ProofStep` union.
- Produces: machine-readable step tags, deterministic matcher fixtures, exact tag-set validation, TypeScript DAG enforcement, and `npm run formal:check`.

- [ ] **Step 1: Write failing TypeScript coverage and DAG tests**

Add tests that parse emitted Lean tags and compare them with the 25 `ProofStep` discriminants. Add store tests constructing ordered definitions with a valid backward reference and invalid unknown, forward, self, and cyclic references.

Run:

`npx vitest run --config vitest.config.ts tests/kernel/formal/correspondence.test.ts tests/kernel/proof/store.test.ts`

Expected: FAIL because emitters, script, and DAG validation do not exist.

- [ ] **Step 2: Emit canonical tags from Lean**

Define `StepTag.all : List StepTag`, prove `nodup` and completeness by constructor cases, and map tags to the exact TypeScript strings. `StepTagsMain.lean` prints one JSON array. Add to `lakefile.toml`:

```toml
[[lean_exe]]
name = "visualproof_step_tags"
root = "VisualProof.Correspondence.StepTagsMain"

[[lean_exe]]
name = "visualproof_match_fixtures"
root = "VisualProof.Correspondence.MatchFixturesMain"
```

- [ ] **Step 3: Implement exact set comparison without a duplicate list**

`scripts/check-lean-step-tags.mjs` must:

1. run `lake exe visualproof_step_tags`;
2. read `src/kernel/proof/step.ts`;
3. extract literal values following `readonly rule:` inside `ProofStep`;
4. compare sorted unique sets;
5. fail on missing, extra, or duplicate tags; and
6. print the agreed count.

The script may not contain its own expected tag list.

- [ ] **Step 4: Emit and compare matcher fixtures**

Create deterministic Lean fixtures for boundary aliases, nested exactness, open binders, bare wires, and symmetry fallback. Emit pattern, host, options, and canonical occurrence footprints as JSON lines. The TypeScript test rebuilds the same graphs through `mkDiagram`, calls `findOccurrences` in exact mode, and compares footprints.

- [ ] **Step 5: Enforce the ordered definition DAG in TypeScript**

Replace the all-at-once relation resolution in `verifyTheory` with registration-order validation. While visiting each relation body, resolve `ref` nodes only against the prefix map. Reject forward/self/cyclic references with the offending relation and reference IDs. Theorems resolve against the complete verified relation prefix.

Do not add a legacy mode accepting unordered definitions.

- [ ] **Step 6: Add repository formal commands**

Add to `package.json`:

```json
{
  "scripts": {
    "formal:tags": "node scripts/check-lean-step-tags.mjs",
    "formal:check": "node scripts/check-formalization.mjs"
  }
}
```

`check-formalization.mjs` runs `lake build`, scans Lean source for forbidden proof placeholders and project axioms, runs `lake env lean VisualProof/Audit.lean`, invokes tag comparison, runs matcher differential tests, then runs `npm run typecheck`. It exits on the first failure with the command and captured output.

- [ ] **Step 7: Verify and commit**

Run:

`npm run formal:check`

`npm test`

Expected: PASS; tag check reports exactly 25; definition tests reject every cyclic/forward case.

```bash
git add VisualProof.lean VisualProof/Correspondence lakefile.toml scripts/check-lean-step-tags.mjs scripts/check-formalization.mjs tests/kernel/formal/correspondence.test.ts src/kernel/proof/store.ts tests/kernel/proof/store.test.ts package.json
git commit -m "feat(formal): enforce Lean runtime correspondence"
```

### Task 13: Public theorem audit and full completion oracle

**Files:**
- Create: `VisualProof/Audit.lean`
- Modify: `VisualProof.lean`
- Modify: `docs/kernel/canonicalization.md`
- Modify: `docs/superpowers/specs/2026-07-13-lean-formalization-design.md`

**Interfaces:**
- Consumes: every public semantic, soundness, theory, and matcher theorem.
- Produces: explicit axiom audit output, final 25-row coverage evidence, user-facing kernel documentation, and the full completion receipt.

- [ ] **Step 1: Add the public audit module**

`VisualProof/Audit.lean` imports the complete library and runs `#print axioms` for:

```lean
VisualProof.Lambda.checkCertificate_sound
VisualProof.Diagram.iso_denotation
VisualProof.Diagram.denote_splice
VisualProof.Rule.applyStep_sound
VisualProof.Proof.checkedTheorem_sound
VisualProof.Proof.verifiedTheory_sound
VisualProof.Matcher.exactMatcher_sound
VisualProof.Matcher.exactMatcher_complete
VisualProof.Matcher.exactMatcher_decides
VisualProof.Matcher.betaEtaMatcher_sound
VisualProof.Matcher.betaEtaMatcher_complete_of_decided
```

Make `check-formalization.mjs` parse this output and reject every name outside the documented allowlist.

- [ ] **Step 2: Mutate each completion gate once**

Perform and revert these local probes:

- add a temporary `sorry` and observe `formal:check` fail;
- add a temporary project `axiom` and observe failure;
- remove one Lean step tag and observe tag mismatch;
- add one TypeScript `ProofStep` tag and observe tag mismatch;
- replace one exact matcher expected footprint and observe differential failure; and
- temporarily hide an exhausted beta-eta result and observe its test fail.

Record the observed failure messages in the final task receipt; do not commit mutations.

- [ ] **Step 3: Document the authority boundary**

Update `docs/kernel/canonicalization.md` to link the Lean isomorphism and matcher theorems and state precisely:

- canonical Lean semantics is authoritative;
- the exact matcher theorem applies to `Matcher.Specification.Occurrence`;
- TypeScript differential checks establish monitored correspondence, not a machine proof of TypeScript execution; and
- beta-eta completeness remains conditional on decisions and complete exploration.

Append the final `<conformance>` section to `/tmp/visualproof-foundation-20260713-lean-formalization.xml`, recording implemented owners, migrated TypeScript definition semantics, deleted competing paths, validation commands, and evidence that no previous model remains.

- [ ] **Step 4: Run the complete oracle from a clean state**

Run:

`git diff --check`

`lake build`

`npm run formal:check`

`npm test`

`npm run typecheck`

`rg -n "sorry|admit|decreasing_by[[:space:]]+sorry|^[[:space:]]*axiom[[:space:]]" VisualProof VisualProof.lean`

Expected: every command PASS; the final `rg` exits 1 with no matches; tag coverage is exactly 25; audit output contains no unapproved axiom.

- [ ] **Step 5: Build the final coverage receipt**

Produce a 25-row mapping from TypeScript tag to Lean constructor, executable applier, semantic theorem, shared metatheorems, and verification command. Audit every explicit requirement in the design spec against current files and command output. Reject completion for any missing or indirect evidence.

- [ ] **Step 6: Commit final audit documentation**

```bash
git add VisualProof.lean VisualProof/Audit.lean docs/kernel/canonicalization.md docs/superpowers/specs/2026-07-13-lean-formalization-design.md
git commit -m "docs(formal): record verified semantics and audit"
```

## Plan Self-Review Results

- Spec sections 1–16 map to Tasks 1–13.
- Every one of the 25 TypeScript tags is introduced in Task 7 and receives a dispatcher branch and semantic theorem by Task 9.
- Lambda quotient semantics, head-strip's nontrivial rigid-head theorem, boundary aliasing, context polarity, concrete elaboration, named-definition acyclicity, exact matcher completeness, conditional beta-eta matching, and TypeScript correspondence each have an explicit task and oracle.
- The plan defines every cross-task public name before it is consumed.
- The plan contains no deferred implementation placeholder or proof hole.
- Rendering, physics, UI, and general calculus completeness remain outside scope.
