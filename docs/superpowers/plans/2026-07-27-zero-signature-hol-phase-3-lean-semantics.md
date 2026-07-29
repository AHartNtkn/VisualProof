# Zero-Signature HOL Phase 3 Lean Semantics Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the deferred Lambda/comprehension Lean formalization with a
sound, signature-indexed, all-models formal semantics for the landed
zero-signature kernel and its complete 15-step proof language.

**Architecture:** Rebuild the Lean library around a small intrinsic semantic
core and a checked finite-graph elaboration bridge matching the TypeScript
diagram vocabulary. Structural soundness is proved over a generic prestructure;
`Model` specializes every higher signature to a full Lean function space, and
only strongest-form relational sever/join use that fullness. Concrete rule
applications elaborate to the intrinsic calculus, then proof, theorem, and
ordered-theory soundness compose those rule theorems.

**Tech Stack:** Lean 4.30.0 + Std, Lake, TypeScript 5.5+, Node 20+, Vitest.

## Global Constraints

- Phase 3 changes Lean semantics and formal-validation tooling only. Do not
  change `src/kernel/**`, theory construction, proof JSON, generated theories,
  replay, interaction, or view behavior.
- `LambdaModel` becomes `Model`. No `eval`, `eval_port`, `eval_bindFree`,
  `betaEta_sound`, Lambda term, quotient, normalization, or βη declaration
  survives.
- Signatures are exactly recursive `ι | rel(Sig…)`; no `Nat`-only arity context
  remains as semantic authority.
- A `Model` has a nonempty carrier for `ι`; every higher signature denotes the
  full Lean function space over its recursively interpreted argument domains.
- Validity means truth in every `Model`, never truth in a canonical model.
- The intrinsic content vocabulary has atom, named/ref, identity, cut, and wire
  binding. The `rel` case of the uniform wire binder is the specification's
  higher-order bubble; there is no second concrete bubble-region authority.
- Identity ports are semantically unordered at every signature. Identity
  denotation is n-ary all-equal, and no extensionality or distinctness oracle is
  grammatical.
- Prove all five identity transformations: degeneracy, co-scoped collapse,
  same-region fusion, orientation-aware insertion/erasure, and
  identity-retargeted iteration/deiteration.
- Prove definitional unfold/fold as boundary-pinned splice equivalence sourced
  only from the ordered definition store.
- Prove strongest-form wire sever/join. Their relation-content cases are the only
  soundness proofs allowed to use fullness; all structural, identity,
  definitional, and `ι` cases must be prestructure-generic.
- The formal proof-step inventory is exactly:
  `refSpawn`, `atomSpawn`, `identityInsert`, `wireJoin`, `erasure`,
  `wireSever`, `iteration`, `deiteration`, `doubleCutIntro`,
  `doubleCutElim`, `theorem`, `vacuousIntro`, `vacuousElim`, `unfold`,
  `fold`.
- Forward insertion requires negative polarity; backward physical insertion
  requires positive polarity. Forward erasure requires positive polarity and is
  rejected during backward replay.
- Do not add a macro system, computation layer, reference-HOL syntax,
  translation, denotation-preservation theorem, Henkin semantics, or any
  Phase-4 artifact.
- No `axiom`, `sorry`, `admit`, `unsafe`, or custom classical postulate.
  Lean's standard classical logic is permitted.
- Keep every maintained source file below 3,000 physical lines.
- TDD is mandatory. Every task starts from a failing executable test, failing
  Lean example, or absent theorem checked by a dedicated audit module.
- Run `lake build` after every Lean task. Stage and commit only explicit paths.
  Never stash. Leave `archive/` and `scratchpad/` untouched.

## Selected File Structure

The current semantic hierarchy is displaced, not migrated. Retain only
`VisualProof/Data/Finite.lean`; replace every other `VisualProof/**` source with
the following owners:

```text
VisualProof.lean
VisualProof/
  Audit.lean
  Data/Finite.lean                         # retained generic finite utilities
  Sig.lean                                 # recursive signatures and typed refs
  Model.lean                               # PreModel, full Model, environments
  Diagram/
    Core.lean                              # intrinsic regions/items/wire binders
    Semantics.lean                         # denotation and all-model validity
    Context.lean                           # polarity and contextual transport
    Open.lean                              # ordered/aliased boundaries
    Concrete/
      Core.lean                            # finite TS-shaped graph
      WellFormed.lean                      # one authoritative checker/proposition
      Elaborate.lean                       # checked graph -> intrinsic diagram
      Isomorphism.lean                     # identifier/order invariance
      Examples.lean                        # executable correspondence fixtures
      Subgraph/
        Selection.lean                     # closed selections
        Occurrence.lean                    # exact occurrence certificates
        Extract.lean                       # open extraction
        Splice.lean                        # capture-avoiding boundary splice
  Theory/
    Definition.lean                        # ordered dependent definition context
    Semantics.lean                         # recursively interpreted definitions
  Rule/
    Tag.lean                               # exact 15-constructor inventory
    Identity.lean                          # normalization + substitution
    Structural.lean                        # insertion/erasure/copy/cuts/vacuity
    WireQuantifier.lean                    # strongest sever/join
    Definition.lean                        # ref spawn and fold/unfold
    Theorem.lean                           # contextual cited rewrite
    Step.lean                              # executable checked step sum
    Soundness.lean                         # complete step theorem
  Proof/
    Replay.lean                            # forward/backward replay soundness
    Theorem.lean                           # meet-in-the-middle theorem soundness
    Theory.lean                            # ordered verification soundness
  Correspondence/
    StepTags.lean                          # serialized tag projection
    StepTagsMain.lean                      # executable tag output
```

No import umbrella may preserve a displaced implementation path. `VisualProof.lean`
is the only umbrella and imports exactly the maintained modules above.

---

### Task 1: Remove the displaced formalization and establish the typed model core

**Files:**

- Delete: `VisualProof/Lambda/`
- Delete: `VisualProof/Correspondence/`
- Delete: `VisualProof/Diagram/`
- Delete: `VisualProof/Proof/`
- Delete: `VisualProof/Rule/`
- Delete: `VisualProof/Theory/`
- Delete: `VisualProof/Audit.lean`
- Replace: `VisualProof.lean`
- Create: `VisualProof/Sig.lean`
- Create: `VisualProof/Model.lean`
- Modify: `lakefile.toml`
- Create: `tests/architecture/lean-semantics.test.ts`

**Interfaces:**

- Produces:
  `VisualProof.Sig`,
  `Sig.denote`,
  `Sig.Args`,
  `Var`,
  `Vars`,
  `PreModel`,
  `Model`,
  `Model.toPreModel`,
  `Env`,
  `Env.extend`,
  and `Env.append`.
- Retains: `VisualProof.Data.Finite.FiniteEquiv`.

- [x] **Step 1: Write the failing displaced-model architecture test**

Create `tests/architecture/lean-semantics.test.ts` with a recursive Lean-source
reader that excludes `.lake`, `archive`, and `scratchpad`, then assert:

```ts
expect(existsSync('VisualProof/Lambda')).toBe(false)
expect(source).not.toMatch(
  /\b(LambdaModel|betaEta|Item\.equation|comprehension|fusion|fission|headStrip|inconsistentCut)\b/i,
)
expect(source).not.toContain('openTermSpawn')
expect(source).not.toContain('congruenceJoin')
```

Also assert that `VisualProof/Sig.lean`, `VisualProof/Model.lean`, and the retained
`VisualProof/Data/Finite.lean` exist.

- [x] **Step 2: Run the architecture test and verify RED**

Run:

```bash
npx vitest run tests/architecture/lean-semantics.test.ts
```

Expected: FAIL because `VisualProof/Lambda/` exists and the source contains the
displaced vocabulary.

- [x] **Step 3: Delete the displaced hierarchy explicitly**

Run only these exact deletions:

```bash
git rm -r -- \
  VisualProof/Lambda \
  VisualProof/Correspondence \
  VisualProof/Diagram \
  VisualProof/Proof \
  VisualProof/Rule \
  VisualProof/Theory
git rm -- VisualProof/Audit.lean VisualProof.lean
```

Do not remove `VisualProof/Data/Finite.lean`.

- [x] **Step 4: Implement recursive signatures and typed variables**

Create `VisualProof/Sig.lean` with:

```lean
namespace VisualProof

inductive Sig where
  | iota
  | rel (args : List Sig)
  deriving Repr

mutual
  def Sig.denote (Carrier : Type u) : Sig → Type u
    | .iota => Carrier
    | .rel args => Sig.Args Carrier args → Prop

  def Sig.Args (Carrier : Type u) : List Sig → Type u
    | [] => PUnit
    | sig :: rest => Sig.denote Carrier sig × Sig.Args Carrier rest
end

inductive Var : List Sig → Sig → Type
  | here : Var (sig :: rest) sig
  | there : Var rest sig → Var (head :: rest) sig

inductive Vars (ctx : List Sig) : List Sig → Type
  | nil : Vars ctx []
  | cons : Var ctx sig → Vars ctx rest → Vars ctx (sig :: rest)

end VisualProof
```

Add structural `Sig.beq`, prove `Sig.beq_eq_true_iff`, and define typed lookup
for `Sig.Args`/`Vars`; do not introduce an untyped `Nat` arity fallback.

- [x] **Step 5: Implement generic and full models**

Create `VisualProof/Model.lean` with:

```lean
namespace PreModel

def Args (Domain : Sig → Type u) : List Sig → Type u
  | [] => PUnit
  | sig :: rest => Domain sig × Args Domain rest

def Args.toFull :
    Args (Sig.denote Carrier) sigs → Sig.Args Carrier sigs
  | [], PUnit.unit => PUnit.unit
  | _ :: _, ⟨head, tail⟩ => ⟨head, Args.toFull tail⟩

def Args.ofFull :
    Sig.Args Carrier sigs → Args (Sig.denote Carrier) sigs
  | [], PUnit.unit => PUnit.unit
  | _ :: _, ⟨head, tail⟩ => ⟨head, Args.ofFull tail⟩

end PreModel

structure PreModel where
  Domain : Sig → Type u
  inhabited : (sig : Sig) → Nonempty (Domain sig)
  apply : {args : List Sig} → Domain (.rel args) →
    PreModel.Args Domain args → Prop

mutual
  def PreModel.Args (Domain : Sig → Type u) : List Sig → Type u
    | [] => PUnit
    | sig :: rest => Domain sig × PreModel.Args Domain rest
end

structure Model where
  Carrier : Type u
  inhabited : Nonempty Carrier

def Model.toPreModel (model : Model) : PreModel where
  Domain := Sig.denote model.Carrier
  inhabited := Sig.denote_nonempty model.inhabited
  apply relation arguments := relation (PreModel.Args.toFull arguments)
```

Define `Env pre ctx := (sig : Sig) → Var ctx sig → pre.Domain sig`, typed
`Env.extend`, `Env.append`, and `Vars.denote`. Prove lookup laws for `here`,
`there`, append-left, and append-right. Prove:

```lean
theorem Model.reify (model : Model) (P : Sig.Args model.Carrier args → Prop) :
  ∃ relation : Sig.denote model.Carrier (.rel args),
    ∀ values, relation values ↔ P values
```

This theorem is the single fullness constructor later consumed by relational
sever/join.

- [x] **Step 6: Rebuild the root import and Lake target**

Replace `VisualProof.lean` with imports of `VisualProof.Data.Finite`,
`VisualProof.Sig`, and `VisualProof.Model`. Remove both obsolete executables from
`lakefile.toml`; Task 10 restores only the new step-tag executable.

- [x] **Step 7: Run GREEN gates**

Run:

```bash
lake build
npx vitest run tests/architecture/lean-semantics.test.ts
npm run formal:size
```

Expected: the minimal new library builds, the displaced vocabulary test passes,
and the retained/new sources remain below 3,000 lines.

- [x] **Step 8: Commit**

```bash
git add -A -- \
  VisualProof.lean \
  VisualProof \
  lakefile.toml \
  tests/architecture/lean-semantics.test.ts
git commit -m "refactor: replace the displaced Lean semantic core"
```

---

### Task 2: Define intrinsic diagrams and all-model denotation

**Files:**

- Create: `VisualProof/Diagram/Core.lean`
- Create: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof.lean`
- Test: `VisualProof/Diagram/Semantics.lean` executable examples

**Interfaces:**

- Consumes: `Sig`, `Var`, `Vars`, `PreModel`, `Model`, and `Env`.
- Produces:
  `DefVar`,
  `Region`,
  `Item`,
  `ItemSeq`,
  `denoteRegion`,
  `denoteItem`,
  `denoteItemSeq`,
  `AllEqual`,
  `Valid`,
  and `Entails`.

- [x] **Step 1: Add compile-failing semantic examples**

At the bottom of the new `VisualProof/Diagram/Semantics.lean`, first add examples
using the not-yet-defined API:

```lean
example : Valid blank := by simp [Valid, blank, denoteRegion]

example (x y : Var ctx sig) :
    denoteItem pre defs env (.identity sig [x, y] (by decide)) ↔
      env sig x = env sig y := by
  simp [denoteItem, AllEqual]

example (ports₁ ports₂ : List (Var ctx sig))
    (permutation : ports₁.Perm ports₂) :
    AllEqual (ports₁.map (env sig)) ↔ AllEqual (ports₂.map (env sig)) := by
  exact AllEqual.perm permutation
```

Run `lake build` and require failure on missing `Valid`, `blank`, or
`denoteItem`.

- [x] **Step 2: Implement the intrinsic syntax**

In `VisualProof/Diagram/Core.lean`, use one heterogeneous wire context. The
uniform `.bind` item binds one value of any signature; its `.rel` case is the
specification's higher-order bubble:

```lean
mutual
  structure Region (defs : List (List Sig)) (ctx : List Sig) where
    items : ItemSeq defs ctx

  inductive Item (defs : List (List Sig)) (ctx : List Sig)
    | atom (head : Var ctx (.rel args)) (arguments : Vars ctx args)
    | named (definition : DefVar defs args) (arguments : Vars ctx args)
    | identity (sig : Sig) (ports : List (Var ctx sig))
        (atLeastTwo : 2 ≤ ports.length)
    | cut (body : Region defs ctx)
    | bind (sig : Sig) (body : Region defs (sig :: ctx))

  inductive ItemSeq (defs : List (List Sig)) (ctx : List Sig)
    | nil
    | cons (head : Item defs ctx) (tail : ItemSeq defs ctx)
end
```

Define `DefVar` as an intrinsically signature-correct de Bruijn reference into
the ordered list of definition boundary signatures. Define `blank`, sequence
append, typed wire renaming, definition renaming, and binder-safe substitution.

- [x] **Step 3: Implement denotation**

Define `DefinitionEnv pre defs` as typed relation interpretations indexed by
`DefVar`; Task 3 adds the law tying those values to ordered definition bodies.
Define mutual denotation:

```lean
denoteItem pre definitions env (.atom head args) :=
  pre.apply (env _ head) (Vars.denote pre env args)

denoteItem pre definitions env (.named definition args) :=
  definitions.lookup definition (Vars.denote pre env args)

denoteItem pre definitions env (.identity sig ports _) :=
  AllEqual (ports.map (env sig))

denoteItem pre definitions env (.cut body) :=
  ¬ denoteRegion pre definitions env body

denoteItem pre definitions env (.bind sig body) :=
  ∃ value : pre.Domain sig,
    denoteRegion pre definitions (env.extend value) body
```

`ItemSeq` denotes conjunction and `Region` delegates to its sequence.

Define:

```lean
def Valid (diagram : Region defs []) : Prop :=
  ∀ (model : Model) (definitions : DefinitionEnv model.toPreModel defs),
    denoteRegion model.toPreModel definitions Env.empty diagram

def Entails (left right : Region defs []) : Prop :=
  ∀ (model : Model) (definitions : DefinitionEnv model.toPreModel defs),
    denoteRegion model.toPreModel definitions Env.empty left →
      denoteRegion model.toPreModel definitions Env.empty right
```

- [x] **Step 4: Prove unordered identity and binder laws**

Prove `AllEqual` reflexivity, append, union, and `List.Perm` invariance. Add
theorems for empty/singleton impossibility under the syntax proof, binary
identity, conjunction append, cut negation, binder existential, environment
renaming, and denotation under typed substitution.

- [x] **Step 5: Run GREEN gates and commit**

```bash
lake build
npx vitest run tests/architecture/lean-semantics.test.ts
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Diagram/Core.lean \
  VisualProof/Diagram/Semantics.lean
git commit -m "feat: define all-model diagram denotation"
```

---

### Task 3: Add open diagrams and ordered conservative definitions

**Files:**

- Create: `VisualProof/Diagram/Open.lean`
- Create: `VisualProof/Theory/Definition.lean`
- Create: `VisualProof/Theory/Semantics.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Consumes: intrinsic syntax and denotation.
- Produces:
  `OpenDiagram`,
  `BoundaryEnv`,
  `denoteOpen`,
  `Definition`,
  `Definitions`,
  `Definitions.signatures`,
  `Definitions.denote`,
  and `Definitions.lookup_denote`.

- [x] **Step 1: Add failing alias and dependency examples**

Add examples requiring:

```lean
example (open : OpenDiagram defs [.iota, .iota])
    (alias : open.boundaryAliases 0 1) (x y : pre.Domain .iota)
    (different : x ≠ y) :
    ¬ denoteOpen pre definitions open (x, (y, PUnit.unit)) := by
  exact open.reject_unequal_alias pre definitions alias different

example (defs : Definitions) (ref : DefVar defs.signatures args) :
    defs.denote model |>.lookup ref =
      defs.denoteDefinition model ref := by
  exact Definitions.lookup_denote defs model ref
```

Run `lake build`; expected failure on missing open/definition APIs.

- [x] **Step 2: Implement ordered, aliased boundaries**

`OpenDiagram defs args` stores:

```lean
structure OpenDiagram (defs : List (List Sig)) (args : List Sig) where
  classes : List Sig
  boundary : Vars classes args
  boundary_surjective :
    ∀ sig (class : Var classes sig), Vars.Contains boundary class
  body : Region defs classes
```

`denoteOpen` existentially chooses an `Env pre classes`, equates every ordered
boundary occurrence to the supplied `PreModel.Args pre.Domain args`, then
denotes `body`. Repeated boundary variables therefore enforce aliases without a
second equality representation.

- [x] **Step 3: Implement the dependent ordered definition store**

Use a snoc-list so each body can reference exactly its prior prefix:

```lean
inductive Definitions where
  | nil
  | snoc (prefix : Definitions) (args : List Sig)
      (body : OpenDiagram prefix.signatures args)
```

Define `Definitions.signatures`, weakening of earlier `DefVar`s, and recursive
`Definitions.denote (model : Model)`. The new definition's full-function-space
value is the predicate `denoteOpen` over the already-built prefix environment.
Also define `DefinitionLawful pre definitions env`, which states that every
stored relation value applies exactly when its open body denotes. Prove that
`Definitions.denote model` is lawful and prove lookup for the newest and
weakened earlier definitions.

- [x] **Step 4: Prove definition interpretation is model-parametric**

Prove that definition denotation depends only on the model, ordered prefix, and
boundary values; it is invariant under concrete identifiers and item order.
Generic fold/unfold theorems quantify over a `PreModel` plus
`DefinitionLawful`, rather than assuming representability. There is no
unconstrained named-relation valuation and no recursive/cyclic definition
constructor.

- [x] **Step 5: Run GREEN gates and commit**

```bash
lake build
npx vitest run tests/architecture/lean-semantics.test.ts
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Diagram/Open.lean \
  VisualProof/Theory/Definition.lean \
  VisualProof/Theory/Semantics.lean
git commit -m "feat: formalize ordered relation definitions"
```

---

### Task 4: Rebuild the checked concrete graph and elaboration bridge

**Files:**

- Create: `VisualProof/Diagram/Concrete/Core.lean`
- Create: `VisualProof/Diagram/Concrete/WellFormed.lean`
- Create: `VisualProof/Diagram/Concrete/Elaborate.lean`
- Create: `VisualProof/Diagram/Concrete/Isomorphism.lean`
- Create: `VisualProof/Diagram/Concrete/Examples.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  `ConcreteDiagram`,
  `CRegion`,
  `CNode`,
  `CPort`,
  `CEndpoint`,
  `CWire`,
  `WellFormed`,
  `WFError`,
  `CheckedDiagram`,
  `checkWellFormed`,
  `elaborate`,
  `ConcreteIso`,
  and `iso_denotation`.

- [x] **Step 1: Write failing executable fixtures**

Create concrete examples for:

1. a nullary relation atom;
2. a higher-order atom whose argument is a relation wire;
3. a three-port identity with permuted endpoint storage order;
4. a repeated boundary alias;
5. a malformed mixed-signature identity;
6. a wire whose scope does not enclose its endpoint.

Examples 1–4 must elaborate and have the expected denotation. Examples 5–6
must return exact `WFError` constructors. Run `lake build` and require failure
before implementing the checker.

- [x] **Step 2: Define the finite graph matching TypeScript**

Use separate `Fin` identifier types over stored counts. Define:

```lean
inductive CRegion (regionCount : Nat)
  | sheet
  | cut (parent : Fin regionCount)

inductive CNode (regionCount definitionCount : Nat)
  | atom (region : Fin regionCount) (args : List Sig)
  | ref (region : Fin regionCount) (definition : Fin definitionCount)
      (args : List Sig)
  | identity (region : Fin regionCount) (sig : Sig) (arity : Nat)

inductive CPort
  | head
  | arg (index : Nat)
  | identity (index : Nat)
```

`ConcreteDiagram` owns total region/node/wire tables, one root, typed wire
signatures, scopes, and endpoint lists. Identity indices are storage-only.

- [x] **Step 3: Define and decide one well-formedness proposition**

`WellFormed definitions diagram` must state:

- unique sheet root and every parent chain terminates there;
- definition indices and ref signatures agree;
- every node port exists and is covered exactly once;
- atom head is `rel(args)` and each positional argument matches;
- ref arguments match the stored definition signature;
- identity arity is at least two and every incident wire has its one homogeneous
  signature;
- every wire scope encloses every endpoint node;
- no duplicate endpoint occurrence.

`checkWellFormed` returns `Except WFError (CheckedDiagram definitions)` and must
prove preservation and iff:

```lean
theorem checkWellFormed_preserves_input
    (ok : checkWellFormed definitions diagram = .ok checked) :
    checked.val = diagram

theorem checkWellFormed_iff :
    (∃ checked,
      checkWellFormed definitions diagram = .ok checked ∧
      checked.val = diagram) ↔
      diagram.WellFormed definitions
```

- [x] **Step 4: Implement checked elaboration**

Elaboration recursively traverses the region tree. For each region it
deterministically nests `.bind` items for every wire scoped there, regardless of
signature, and converts atom/ref/identity/cut content using the typed visible
wire environment. Prove:

```lean
theorem elaborate_proof_irrelevant
    (left right : diagram.WellFormed definitions) :
    elaborateWith definitions diagram left =
      elaborateWith definitions diagram right

theorem elaborate_denotes_checked
    (checked : CheckedDiagram definitions) :
    denoteChecked pre definitionEnv checked =
      denoteRegion pre definitionEnv Env.empty (elaborate checked)
```

The enumeration order of co-scoped binders is nonsemantic and is discharged by
typed-renaming and existential-commutation lemmas.

- [x] **Step 5: Prove concrete isomorphism invariance**

`ConcreteIso` contains region/node/wire finite equivalences preserving root,
parentage, node kinds, ref identity, positional atom/ref ports, unordered
identity incidences, wire signatures/scopes, and endpoint incidence. Prove
elaboration and denotation invariance, including an explicit fixture where all
identity port indices and endpoint list orders are permuted.

- [x] **Step 6: Run GREEN gates and commit**

```bash
lake build
npx vitest run tests/architecture/lean-semantics.test.ts
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Diagram/Concrete/Core.lean \
  VisualProof/Diagram/Concrete/WellFormed.lean \
  VisualProof/Diagram/Concrete/Elaborate.lean \
  VisualProof/Diagram/Concrete/Isomorphism.lean \
  VisualProof/Diagram/Concrete/Examples.lean
git commit -m "feat: elaborate checked signature-indexed diagrams"
```

---

### Task 5: Formalize contexts, occurrences, extraction, and splice

**Files:**

- Create: `VisualProof/Diagram/Context.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Selection.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Occurrence.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Extract.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  `DiagramContext`,
  `context_mono`,
  `context_anti`,
  `context_equiv`,
  `CheckedSelection`,
  `Occurrence`,
  `extract`,
  `splice`,
  `denote_splice`,
  and `extract_splice_iso`.

- [x] **Step 1: Add failing context and splice examples**

Add compile-checked examples for positive monotonicity, negative
antitonicity, exact occurrence with repeated boundary aliases, and
extract-then-splice reconstruction. Require `lake build` to fail on the absent
theorems.

- [x] **Step 2: Implement intrinsic contexts and polarity**

Represent one typed hole with its cut depth and binder path. Prove by structural
induction:

```lean
theorem context_mono
    (even : context.cutDepth % 2 = 0)
    (entails : ∀ env, denote left env → denote right env) :
    denote (context.fill left) env → denote (context.fill right) env

theorem context_anti
    (odd : context.cutDepth % 2 = 1)
    (entails : ∀ env, denote left env → denote right env) :
    denote (context.fill right) env → denote (context.fill left) env
```

Equivalence transports at every depth.

- [x] **Step 3: Define checked selection and exact occurrence**

A selection is closed under descendant regions/nodes and internally scoped
wires. An `Occurrence pattern host` supplies injective region/node/wire maps,
preserves positional atom/ref ports, treats identity incidences as an unordered
multiset, preserves scopes and exact nested content, and reports ordered
boundary attachments including aliases. It validates evidence; it never
searches.

- [x] **Step 4: Implement extraction and capture-avoiding splice**

Extraction converts touching wires into ordered root boundary classes. Splice
maps those classes to supplied host wires, validates signatures and enclosure,
materializes identity when distinct attachments fill repeated boundary
positions, and normalizes only through the identity owner added in Task 6.

- [x] **Step 5: Prove semantic substitution and reconstruction**

Prove `denote_splice`, exact-occurrence denotation preservation, removal frame
semantics, and `extract_splice_iso`. These are the only subgraph semantic
theorems later rules may cite.

- [x] **Step 6: Run GREEN gates and commit**

```bash
lake build
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Diagram/Context.lean \
  VisualProof/Diagram/Concrete/Subgraph/Selection.lean \
  VisualProof/Diagram/Concrete/Subgraph/Occurrence.lean \
  VisualProof/Diagram/Concrete/Subgraph/Extract.lean \
  VisualProof/Diagram/Concrete/Subgraph/Splice.lean
git commit -m "feat: prove boundary-pinned splice semantics"
```

---

### Task 6: Prove identity normalization and substitution

**Files:**

- Create: `VisualProof/Rule/Identity.lean`
- Modify: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  `dropDegenerate`,
  `collapseCoScoped`,
  `fuseSameRegion`,
  `normalizeIdentities`,
  `normalizeIdentities_sound`,
  `IdentityRetarget`,
  and `identity_retarget_sound`.

- [x] **Step 1: Add failing identity theorem fixtures**

Add examples for:

- repeated incidences on one wire dropping as truth;
- every co-scoped wire collapsing to one quantified wire in positive and
  negative contexts;
- two same-region identities sharing a wire fusing to an unordered union;
- permutations of n-way identity ports yielding identical denotation;
- relation-sorted identity;
- identity-retargeted copy under a dominated site;
- refusal when the identity does not dominate the site.

Run `lake build`; expected failure on missing normalization/substitution
theorems.

- [x] **Step 2: Implement the three eager normalizations**

Mirror the TypeScript fixpoint owner over checked concrete diagrams. Return both
the normalized diagram and a typed wire-image map. Identity port indices may be
renumbered but never consulted semantically.

- [x] **Step 3: Prove each normalization equivalence**

Prove:

```lean
theorem dropDegenerate_sound
    (result : dropDegenerate source node = some target) :
    denoteChecked pre definitions target ↔
      denoteChecked pre definitions source

theorem collapseCoScoped_sound
    (result : collapseCoScoped source node = some target) :
    denoteChecked pre definitions target ↔
      denoteChecked pre definitions source

theorem fuseSameRegion_sound
    (result : fuseSameRegion source left right = some target) :
    denoteChecked pre definitions target ↔
      denoteChecked pre definitions source

theorem normalizeIdentities_sound :
  denoteChecked model definitions normalized ↔
    denoteChecked model definitions source
```

The co-scoped proof is the one-point rule and must cover both cut parities.

- [x] **Step 4: Prove identity-retargeted substitution**

`IdentityRetarget` names a boundary position, dominating identity node, source
wire, and target wire. Its checker proves homogeneous signature, incidence of
both wires, distinctness of wire identities, exact boundary attachment, and
dominance. Use `AllEqual` to prove endpoint value equality, then typed
denotation substitution for iteration and deiteration.

- [x] **Step 5: Integrate normalization into splice**

Every concrete constructor returns the normalized diagram plus wire transport.
Prove that composing splice soundness with the normalization receipt preserves
ordered boundary aliases.

- [x] **Step 6: Run GREEN gates and commit**

```bash
lake build
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Rule/Identity.lean \
  VisualProof/Diagram/Concrete/Subgraph/Splice.lean
git commit -m "feat: prove orderless identity transformations"
```

---

### Task 7: Prove structural rule soundness

**Files:**

- Create: `VisualProof/Rule/Tag.lean`
- Create: `VisualProof/Rule/Structural.lean`
- Create: `VisualProof/Diagram/Concrete/OpenCompilation.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Selection.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/SelectionFixtures.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Occurrence.lean`
- Create: `VisualProof/Diagram/Concrete/Subgraph/OccurrenceFixtures.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Extract.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Splice.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Reconstruction.lean`
- Correct: `VisualProof/Diagram/Concrete/Subgraph/Factorization*.lean`
- Correct: `VisualProof/Rule/Identity*.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  exact `StepTag`,
  `Orientation`,
  `Directed`,
  structural checked transformations,
  and their prestructure-generic soundness theorems.

- [ ] **Step 0: Correct the concrete selection and insertion authority**

Replace the Task 5 selection receipt that incorrectly selected its ambient
anchor and every descendant. Match the kernel's exact selection contract:

- `region` is an unselected ambient anchor;
- selected regions are direct child-subtree roots, with descendant closure
  derived internally;
- selected nodes are explicit direct anchor nodes plus nodes in selected
  subtrees;
- selected top-level wires are explicit anchor-scoped internal wires;
- all other internally scoped and touching wires are derived;
- extraction creates one ordered boundary stub per touching wire, not one per
  endpoint crossing.

Rebuild occurrence, extraction, removal, reconstruction, and factorization on
that sole authority. Generalize concrete splice attachment to an arbitrary
checked base diagram plus explicit site so the same constructor supports both
replacement and non-replacing insertion. Migrate Task 6 identity-retargeting
to the generalized splice without changing identity semantics or
normalization. Canonical selection extraction requires its ordered boundary to
equal the unique host-ordered touching-wire list; generic exact open-occurrence
reconstruction remains separate and preserves repeated ordered boundary
aliases. Add RED fixtures for partial direct-node selection, partial
child-subtree selection, explicit anchor-scoped internal wires, one boundary
class for a multiply incident touching wire, and a legal descendant target
outside the selected content. Delete the old root-selected/crossing-boundary
model; do not retain an adapter or parallel selection authority.

- [ ] **Step 1: Define the exact tag inventory and failing coverage theorem**

Define:

```lean
inductive StepTag
  | refSpawn | atomSpawn | identityInsert | wireJoin | erasure | wireSever
  | iteration | deiteration | doubleCutIntro | doubleCutElim | theorem
  | vacuousIntro | vacuousElim | unfold | fold
```

Define `StepTag.all` in that exact order. First state `all_length : all.length =
15` and `all_nodup`; run `lake build` RED until both are proved.

- [ ] **Step 2: Implement polarity-directed insertion and erasure**

Formalize negative forward / positive backward insertion for atom, ref, and
identity content. Formalize positive forward erasure only; the backward
constructor/checker returns an explicit orientation error. Prove soundness using
`context_mono`/`context_anti`, never a full-model witness.

- [ ] **Step 3: Implement ordinary and identity-retargeted copy rules**

Iteration non-destructively extracts the exact selection and splices it into
the same anchor or a descendant region outside the copied content.
Deiteration removes an explicitly selected inner copy only after checking an
exact ancestor justifier occurrence and ordered attachment correspondence.
Prove conjunction contraction/weakening through checker-derived concrete
factorizations and invoke Task 6 only for checked identity-retargeted
attachments. Freely constructed intrinsic contexts may be private proof
machinery but are not durable concrete rule receipts.

- [ ] **Step 4: Implement double-cut and vacuous wire rules**

Prove classical double-negation equivalence. Prove introduction/elimination of
an unused binder for every `Sig` from `PreModel.inhabited`; there is no special
relation-variable or bubble path.

- [ ] **Step 5: Add the complete orientation/polarity matrix examples**

Examples must accept:

- forward-negative insertion;
- backward-positive insertion;
- forward-positive erasure.

They must reject:

- forward-positive insertion;
- backward-negative insertion;
- backward erasure.

- [ ] **Step 6: Run GREEN gates and commit**

```bash
lake build
npm run formal:size
git add -- \
  docs/superpowers/plans/2026-07-27-zero-signature-hol-phase-3-lean-semantics.md \
  VisualProof.lean \
  VisualProof/Diagram/Concrete/Subgraph \
  VisualProof/Rule/Tag.lean \
  VisualProof/Rule/Structural.lean \
  VisualProof/Rule/Identity.lean \
  VisualProof/Rule/IdentityFixtures.lean \
  VisualProof/Rule/IdentityRetargetSemantics.lean
git commit -m "feat: prove structural rule soundness"
```

---

### Task 8: Prove strongest-form wire sever and join

**Files:**

- Create: `VisualProof/Rule/WireQuantifier.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  `ContentOccurrence`,
  `WireSeverInput`,
  `WireJoinInput`,
  `applyWireSever`,
  `applyWireJoin`,
  `iota_sever_sound`,
  `iota_join_sound`,
  `relation_sever_sound`,
  and `relation_join_sound`.

- [ ] **Step 1: Add failing strongest-form examples**

Create examples for:

- `ι` sever and comparable-scope join;
- relation sever over multiple disjoint mixed-parity exact copies with ordered
  formals and coherent ambient parameters;
- nullary content sever;
- relation join splicing one content into every applied endpoint;
- rejection of non-applied relation-wire endpoints;
- rejection of mismatched copies, formal order, parameters, or scope.

Run `lake build`; expected failure before the rule API exists.

- [ ] **Step 2: Implement the `ι` cases generically**

Mirror endpoint partition for sever and comparable-scope merge for join. Prove
their directed one-point quantifier laws over `PreModel`. No `Model.reify` call
is allowed in these proofs.

- [ ] **Step 3: Implement relation-content sever**

Each `ContentOccurrence` contains a checked exact selection and ordered formal
attachments. Validate disjointness, one boundary-pinned content shape, the same
ambient attachment vector, and parameter scopes enclosing the fresh wire scope.
Replace each copy by an atom headed by the new rel wire.

Prove soundness by calling `Model.reify` exactly once with the open content
predicate. Record this dependency in theorem arguments so the source audit can
verify that no other rule imports `Model.reify`.

- [ ] **Step 4: Implement relation-content join**

Require the quantified rel wire to have only applied-head endpoints. Validate
the content boundary signature and parameter scope, then splice the supplied
content at every atom and remove the emptied wire. Prove soundness by
instantiating the universal relation value with the content denotation.

- [ ] **Step 5: Prove the fullness boundary mechanically**

Add an audit theorem/module check that:

- `iota_sever_sound`, `iota_join_sound`, and every Task 6/7 theorem quantify
  over `PreModel`;
- only `relation_sever_sound` and `relation_join_sound` quantify over `Model`
  and invoke `Model.reify`.

- [ ] **Step 6: Run GREEN gates and commit**

```bash
lake build
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Rule/WireQuantifier.lean
git commit -m "feat: prove strongest wire quantifier soundness"
```

---

### Task 9: Prove definitions, citation, steps, replay, and theory soundness

**Files:**

- Create: `VisualProof/Rule/Definition.lean`
- Create: `VisualProof/Rule/Theorem.lean`
- Create: `VisualProof/Rule/Step.lean`
- Create: `VisualProof/Rule/Soundness.lean`
- Create: `VisualProof/Proof/Replay.lean`
- Create: `VisualProof/Proof/Theorem.lean`
- Create: `VisualProof/Proof/Theory.lean`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces:
  `ProofStep`,
  `applyStep`,
  `applyStep_sound`,
  `Proof`,
  `replay`,
  `replay_sound`,
  `backward_replay_sound`,
  `Theorem`,
  `checkTheorem`,
  `checkedTheorem_sound`,
  `Theory`,
  `verifyTheory`,
  and `verifiedTheory_sound`.

- [ ] **Step 1: Add failing public soundness examples**

State examples that replay one instance of every `StepTag`, a two-sided theorem
whose halves meet only up to concrete isomorphism and ordered boundary
transport, a theorem citation at both allowed polarities, and an ordered theory
where a later theorem cites an earlier theorem. Run `lake build` RED.

- [ ] **Step 2: Prove ref spawn and fold/unfold**

`refSpawn` inserts one named/ref item through the structural insertion gate.
`unfold` splices the selected ordered definition body onto the ref arguments;
`fold` checks a boundary-pinned exact occurrence and replaces it with the ref.
Prove both directions from `Definitions.lookup_denote` plus `denote_splice`.
They are equivalences at every context depth and never call sever/join.

- [ ] **Step 3: Prove cited theorem application**

A verified theorem stores ordered open LHS/RHS boundaries and semantic
entailment. Citation checks an exact pinned occurrence, applies LHS→RHS in a
positive context or RHS→LHS in a negative context, with gates flipped during
backward replay. Prove it through context polarity and splice, without inlining
the theorem's proof.

- [ ] **Step 4: Define the exact 15-payload `ProofStep` sum**

Each constructor carries the checked structural payload used by its owning
module. `applyStep` dispatches exhaustively and then composes identity
normalization plus boundary transport. Define:

```lean
def Directed (orientation : Orientation) (source target : CheckedDiagram defs) :=
  match orientation with
  | .forward => ∀ model, denoteChecked model source → denoteChecked model target
  | .backward => ∀ model, denoteChecked model target → denoteChecked model source
```

Prove `applyStep_sound` by exactly 15 cases. No default case and no theorem
whose premise is already `Directed source target`.

- [ ] **Step 5: Prove replay and two-sided theorem soundness**

Forward replay composes entailments from LHS. Backward replay composes reverse
entailments from RHS. `checkTheorem` independently transports every ordered
boundary after every step and requires the two results to be isomorphic. Prove
the exact registered LHS entails the exact registered RHS; the computed meeting
object is not substituted as the theorem endpoint.

- [ ] **Step 6: Prove ordered theory verification**

Definitions form the complete prefix before theorem registration. Theorems are
verified in sequence and may cite only their prior theorem prefix. Prove every
verified theorem semantically valid in every `Model`.

- [ ] **Step 7: Run GREEN gates and commit**

```bash
lake build
npm run formal:size
git add -- \
  VisualProof.lean \
  VisualProof/Rule/Definition.lean \
  VisualProof/Rule/Theorem.lean \
  VisualProof/Rule/Step.lean \
  VisualProof/Rule/Soundness.lean \
  VisualProof/Proof/Replay.lean \
  VisualProof/Proof/Theorem.lean \
  VisualProof/Proof/Theory.lean
git commit -m "feat: prove proof and theory soundness"
```

---

### Task 10: Restore truthful Lean correspondence and audit tooling

**Files:**

- Create: `VisualProof/Correspondence/StepTags.lean`
- Create: `VisualProof/Correspondence/StepTagsMain.lean`
- Create: `VisualProof/Audit.lean`
- Create: `scripts/check-lean-step-tags.mjs`
- Create: `scripts/check-formalization.mjs`
- Modify: `lakefile.toml`
- Modify: `package.json`
- Modify: `tests/architecture/lean-semantics.test.ts`
- Modify: `VisualProof.lean`

**Interfaces:**

- Produces executable `visualproof_step_tags`.
- Produces supported `npm run formal:tags` and `npm run formal:check`.

- [ ] **Step 1: Write failing tooling tests**

Extend `tests/architecture/lean-semantics.test.ts` to require:

- package scripts `formal:tags` and `formal:check`;
- both checker scripts;
- exactly one Lean executable, `visualproof_step_tags`;
- no `visualproof_match_fixtures`;
- the complete exact 15-tag output.

Run the test and require failure because the tooling is absent.

- [ ] **Step 2: Serialize the exact Lean inventory**

Implement `StepTag.serializedName`, `serializedAll`, injectivity, length 15, and
nodup. `StepTagsMain` prints one serialized tag per line.

- [ ] **Step 3: Rebuild the cross-language tag checker**

`scripts/check-lean-step-tags.mjs` must:

1. parse only the `rule: '…'` discriminants from the exported TypeScript
   `ProofStep` union;
2. run `lake env visualproof_step_tags`;
3. reject duplicates on either side;
4. require exact set equality and report missing/extra tags;
5. require the fixed 15-tag count.

It must not hard-code the TypeScript list separately.

- [ ] **Step 4: Add proof-authority audits**

`VisualProof/Audit.lean` imports all central soundness modules and uses
`#print axioms` for:

- `normalizeIdentities_sound`;
- `identity_retarget_sound`;
- both relation sever/join theorems;
- `applyStep_sound`;
- `replay_sound`;
- `checkedTheorem_sound`;
- `verifiedTheory_sound`.

`scripts/check-formalization.mjs` must fail on repository-owned Lean source
containing `sorry`, `admit`, custom `axiom`, `Lambda`, beta/eta, comprehension,
the deleted rule names, or Phase-4 reference syntax. It then runs:

```text
npm run formal:size
lake build
npm run formal:tags
npm run typecheck
npx vitest run tests/architecture/lean-semantics.test.ts
```

The audit accepts Lean's standard classical axioms but rejects `sorryAx` or any
project-defined axiom in `Audit.lean` output.

- [ ] **Step 5: Restore package and Lake commands**

Add:

```json
"formal:tags": "node scripts/check-lean-step-tags.mjs",
"formal:check": "node scripts/check-formalization.mjs"
```

Add only `visualproof_step_tags` to `lakefile.toml`.

- [ ] **Step 6: Run GREEN gates and commit**

```bash
npm run formal:tags
npm run formal:check
npx vitest run tests/architecture/lean-semantics.test.ts
git diff --check
git add -- \
  VisualProof.lean \
  VisualProof/Audit.lean \
  VisualProof/Correspondence/StepTags.lean \
  VisualProof/Correspondence/StepTagsMain.lean \
  scripts/check-lean-step-tags.mjs \
  scripts/check-formalization.mjs \
  lakefile.toml \
  package.json \
  tests/architecture/lean-semantics.test.ts
git commit -m "build: restore zero-signature formal checks"
```

---

### Task 11: Clean-build audit and complete Phase 3 gates

**Files:**

- Modify only if a gate exposes a defect:
  the exact owner named by the failing theorem or checker
- Append conformance:
  `/tmp/vpa-phase3-lean-plan-foundation-20260727.md`

- [ ] **Step 1: Prove the legacy hierarchy is absent**

Run:

```bash
test ! -d VisualProof/Lambda
test ! -d VisualProof/Rule/Soundness/Comprehension
rg -n \
  "LambdaModel|Item\\.equation|openTermSpawn|conversion|congruenceJoin|headStrip|closedTermIntro|fusion|fission|comprehensionInstantiate|comprehensionAbstract|inconsistentCut" \
  VisualProof VisualProof.lean lakefile.toml package.json scripts tests/architecture
```

Expected: no positive authority match. Negative audit patterns must be
contextually identified as negative assertions.

- [ ] **Step 2: Prove Phase 4 has not started**

```bash
test ! -e VisualProof/HOL
rg -n "denotation-preservation|translateHOL|ReferenceHOL|Henkin" VisualProof
```

Expected: no files or declarations.

- [ ] **Step 3: Run a clean Lean build**

```bash
lake clean
lake build
npm run formal:check
```

The clean build proves no cached legacy object is satisfying an import.

- [ ] **Step 4: Run complete repository gates**

```bash
npm test
npm run e2e
npm run typecheck
npm run formal:size
git diff --check
git status --short
```

Expected: every gate passes; only unrelated pre-existing `archive/` and
`scratchpad/` paths may remain untracked.

- [ ] **Step 5: Append foundation conformance**

Append `<conformance>` to
`/tmp/vpa-phase3-lean-plan-foundation-20260727.md` recording:

- the retained generic finite owner;
- every displaced hierarchy deleted;
- the final signature/model/diagram/rule/proof owners;
- the exact 15-tag parity result;
- proof-authority audit results;
- the two fullness-dependent theorem names;
- clean Lean build, full npm/E2E/typecheck, and diff/status results;
- explicit evidence that Phase 4 is absent.

- [ ] **Step 6: Commit any gate-owned correction**

If Step 1–4 required a correction, stage only its exact owner and commit:

```bash
git add -- <exact-corrected-paths>
git commit -m "fix: complete zero-signature Lean semantics"
```

If no tracked correction exists, do not create an empty commit.

## Acceptance Matrix

| Requirement | Direct evidence |
|---|---|
| No Lambda/computation layer | Task 1 deletion + Task 10/11 audits |
| Recursive full higher-type domains | `Sig.denote`, `Model.toPreModel`, `Model.reify` |
| Nonempty individual carrier | `Model.inhabited` |
| Atom/ref/cut/higher-order binder semantics | Task 2 denotation examples |
| Unordered n-ary identity at every sort | Tasks 2, 4, and 6 permutation theorems |
| Truth in all models | `Valid`/`Entails` |
| Three identity normalizations | `normalizeIdentities_sound` |
| Orientation-aware insertion/erasure | Task 7 matrix |
| Identity substitution | `identity_retarget_sound` |
| Definitional splice transparency | `unfold_sound`, `fold_sound` |
| Strongest relation sever/join | Task 8 mixed-parity/parameter fixtures |
| Fullness used only by sever/join | Task 8 API + Task 10 audit |
| All 15 primitive steps sound | `applyStep_sound` exhaustive cases |
| Forward/backward replay sound | `replay_sound`, `backward_replay_sound` |
| Exact registered theorem endpoints | `checkedTheorem_sound` |
| Ordered theory/citation sound | `verifiedTheory_sound` |
| TS/Lean inventory parity | `npm run formal:tags` |
| No Phase-4 work | Task 11 absence gate |
