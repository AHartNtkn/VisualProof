# Recursive Rewrite Authority Implementation Plan

> **Execution:** Use `superpowers:subagent-driven-development` with one bounded worker task at a time, followed by plan-compliance and code-quality review. Track the same tasks in the GoalBuddy board.

**Goal:** Make recursive diagrams, relational rewrite rules, and recursively defined semantics the mathematical authority. Flat diagrams and executable rewriting are correct exactly when translation and execution refine that authority.

**Stack:** Lean 4, Lake, the existing `VisualProof` package.

## Non-negotiable architecture

- `Region` is the only recursive diagram syntax.
- `OpenDiagram arity` is a nonrecursive mathematical interface: one `Region externalClasses []`, an ordered map from `Fin arity` boundary positions to external wire classes, and surjectivity. Repeated positions may alias; order and multiplicity are preserved.
- Rule-specific mathematics is stated over `Region` whenever no ordered boundary fact is involved. Rules that can change the boundary quotient are stated directly over `OpenDiagram`.
- A local occurrence is evidence that a recursive host body is isomorphic to a typed `DiagramContext` filled with a `Region`. It is not a search result.
- Every rule is a proposition-valued relation. The recursive mathematical inventory is exactly `Erasure`, `WireSever`, `Iteration`, `DoubleCut`, `Comprehension`, and `Vacuity`. `Comprehension` and its standalone soundness theorem remain available as recursive mathematics but are not members of the actual `Rule.Step` ruleset.
- Each pair has one positive-context relation. A negative controlling context uses its converse. `Iteration`, `DoubleCut`, and `Vacuity` may admit both directions at either polarity only after their base transformation is proved semantically invertible.
- Abstract relations and `Rule.Step` have no execution orientation. `Step source target` means the ordinary implication from `source` to `target`.
- Concrete execution has exactly ten operation constructors: `boundRelationSpawn`, `wireJoin`, `erasure`, `wireSever`, `iteration`, `deiteration`, `doubleCutIntro`, `doubleCutElim`, `vacuousIntro`, and `vacuousElim`. Abstraction and instantiation have no concrete request, payload, tag, executor branch, receipt theorem, refinement theorem, completeness theorem, or rejection branch.
- The concrete operation split does not define the abstract rule split. Refinement maps each operation to the base relation or its converse at the one controlling region polarity.
- Lean contains no occurrence matcher, search status, candidate enumeration, search frontier, or matcher theorem. Requests contain the selected finite data and proofs that execution consumes.
- `Concrete.translate` is the public fallible conversion from unchecked flat open syntax. `Represents` is its graph modulo `OpenDiagramIso`.
- Representation completeness and one-step execution completeness are required for the whole calculus.
- `Rule.Step.sound` has no dependency on flat diagrams, translation, execution, errors, receipts, compiler traversal, or carrier numbering.
- `Concrete/**` and `Refinement/**` are syntactic layers. Their declarations may establish validation, translation, representation, structural isomorphism, execution refinement, completeness, and rejection correctness, but may not mention models, denotation, semantic implication, `Rule.Step.sound`, or rule soundness.
- Concrete-dependent semantic validity exists only under `Proof/**`. It is a thin composition of `Refinement.execute_sound`, `Rule.Step.sound`, and representation/isomorphism transport; it contains no request-family case split or rule-specific semantic argument.
- Dependency purity is bidirectional: recursive rule soundness imports no concrete/refinement implementation, and concrete/refinement import closures contain no semantic modules or semantic authority.
- TypeScript is outside implementation and validation scope.
- Do not introduce names prefixed with `Direct`, `Directed`, `Abstract`, or `Recursive` merely to distinguish the new authority.
- No compatibility aliases, transitional public wrappers, or parallel semantic authorities remain after their owning migration task.

## Completeness consequences

Two implementation changes follow logically from the required theorems.

1. Execution operates on checked open states, not only closed checked diagrams. Otherwise `execute_complete` can cover only arity zero.
2. The constructor named `boundRelationSpawn` must accept a supplied checked open diagram and insertion occurrence sufficient to realize the full converse of `Erasure`. Its present atom-only payload cannot realize arbitrary negative-context insertion, so keeping that payload would make one-step execution completeness false. The ten-constructor roster and constructor name stay fixed; this constructor's payload becomes general enough for its assigned relation.

Iteration remains a one-selected-occurrence/one-target transformation, matching the existing operation. The abstract relation does not invent a simultaneous list operation.

## Interface precision rule

Code blocks below are acceptance signatures, not sketches. Every identifier in a block either already exists or is introduced earlier in the plan. Prose describing an internal witness is a mathematical construction requirement, not purported Lean syntax. Its owning Worker must complete and compile that definition, then obtain review, before any theorem using it enters RED.

Lean's indexed `Fin` and `RelVar` syntax provides scope and capture safety. Do not add a name-based freshness predicate unless a later mathematical statement actually requires names and supplies freshness for both the context and the inserted term.

## Final module ownership

| Layer | Modules | Responsibility |
|---|---|---|
| Diagram | structural diagram modules plus separately owned semantic modules | Recursive syntax, open interface, renaming, isomorphism, contexts, occurrence evidence, and separately layered denotation |
| Rules | `VisualProof/Rule/{Relation,Erasure,WireSever,Iteration,DoubleCut,Comprehension,Vacuity,Step,Soundness}.lean` and family soundness modules | Six recursive relations and their soundness; the actual `Step` union contains the five executable rule families and excludes standalone `Comprehension` |
| Concrete | `VisualProof/Concrete/{Diagram,Open,WellFormed,Translate,Occurrence,Step}.lean` plus implementation submodules | Flat syntax, checking, supplied selections, compilation, and execution; no semantics |
| Refinement | `VisualProof/Refinement/{Represents,Step,Complete,Rejection}.lean` plus structural family submodules | Translation/encoding laws, structural execution refinement/completeness, and rejection correctness; no semantics |
| Proof | `VisualProof/Proof/{Replay,Schema,Theorem,Theory}.lean` | The only concrete-execution semantic validity, inherited compositionally from refinement and `Step.sound` |

## Theorem-development protocol

For every owning theorem:

1. Complete and compile every definition in its dependency closure.
2. Add `by sorry` only as that theorem's proof and compile with `-DwarningAsError=false` to establish RED.
3. Confirm the only new `sorry` is that theorem proof.
4. Replace it with a kernel-checked proof and compile with `-DwarningAsError=true` for GREEN.
5. Run the task's broader build and source scan before committing.

No fixture theorem, `example`, or `#check` is added to simulate RED/GREEN.

---

### Task 1: Stabilize the diagram kernel and generic open lift

**Files:**

- Modify `VisualProof/Diagram/Boundary.lean`
- Modify `VisualProof/Diagram/Isomorphism.lean`
- Modify `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify `VisualProof/Diagram/Semantics.lean`

**Work:**

- Add `OpenDiagram.withBody`, preserving `externalClasses`, `boundary`, and `boundary_surjective` definitionally.
- Add `BoundaryAssignment.equal_of_alias`.
- Retain the existing `Core.Isomorphic` relation and its existing reflexive, symmetric, transitive, and denotation results. Add only missing congruence theorems for the existing `Region.renameWires` and `Region.renameRelations`; there is no generic `Region.substitute` operation.
- Retain `OpenDiagramIso.denoteOpen_iff`; do not recreate it under another name.
- Add the one unchanged-interface semantic lift:

```lean
theorem OpenDiagram.denote_body
    {diagram : OpenDiagram arity}
    {before after : Region diagram.externalClasses []}
    {model : Model}
    {args : Fin arity → model.Carrier}
    (h : ∀ env : Fin diagram.externalClasses → model.Carrier,
      denoteRegion model env PUnit.unit before →
      denoteRegion model env PUnit.unit after) :
    denoteOpen model (diagram.withBody before) args →
    denoteOpen model (diagram.withBody after) args
```

Prove the analogous `denote_body_iff` with an `↔` premise and conclusion.

**Validation:**

```bash
lake env lean -DwarningAsError=true VisualProof/Diagram/Boundary.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/Isomorphism.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/OpenIsomorphism.lean
lake env lean -DwarningAsError=true VisualProof/Diagram/Semantics.lean
lake build
git diff --check
```

Commit only these paths as `Establish recursive diagram interface laws`.

### Task 2: Complete contexts, polarity, and occurrence evidence

**Files:**

- Modify `VisualProof/Diagram/Context.lean`
- Modify `VisualProof/Diagram/ContextReachability.lean`
- Modify `VisualProof/Diagram/Rename.lean`
- Modify `VisualProof/Diagram/Algebra.lean`
- Modify `VisualProof/Diagram/Isomorphism.lean`
- Modify `VisualProof/Diagram/OpenIsomorphism.lean`
- Create `VisualProof/Diagram/Occurrence.lean`
- Modify `VisualProof.lean`

**Definitions:**

```lean
def RelationRenaming.weaken (head : Nat) :
    RelationRenaming rels (head :: rels) :=
  fun relation => ⟨relation.index.succ, relation.hasArity⟩

def RelationRenaming.empty :
    RelationRenaming [] rels :=
  fun relation => Fin.elim0 relation.index

inductive Polarity
  | positive
  | negative

def DiagramContext.polarity
    (context : DiagramContext outerWires holeWires outerRels holeRels) :
    Polarity :=
  if context.cutDepth % 2 = 0 then .positive else .negative

def DiagramContext.outerRelation :
    (context :
      DiagramContext outerWires holeWires outerRels holeRels) →
    RelationRenaming outerRels holeRels
  | .hole => fun relation => relation
  | .cut _ _ _ child => child.outerRelation
  | .bubble _ _ _ arity child =>
      fun relation =>
        child.outerRelation
          (RelationRenaming.weaken arity relation)

structure Occurrence
    (pattern : Region holeWires holeRels)
    (host : OpenDiagram arity) where
  interface : OpenDiagram arity
  context : DiagramContext interface.externalClasses holeWires [] holeRels
  host_iso : OpenDiagramIso host
    (interface.withBody (context.fill pattern))
```

Introduce `RelationRenaming.weaken` and `RelationRenaming.empty` in `Rename.lean`. Move the existing `DiagramContext.outerRelation` from `ContextReachability.lean` into `Context.lean`; do not duplicate it. Update `ContextReachability.lean` to consume the moved declaration.

**Theorems:**

- Keep `DiagramContext.fill_equiv` as the existing semantic equivalence theorem. Separately prove structural transport in `Isomorphism.lean`, which already sits above `Context.lean` in the import graph:

```lean
theorem DiagramContext.fill_iso
    (context : DiagramContext outerWires holeWires outerRels holeRels)
    {before after : Region holeWires holeRels}
    (h : Core.Isomorphic before after) :
    Core.Isomorphic (context.fill before) (context.fill after)
```

Prove unchanged-interface transport in `OpenIsomorphism.lean`:

```lean
def OpenDiagram.withBody_iso
    {diagram : OpenDiagram arity}
    {before after : Region diagram.externalClasses []}
    (h : Core.Isomorphic before after) :
    OpenDiagramIso
      (diagram.withBody before)
      (diagram.withBody after)
```

Package the existing `context_mono` and `context_anti` results:

```lean
theorem DiagramContext.denote_fill
    (context :
      DiagramContext outerWires holeWires outerRels holeRels)
    {before after : Region holeWires holeRels}
    (model : Model)
    (h : ∀
      (env : Fin holeWires → model.Carrier)
      (rels : RelEnv model.Carrier holeRels),
      denoteRegion model env rels before →
      denoteRegion model env rels after) :
    ∀ (env : Fin outerWires → model.Carrier)
      (rels : RelEnv model.Carrier outerRels),
      match context.polarity with
      | .positive =>
          denoteRegion model env rels (context.fill before) →
          denoteRegion model env rels (context.fill after)
      | .negative =>
          denoteRegion model env rels (context.fill after) →
          denoteRegion model env rels (context.fill before)
```

Prove occurrence transport:

```lean
def Occurrence.transportHost
    (occurrence : Occurrence pattern host)
    (iso : OpenDiagramIso host host') :
    Occurrence pattern host'

def Occurrence.transportPattern
    (occurrence : Occurrence pattern host)
    (iso : Core.Isomorphic pattern pattern') :
    Occurrence pattern' host
```

`transportHost` retains `occurrence.interface` and `occurrence.context` and composes `iso.symm` with `occurrence.host_iso`. This is why the occurrence owns an independent interface carrier rather than indexing its context by `host.externalClasses`: an open isomorphism may permute external classes. `transportPattern` uses `DiagramContext.fill_iso` and `OpenDiagram.withBody_iso` on that same interface.

Do not assert occurrence uniqueness.
- Express every capture claim through typed wire/relation renaming. No `FreshFor` declaration or theorem is introduced.

**Validation:** compile all six paths separately, run `lake build`, `git diff --check`, scan the modified dependency closure for `sorry`, and commit them as `Define recursive occurrence evidence`.

### Task 3: Define shared relational infrastructure

**Files:**

- Create `VisualProof/Rule/Relation.lean`
- Modify `VisualProof.lean`

**Definitions:**

```lean
abbrev LocalRule : Type :=
  ∀ {wires : Nat} {rels : RelCtx},
    Region wires rels → Region wires rels → Prop

abbrev Rule : Type :=
  ∀ {arity : Nat},
    OpenDiagram arity → OpenDiagram arity → Prop

def converse (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation after before

def symmetric (relation : α → α → Prop) : α → α → Prop :=
  fun before after => relation before after ∨ relation after before

def atPolarity (polarity : Polarity)
    (relation : α → α → Prop) : α → α → Prop :=
  match polarity with
  | .positive => relation
  | .negative => converse relation

def Contextual (local : LocalRule) : Rule :=
  fun {arity} source target =>
    ∃ (wires : Nat) (rels : RelCtx)
      (before after : Region wires rels)
      (occurrence : Occurrence before source)
      (_targetIso : OpenDiagramIso target
        (occurrence.interface.withBody
          (occurrence.context.fill after))),
      atPolarity occurrence.context.polarity
        (@local wires rels) before after
```

Add relation and contextual isomorphism transport. Do not define `Step` yet.

**Validation:** compile `Relation.lean`, build, scan the new file for `sorry`, and commit as `Define relational rewrite infrastructure`.

### Task 4: Define all six rule bases completely

**Files:**

- Create `VisualProof/Rule/Erasure.lean`
- Create `VisualProof/Rule/WireSever.lean`
- Create `VisualProof/Rule/Iteration.lean`
- Create `VisualProof/Rule/DoubleCut.lean`
- Create `VisualProof/Rule/Comprehension/Relation.lean`
- Create `VisualProof/Rule/Vacuity.lean`
- Keep `VisualProof/Rule/Comprehension.lean` as standalone recursive mathematics: its relation, isomorphism transport, and soundness remain in Rule and have no Concrete or Refinement execution destination

This task defines the noninvertible family relations and the bases of the three invertible families. It contains no semantic theorem and imports no concrete module.

#### Erasure

```lean
namespace Erasure

inductive Local : LocalRule
  | erase
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (material : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems material wireMap relationMap)
        (.mk hostLocal hostItems)

end Erasure

def Erasure : Rule :=
  Contextual Erasure.Local

theorem Erasure.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Erasure source target)
    (targetIso : OpenDiagramIso target target') :
    Erasure source' target'
```

`spliceAt` is the recursive gluing operation: erased material may refer to the
site's retained local witnesses and lexical relations.  No injectivity is
required of either map.  This is essential for ordinary selected subdiagrams
that touch a retained anchor-local wire; `conjoin` is only the disjoint special
case.

#### Wire severing

Define the collapse that identifies the newly added local wire with the selected existing wire:

```lean
namespace WireSever

def collapseLocal
    (wires localWires : Nat)
    (joined : Fin (wires + localWires)) :
    Fin (wires + (localWires + 1)) →
      Fin (wires + localWires)
```

`collapseLocal` is identity on the old prefix and maps the final fresh wire to `joined`.

```lean
inductive Local : LocalRule
  | sever
      (joined : Fin (wires + localWires))
      (separate :
        ItemSeq (wires + (localWires + 1)) rels) :
      Local
        (.mk localWires
          (separate.renameWires
            (collapseLocal wires localWires joined)))
        (.mk (localWires + 1) separate)

structure Open
    (source target : OpenDiagram arity) where
  one_more :
    target.externalClasses = source.externalClasses + 1
  collapse :
    Fin target.externalClasses →
      Fin source.externalClasses
  collapse_surjective :
    Function.Surjective collapse
  boundary :
    ∀ position,
      collapse (target.boundary position) =
        source.boundary position
  body :
    Core.Isomorphic source.body
      (target.body.renameWires collapse)

end WireSever

def WireSever : Rule :=
  fun source target =>
    Contextual WireSever.Local source target ∨
      Nonempty (WireSever.Open source target)

theorem WireSever.iso
    (sourceIso : OpenDiagramIso source source')
    (step : WireSever source target)
    (targetIso : OpenDiagramIso target target') :
    WireSever source' target'
```

The local constructor permits any partition of the joined wire's occurrences: renaming both separated classes through `collapseLocal` recovers the joined source. The open constructor is required because `source.withBody` cannot express a changed boundary alias partition. `one_more` and the surjective collapse say that exactly one external class has been split independently of class numbering; `boundary` preserves ordered positions while allowing their alias partition to become finer.

#### Iteration base

Iteration uses a separate interface carrier so endpoint isomorphism transport does not depend on either endpoint's external-class numbering:

```lean
namespace Iteration

structure Base
    (source target : OpenDiagram arity) where
  interface : OpenDiagram arity
  ancestorWires : Nat
  anchorLocal : Nat
  descendantWires : Nat
  ancestorRels : RelCtx
  descendantRels : RelCtx
  outer :
    DiagramContext interface.externalClasses ancestorWires
      [] ancestorRels
  descendant :
    DiagramContext (ancestorWires + anchorLocal) descendantWires
      ancestorRels descendantRels
  selected :
    Region (ancestorWires + anchorLocal) ancestorRels
  remainder :
    Region descendantWires descendantRels
  source_iso :
    OpenDiagramIso source
      (interface.withBody
        (outer.fill
          (Region.adjoinAt anchorLocal .nil
            (selected.conjoin
              (descendant.fill remainder)))))
  target_iso :
    OpenDiagramIso target
      (interface.withBody
        (outer.fill
          (Region.adjoinAt anchorLocal .nil
            (selected.conjoin
              (descendant.fill
                (((selected.renameWires descendant.outerWire)
                    .renameRelations descendant.outerRelation)
                  .conjoin remainder))))))

def Base.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Base source target)
    (targetIso : OpenDiagramIso target target') :
    Base source' target'

end Iteration
```

`anchorLocal` binds the anchor-scoped witnesses once around both factors.
Inside that binder block, selected and retained material share the full
`ancestorWires + anchorLocal` carrier; witnesses owned only by the selected
factor may remain local to `selected`.  This includes hidden root wires, which
are recursive root locals rather than open external classes.

There is one selected occurrence and one target. Do not define `Iteration` until Task 5 proves `Iteration.Base.sound_iff`.

#### Double-cut base

```lean
namespace DoubleCut

def wrap (body : Region wires rels) :
    Region wires rels :=
  .mk 0
    (.cons
      (.cut (.mk 0 (.cons (.cut body) .nil)))
      .nil)

inductive Local : LocalRule
  | introduce
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems body wireMap relationMap)
        (Region.spliceAt hostLocal hostItems (wrap body) wireMap relationMap)

end DoubleCut
```

Do not define `DoubleCut` until Task 5 proves `DoubleCut.Local.sound_iff`.

#### Comprehension instantiation

Define closed open diagrams as semantic relations:

```lean
def OpenDiagram.asRelation
    (model : Model)
    (pattern : OpenDiagram arity) :
    Relation model.Carrier arity :=
  fun args => denoteOpen model pattern args
```

Define the structural mapping used while removing the newly bound head relation:

```lean
namespace Comprehension

inductive Image (targetRels : RelCtx) : Nat → Type
  | variable
      (relation : RelVar targetRels arity) :
      Image targetRels arity
  | diagram
      (pattern : OpenDiagram arity) :
      Image targetRels arity

abbrev Mapping (sourceRels targetRels : RelCtx) :=
  {arity : Nat} →
    RelVar sourceRels arity →
    Image targetRels arity

def Image.weaken
    (head : Nat)
    {arity : Nat} :
    Image targetRels arity →
      Image (head :: targetRels) arity
  | .variable relation =>
      .variable
        (RelationRenaming.weaken head relation)
  | .diagram pattern =>
      .diagram pattern

def Mapping.lift
    (mapping : Mapping sourceRels targetRels)
    (head : Nat) :
    Mapping (head :: sourceRels) (head :: targetRels)

def Mapping.instantiateHead
    (pattern : OpenDiagram relationArity) :
    Mapping (relationArity :: rels) rels

def singleton
    (item : Item wires rels) :
    Region wires rels :=
  .mk 0 (.cons item .nil)
```

`Mapping.lift` maps the newly nested head variable to itself and applies `Image.weaken` to inherited variables. `Mapping.instantiateHead` maps the distinguished head to `.diagram pattern` and each tail variable to its predecessor in `rels`; its head case transports `pattern` with `OpenDiagram.castArity` when required by the dependent equality in `RelVar`.

A substituted item returns a `Region`, because a relation atom may expand to an arbitrary open diagram:

```lean
namespace Instantiation

mutual
  inductive RegionResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      Region wires sourceRels →
      Region wires targetRels →
      Prop
    | mk
        {mapping : Mapping sourceRels targetRels}
        {localWires : Nat}
        {items : ItemSeq (wires + localWires) sourceRels}
        {result : Region (wires + localWires) targetRels}
        (items_result :
          ItemsResult mapping items result) :
        RegionResult mapping
          (.mk localWires items)
          (Region.adjoinAt localWires .nil result)

  inductive ItemsResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      ItemSeq wires sourceRels →
      Region wires targetRels →
      Prop
    | nil
        {mapping : Mapping sourceRels targetRels} :
        ItemsResult mapping .nil Region.blank
    | cons
        {mapping : Mapping sourceRels targetRels}
        {item : Item wires sourceRels}
        {tail : ItemSeq wires sourceRels}
        {itemResult tailResult : Region wires targetRels}
        (item_result :
          ItemResult mapping item itemResult)
        (tail_result :
          ItemsResult mapping tail tailResult) :
        ItemsResult mapping
          (.cons item tail)
          (itemResult.conjoin tailResult)

  inductive ItemResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      Item wires sourceRels →
      Region wires targetRels →
      Prop
    | atomVariable
        {mapping : Mapping sourceRels targetRels}
        {arity : Nat}
        {relation : RelVar sourceRels arity}
        {arguments : Fin arity → Fin wires}
        (mapped : RelVar targetRels arity)
        (image :
          mapping relation = Image.variable mapped) :
        ItemResult mapping
          (.atom relation arguments)
          (singleton (.atom mapped arguments))

    | atomDiagram
        {mapping : Mapping sourceRels targetRels}
        {arity : Nat}
        {relation : RelVar sourceRels arity}
        {arguments : Fin arity → Fin wires}
        (pattern : OpenDiagram arity)
        (image :
          mapping relation = Image.diagram pattern)
        (assignment :
          BoundaryAssignment pattern (Fin wires))
        (arguments_eq :
          assignment.args = arguments) :
        ItemResult mapping
          (.atom relation arguments)
          ((pattern.substituteBoundary assignment).renameRelations
            RelationRenaming.empty)

    | identity
        {mapping : Mapping sourceRels targetRels}
        (arity : Nat)
        (arguments : Fin arity → Fin wires) :
        ItemResult mapping
          (.identity arity arguments)
          (singleton (.identity arity arguments))

    | cut
        {mapping : Mapping sourceRels targetRels}
        {body : Region wires sourceRels}
        {result : Region wires targetRels}
        (body_result :
          RegionResult mapping body result) :
        ItemResult mapping
          (.cut body)
          (singleton (.cut result))

    | bubble
        {mapping : Mapping sourceRels targetRels}
        (arity : Nat)
        {body : Region wires (arity :: sourceRels)}
        {result : Region wires (arity :: targetRels)}
        (body_result :
          RegionResult (mapping.lift arity) body result) :
        ItemResult mapping
          (.bubble arity body)
          (singleton (.bubble arity result))
end

end Instantiation

def Instantiates
    (pattern : OpenDiagram relationArity)
    (quantified : Region wires (relationArity :: rels))
    (specialized : Region wires rels) :
    Prop :=
  Instantiation.RegionResult
    (Mapping.instantiateHead pattern)
    quantified specialized

inductive Local : LocalRule
  | rewrite
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (arity : Nat)
      (pattern : OpenDiagram arity)
      (body : Region materialWires (arity :: materialRels))
      (specialized : Region materialWires materialRels)
      (instantiates : Instantiates pattern body specialized)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems specialized wireMap relationMap)
        (Region.spliceAt hostLocal hostItems
          (singleton (.bubble arity body)) wireMap relationMap)

end Comprehension

def Comprehension : Rule :=
  Contextual Comprehension.Local

theorem Comprehension.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Comprehension source target)
    (targetIso : OpenDiagramIso target target') :
    Comprehension source' target'
```

`RegionResult.mk` retains the quantified body's original local-wire block and appends local wires introduced by expanded patterns through `Region.adjoinAt`. `ItemsResult.cons` supplies simultaneous replacement without an executable occurrence search.
The `spliceAt` host frame retains unselected siblings and permits the selected
material to share anchor-local witnesses.  Simultaneity remains entirely in
`Instantiation.RegionResult`; no occurrence search is added.

#### Vacuity base

```lean
namespace Vacuity

def wrap
    (arity : Nat)
    (body : Region wires rels) :
    Region wires rels :=
  .mk 0
    (.cons
      (.bubble arity
        (body.renameRelations
          (RelationRenaming.weaken arity)))
      .nil)

inductive Local : LocalRule
  | introduce
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (arity : Nat)
      (body : Region materialWires materialRels)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems body wireMap relationMap)
        (Region.spliceAt hostLocal hostItems (wrap arity body)
          wireMap relationMap)

end Vacuity
```

Do not define `Vacuity` until Task 5 proves `Vacuity.Local.sound_iff`.

**Required compile gate:** each public relation module must contain complete definitions, no `sorry`, and no import from `VisualProof.Diagram.Concrete`, `VisualProof.Concrete`, the incumbent operational `Rule.Step`, or executor soundness modules.

**Validation:** compile each relation module separately, run `lake build` and `git diff --check`, and commit each family independently.

### Task 5: Isolate recursive semantic laws and prove family soundness

**Files:**

- Create `VisualProof/Rule/Laws.lean`
- Create `VisualProof/Rule/Soundness/Contextual.lean`
- Create `VisualProof/Rule/Soundness/{Erasure,WireSever,Iteration,DoubleCut,Comprehension,Vacuity}.lean`
- Modify direct importers of `VisualProof/Rule/Structural/Semantics.lean`

Move the implementation-independent Region theorems for conjunction erasure, wire collapse, ancestor copying, double cut, and vacuous bubbles into `Rule/Laws.lean`. `Rule/Laws.lean` may import only recursive diagram syntax, renaming, context reachability, algebra, isomorphism, and semantics. The operational structural module retains only concrete implementation material and imports no pure-law aggregate unless it directly uses a declaration from it.

The ancestor-copy law quantifies only descendant wire and relation environments that are recursively reachable through the selected `DiagramContext`. `DiagramContext.Reachable` supplies the inherited-environment equations for `outerWire` and `outerRelation`; arbitrary descendant valuations have no such relationship to the retained ancestor and cannot validate copying it.

Give the generic contextual theorem the neutral owner `Rule/Soundness/Contextual.lean`; no family soundness module owns it or serves as another family's import path:

```lean
theorem Contextual.sound
    {local : LocalRule}
    (localSound :
      ∀ {wires rels}
        {before after : Region wires rels},
        local before after →
        ∀ (model : Model)
          (env : Fin wires → model.Carrier)
          (relEnv : RelEnv model.Carrier rels),
          denoteRegion model env relEnv before →
          denoteRegion model env relEnv after)
    (step : Contextual local source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

Its proof decomposes the occurrence, uses `DiagramContext.denote_fill`, applies `OpenDiagram.denote_body`, and transports through the source and target open isomorphisms.

#### Erasure

```lean
theorem Erasure.Local.sound
    (step : Erasure.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before →
      denoteRegion model env relEnv after

theorem Erasure.sound
    (step : Erasure source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

The local proof is `Region.denote_spliceAt_host`; contextual soundness remains
unchanged.

#### Wire severing

```lean
theorem WireSever.Local.sound
    (step : WireSever.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before →
      denoteRegion model env relEnv after

theorem WireSever.Open.sound
    (step : WireSever.Open source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args

theorem WireSever.sound
    (step : WireSever source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

`WireSever.Local.sound` chooses the same semantic value for the fresh local wire as for `joined`. `WireSever.Open.sound` transports a source boundary assignment by composing its class assignment with `collapse`; the position-indexed boundary equation proves agreement.

#### Iteration

```lean
theorem Iteration.Base.sound_iff
    (step : Iteration.Base source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args ↔
      denoteOpen model target args
```

The copied relation and wire environments are exactly `descendant.outerRelation` and `descendant.outerWire`. Only after this theorem is GREEN, define:

```lean
def Iteration : Rule :=
  symmetric fun source target =>
    Nonempty (Iteration.Base source target)

theorem Iteration.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Iteration source target)
    (targetIso : OpenDiagramIso target target') :
    Iteration source' target'

theorem Iteration.sound
    (step : Iteration source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

#### Double cut

```lean
theorem DoubleCut.Local.sound_iff
    (step : DoubleCut.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before ↔
      denoteRegion model env relEnv after
```

Only after this theorem is GREEN, define:

```lean
def DoubleCut : Rule :=
  Contextual (symmetric DoubleCut.Local)

theorem DoubleCut.iso
    (sourceIso : OpenDiagramIso source source')
    (step : DoubleCut source target)
    (targetIso : OpenDiagramIso target target') :
    DoubleCut source' target'

theorem DoubleCut.sound
    (step : DoubleCut source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

#### Comprehension

The recursive owner states exactly which semantic relation witnesses the new existential binder:

```lean
theorem Comprehension.Instantiates.sound
    (step :
      Comprehension.Instantiates pattern quantified specialized) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv specialized →
      denoteRegion model env
        (OpenDiagram.asRelation model pattern, relEnv)
        quantified

theorem Comprehension.Local.sound
    (step : Comprehension.Local specialized quantified) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv specialized →
      denoteRegion model env relEnv quantified

theorem Comprehension.sound
    (step : Comprehension source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

Prove `Instantiates.sound` by mutual induction over `Instantiation.RegionResult`, `ItemsResult`, and `ItemResult`. The diagram-atom case uses `OpenDiagram.denote_substituteBoundary`; the bubble case uses `Mapping.lift`. `Local.sound` chooses `OpenDiagram.asRelation model pattern` as the bubble witness and transports through `quantified_iso`.

#### Vacuity

```lean
theorem Vacuity.Local.sound_iff
    (step : Vacuity.Local before after) :
    ∀ (model : Model)
      (env : Fin wires → model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteRegion model env relEnv before ↔
      denoteRegion model env relEnv after
```

Only after this theorem is GREEN, define:

```lean
def Vacuity : Rule :=
  Contextual (symmetric Vacuity.Local)

theorem Vacuity.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Vacuity source target)
    (targetIso : OpenDiagramIso target target') :
    Vacuity source' target'

theorem Vacuity.sound
    (step : Vacuity source target) :
    ∀ (model : Model)
      (args : Fin arity → model.Carrier),
      denoteOpen model source args →
      denoteOpen model target args
```

Run RED/GREEN separately for each owner and family theorem. Compile all six modules, run `lake build`, verify their dependency closures contain no concrete modules, and commit each family separately.

### Task 6: Move flat representation and execution to `Concrete`

This is one atomic import migration: intermediate public wrappers are not permitted, and the build must pass at the task boundary.

**Destination manifest:**

| Current responsibility | Final destination |
|---|---|
| flat core/open/well-formed types | `VisualProof/Concrete/{Diagram,Open,WellFormed}.lean` |
| checked elaboration/compiler/simulation | `VisualProof/Concrete/Elaboration/**` |
| finite selection, extraction, removal, splice, reassembly | `VisualProof/Concrete/Subgraph/**` |
| concrete isomorphism and occurrence equivalence | `VisualProof/Concrete/{Isomorphism,Occurrence}.lean` |
| provenance and interface transport | `VisualProof/Concrete/Transport.lean` |
| operational structural functions | `VisualProof/Concrete/Operation/**` |
| requests, orientation, errors, receipts, executor | `VisualProof/Concrete/Step.lean` |
| proof-state execution support | `VisualProof/Concrete/State.lean` |

Update every importing Lean module and the Lean executable targets in `lakefile.toml` in the same task. Do not leave namespace aliases or old-path re-exports.

Define checked open execution state with the boundary arity in its type:

```lean
structure Concrete.State (arity : Nat) where
  checked : Concrete.CheckedOpen
  boundary_length : checked.val.boundary.length = arity

def Concrete.State.diagram (source : Concrete.State arity) :
    Concrete.Checked :=
  ⟨source.checked.val.diagram,
    source.checked.property.diagram_well_formed⟩
```

Move the existing proof-bearing payload structures first, changing their input from `CheckedDiagram` to `State arity` and using `source.checked.val.diagram` for finite graph indices. Define the two generalized request payloads before `Concrete.Step`:

```lean
structure Concrete.WireSeverBoundary
    {arity : Nat} (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount) where
  side : Fin arity → Bool
  other : ∀ position,
    source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position) ≠ wire →
      side position = false

structure Concrete.Insertion
    {arity : Nat} (source : Concrete.State arity) where
  input : Concrete.Splice.Input
  frame_eq : input.frame = source.diagram
  admissible : input.Admissible
```

`Concrete.Splice.Input` already contains the checked open material, target region, ordered attachment map, binder spine, terminal-body contract, and binder targets. `admissible` supplies attachment visibility, binder matching, injectivity, and scope. Consequently `Insertion` realizes arbitrary insertion rather than only one bound atom.
Then move the ten-constructor `Concrete.Step (source : State arity)` mechanically. Abstraction and instantiation are not concrete requests and their payloads, tags, operation functions, and executor branches do not move into the final execution API. The changed retained constructors are:

```lean
| boundRelationSpawn (insertion : Concrete.Insertion source)
| wireSever
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
| iteration
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    (target : Fin source.checked.val.diagram.regionCount)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.checked.val.boundary)
```

For boundary positions denoting the severed wire, `WireSeverBoundary.side` chooses the old or fresh target wire. The `other` field canonicalizes irrelevant choices; the operation realization theorem proves those positions retain their original wire. This partition is supplied by the request, not discovered by execution.

`iteration` is proof-bearing. `boundaryDisjoint` is the exact legality
evidence in its public signature; disjointness from `exposedWires` may be
used only as a proved equivalent internal presentation. A request without this
evidence is not constructible, so execution gains no overlap error or
rejection branch.

Define the complete `Concrete.Error` once. Preserve the errors that the executor can actually return and add open-validation errors, but do not treat an error tag as proof that a fully specified request is invalid. Rejection correctness is established later from the exact request's structural meaning and execution equation, for every returned error. Do not add speculative cancellation, resource, unsupported-operation, or internal-error constructors unless the executor can actually return them.

Replace source-wire-only interface transport with position-aware boundary transport:

```lean
structure Concrete.BoundaryTransport
    {arity : Nat} (source target : Concrete.State arity) where
  image : Fin arity → Fin target.checked.val.diagram.wireCount
  target_boundary : ∀ position,
    target.checked.val.boundary.get
      (Fin.cast target.boundary_length.symm position) = image position
```

Operation-specific realization theorems connect each `image position` to the source boundary position. The position index permits `wireSever` to split repeated aliases.

Define receipts only after `State` and boundary transport:

```lean
structure Concrete.Receipt {arity : Nat}
    (source : Concrete.State arity) where
  target : Concrete.State arity
  provenance : WireProvenance source.checked.val.diagram
    target.checked.val.diagram
  boundary : Concrete.BoundaryTransport source target
```

The final executor shape is:

```lean
def Concrete.execute
    (orientation : Concrete.Orientation)
    {arity : Nat}
    (source : Concrete.State arity)
    (request : Concrete.Step source) :
    Except Concrete.Error (Concrete.Receipt source)
```

Execution consumes supplied occurrence certificates and never calls search.

The final Lean tree contains no occurrence-search modules or aggregate imports. Structural occurrence equivalence used by supplied requests remains.

**Validation:** compile every new aggregate, run `lake build`, run `rg` checks for old import paths and search declarations, run `git diff --check`, then commit the explicit migrated paths and `lakefile.toml` as `Separate concrete rewrite execution`.

### Task 7: Define the exhaustive actual `Step`

**Files:**

- Replace the operational contents of `VisualProof/Rule/Step.lean`
- Replace `VisualProof/Rule/Soundness.lean`
- Modify `VisualProof.lean`

After all family relations and concrete request declarations exist, define:

```lean
inductive Step : OpenDiagram arity → OpenDiagram arity → Prop
  | erasure : Erasure source target → Step source target
  | wireSever : WireSever source target → Step source target
  | iteration : Iteration source target → Step source target
  | doubleCut : DoubleCut source target → Step source target
  | vacuity : Vacuity source target → Step source target
```

`Comprehension`, `Comprehension.iso`, and `Comprehension.sound` remain standalone recursive declarations. They are not constructors of the actual ruleset and have no concrete implementation.

Prove `Step.iso` by family transport. RED/GREEN:

```lean
theorem Step.sound
    (step : Step source target) :
    ∀ (model : Model) (args : Fin arity → model.Carrier),
      denoteOpen model source args → denoteOpen model target args
```

The proof is five constructor cases delegating to the corresponding family soundness theorems. Use `lake env lean --deps VisualProof/Rule/Soundness.lean` as a direct-import diagnostic and a recursive source-import traversal to verify the full closure stops at recursive diagram and rule modules. The standalone Comprehension soundness owner remains compiled and audited independently. Commit as `Prove relational step soundness`.

### Task 8: Define translation, encoding, and representation

**Files:**

- Modify `VisualProof/Diagram/OpenIsomorphism.lean`
- Create `VisualProof/Concrete/Translate.lean`
- Create `VisualProof/Concrete/Encode.lean`
- Create `VisualProof/Refinement/Represents.lean`
- Modify `VisualProof.lean`

`OpenDiagramIso` is proof-relevant witness data in `Type`, while
representation is a proposition. Define its propositional existence relation
once at the diagram boundary:

```lean
def OpenDiagram.Isomorphic
    (source target : OpenDiagram arity) : Prop :=
  Nonempty (OpenDiagramIso source target)
```

Prove reflexivity, symmetry, and transitivity by the corresponding witness
operations. Actual witness-consuming functions continue to take
`OpenDiagramIso`; relational conclusions use `OpenDiagram.Isomorphic`.

Implement an actual open validator. It checks the underlying flat diagram and proves every boundary wire is in root scope. Its error records either the existing well-formedness error or the offending boundary position. `Except` requires its success parameter in `Type`, so package the proposition in a proof-carrying type indexed by the exact input; input preservation remains definitional:

```lean
structure Concrete.OpenValidation
    (concrete : Concrete.OpenDiagram) where
  valid : concrete.WellFormed

def Concrete.OpenValidation.checked
    (validation : Concrete.OpenValidation concrete) :
    Concrete.CheckedOpen :=
  ⟨concrete, validation.valid⟩

def Concrete.checkOpen (concrete : Concrete.OpenDiagram) :
    Except Concrete.Error (Concrete.OpenValidation concrete)

theorem Concrete.checkOpen_complete
    (valid : concrete.WellFormed) :
    Concrete.checkOpen concrete = .ok ⟨valid⟩
```

Keep elaboration total on `Concrete.CheckedOpen`. Define translation exactly as open validation followed by elaboration:

```lean
def Concrete.translate (concrete : Concrete.OpenDiagram) :
    Except Concrete.Error (OpenDiagram concrete.boundary.length) :=
  match Concrete.checkOpen concrete with
  | .error error => .error error
  | .ok validation => .ok validation.checked.elaborate

theorem Concrete.translate_checked (checked : Concrete.CheckedOpen) :
    Concrete.translate checked.val = .ok checked.elaborate
```

Define:

```lean
def Represents
    (concrete : Concrete.OpenDiagram)
    (diagram : OpenDiagram concrete.boundary.length) : Prop :=
  ∃ translated,
    Concrete.translate concrete = .ok translated ∧
    OpenDiagram.Isomorphic translated diagram
```

For indexed execution states define:

```lean
def StateRepresents
    (state : Concrete.State arity)
    (diagram : OpenDiagram arity) : Prop :=
  Represents state.checked.val
    (diagram.castArity state.boundary_length.symm)

def Concrete.State.translate (state : Concrete.State arity) :
    Except Concrete.Error (OpenDiagram arity) :=
  (Concrete.translate state.checked.val).map
    (fun diagram => diagram.castArity state.boundary_length)
```

Implement the encoder as an indexed checked state:

```lean
def Concrete.encode (diagram : OpenDiagram arity) : Concrete.State arity

theorem encode_represents (diagram : OpenDiagram arity) :
    StateRepresents (Concrete.encode diagram) diagram
```

Its implementation recursively allocates finite region/node/wire indices and emits the ordered boundary list from `OpenDiagram.boundary`. Prove:

- the encoded flat open diagram is well formed;
- `Concrete.State.translate (Concrete.encode diagram)` succeeds with a diagram isomorphic to `diagram`, with the same ordered positions and alias partition;
- every checked input represents its elaboration:

```lean
theorem checked_represents (concrete : Concrete.CheckedOpen) :
    Represents concrete.val (Concrete.elaborate concrete)
```

- representation uniqueness concludes propositional isomorphism:

```lean
theorem represents_unique
    (first : Represents concrete firstDiagram)
    (second : Represents concrete secondDiagram) :
    OpenDiagram.Isomorphic firstDiagram secondDiagram
```

- representation completeness follows from `encode` with the exact raw form:

```lean
theorem representation_complete (diagram : OpenDiagram arity) :
    ∃ (concrete : Concrete.OpenDiagram)
      (arity_eq : concrete.boundary.length = arity),
      Represents concrete (diagram.castArity arity_eq.symm)
```

Run RED/GREEN for the round trip and the three representation theorems. Compile, build, kernel-audit, and commit as `Prove concrete representation laws`.

### Foundational prerequisite: establish canonical structural witness authority

This prerequisite is GREEN before Task 9 resumes. It changes the existing
structural witness hierarchy itself; it does not introduce a second witness
authority, a compatibility path, or a Task-9-local substitute.

- Convert `RegionIso`, `ItemIso`, and `ItemSeqIso` into the one canonical
  proof-relevant `Type` hierarchy. Preserve ambient and local wire
  equivalences, position equivalences, per-item witnesses, and recursive
  cut/bubble witnesses as its data.
- Theorem-facing relations state propositions with `Nonempty` of that
  canonical Type witness. Canonical maps are fields or indices of the witness,
  not existentially recovered data.
- Make `OpenDiagramIso.body` the canonical Type witness.
- Convert `DiagramContextIso` to Type. Strengthen the existing
  `ContextPathAlignment` so it directly returns or contains composable data;
  it may not rely on `Nonempty` caused by Prop erasure.
- Derive proof-only generic context replacement directly from the source
  occurrence and canonical recursive isomorphism hierarchy, then compose that
  law with the local recursive rule after flat execution.
- Migrate every current Task-9 consumer to these owners while keeping Concrete
  and Refinement semantic-free.

The foundation Worker must compile only production declarations with
`LEAN_NUM_THREADS=1` and `-DwarningAsError=true`; it may add no examples,
fixtures, synthetic theorems, `#check`, or `#eval`. The independent Judge
must verify direct projection and composition without Prop-to-Type elimination,
recursive data in `OpenDiagramIso.body`, source-derived generic
flat-transformation laws, no independently supplied target proof data, all
authority audits, no-hole/axiom scans, and a serial full build.

### Task 9: Prove structural execution refinement family by family

**Files:**

- Create `VisualProof/Refinement/Step/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`
- Create `VisualProof/Refinement/Step.lean`
- Create `scripts/audit-lean-authority.sh`, a Bash audit that recursively follows Lean source imports from fixed root sets and rejects forbidden layer dependencies
- Split structural diagram declarations from semantic declarations wherever the concrete/refinement import closure currently mixes them
- Extract only source-derived elaboration laws, carrier equivalences, boundary correspondences, recursive isomorphisms, receipt inversions, and generic flat-transformation facts consumed by refinement
- Remove concrete-dependent semantic declarations and operational semantic proof towers instead of relocating, renaming, wrapping, re-exporting, or retaining them as parallel authorities

Before continuing family proofs, remediate the existing dependency boundary. `Concrete/**` and `Refinement/**` must have semantic-free source and import closures. In particular, remove concrete denotation APIs and concrete semantic simulation/soundness modules; split any mixed diagram module so structural consumers do not import models or denotation; replace imports of operational `Rule.Soundness` modules with focused structural owners; and remove the operational rule-soundness aggregates once their structural facts have been extracted. Preserve compliant execution inversions and structural proofs already established. Migrate existing `Proof/**` consumers of concrete semantic APIs directly to the authoritative Diagram semantics and Rule soundness interfaces during this remediation; do not create an intermediate semantic adapter. Task 12 later narrows concrete-execution validity to the final thin composition.

`scripts/audit-lean-authority.sh` has five modes. Its import modes fail on a forbidden edge anywhere in the recursive source-import closure:

- `rules`: start from all six relations, all six family soundness owners, `Rule.Step`, and `Rule.Soundness`; reject every `Concrete`, `Refinement`, and `Proof` import.
- `implementation`: start from `Concrete.Step`, `Concrete.Translate`, `Concrete.Encode`, `Refinement.Represents`, `Refinement.Step`, and later completeness/rejection roots when present; reject `Model`, semantic Diagram modules, concrete semantic modules, `Rule.Soundness`, `Rule.Step.sound` owners, and `Proof`.
- `proof`: require concrete-execution semantic owners to import the aggregate refinement and aggregate `Rule.Soundness` interfaces plus structural representation/isomorphism transport; reject direct family soundness, operational soundness, or concrete semantic imports.
- `roster`: inspect the actual `Rule.Step`, `Concrete.Step`, `Step.tag`, `StepTag`, tag inventory, and serialized-tag declarations. It requires exactly the fixed five actual rule constructors and ten concrete constructors/tags, requires the standalone Rule Comprehension relation/isomorphism/soundness declarations, and rejects every Comprehension execution declaration or branch under Concrete, Refinement, `Rule.Step`, Means, or completeness, as well as the former request names in Proof.
- `documentation`: inspect the governing goal, machine board, and plan for competing proof ownership; the only accepted refinement model is source-derived generic flat transformation.

The script reports the full root-to-forbidden-import path for import modes and the exact source declaration mismatch for roster mode. `lake env lean --deps` remains a useful direct-import diagnostic but is not accepted as proof of recursive closure purity.

As part of the Task 9 remediation, remove abstraction and instantiation from `Concrete.Step`, tags, executor dispatch, concrete operation owners, execution inversions, refinement owners, and execution-facing aggregates. Remove the `Comprehension` constructor from `Rule.Step` and its case from `Step.iso`/`Step.sound`, while preserving the standalone recursive Comprehension relation, isomorphism theorem, and soundness theorem.

For each of the ten request constructors, prove that successful execution translates to the assigned actual-rule family relation. Derive proof-only data from the source occurrence, the canonical recursive witnesses, deterministic target checking, and generic flat-transformation laws. Neither family modules nor the aggregate may state or prove a model, denotation, semantic implication, or rule-soundness result.

For `Concrete.Step.iteration selection target boundaryDisjoint`, the
successful-execution inversion must receive and retain `boundaryDisjoint`.
The Iteration structural base theorem must take that same evidence explicitly
and use it to keep selected explicit wires out of the ordered boundary while
building the `Rule.Iteration.Base` witness. This repairs the root boundary
case in the concrete request layer only: do not change `Rule.Iteration`, add
no executor error, and add no rejection branch.

The family table is exhaustive:

| Relation | Concrete constructors |
|---|---|
| `Erasure` | `erasure`, `boundRelationSpawn` |
| `WireSever` | `wireSever`, `wireJoin` |
| `Iteration` | `iteration`, `deiteration` |
| `DoubleCut` | `doubleCutIntro`, `doubleCutElim` |
| `Vacuity` | `vacuousIntro`, `vacuousElim` |

The public aggregate theorem is stated over a checked open state and any represented source:

```lean
theorem execute_sound
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source request = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
       | .forward => Rule.Step sourceDiagram targetDiagram
       | .backward => Rule.Step targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram
```

The family-specific successful-execution theorems produce the existential `targetDiagram`; representation uniqueness and `Step.iso` allow callers to replace it by another recursive representative of the same concrete target.

The structural bridge for a splice is indexed by the recursive occurrence's
context polarity.  At positive polarity erasure relates the spliced diagram to
the host; at negative polarity the whole-diagram relation is reversed by
`Contextual`.  Concrete erasure/spawn polarity evidence aligns that result with
`orientation`; no unconditional nested-splice endpoint order is valid.

Also prove the canonical commuting corollary with the indexed state translation:

```lean
theorem execute_translates
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source request = .ok receipt) :
    ∃ sourceDiagram targetDiagram,
      source.translate = .ok sourceDiagram ∧
      receipt.target.translate = .ok targetDiagram ∧
      match orientation with
      | .forward => Rule.Step sourceDiagram targetDiagram
      | .backward => Rule.Step targetDiagram sourceDiagram
```

It follows from `execute_sound`, translation success for checked states, representation uniqueness, and `Step.iso`; it does not re-prove a rule.

Validate and commit each family separately, then the aggregate. For every concrete/refinement entry point used by representation or execution, audit both its source and recursive dependency closure: they must exclude `Model`, diagram semantic modules, concrete semantic modules, `Rule.Soundness`, `Rule.Step.sound`, and `Proof`.

```bash
lake env lean -DwarningAsError=true VisualProof/Concrete/Step.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Represents.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Step.lean
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh documentation
rg -n '^import VisualProof\.(Model|Diagram\.Semantics|Concrete\.Semantics|Rule\.Soundness|Proof)' VisualProof/Concrete VisualProof/Refinement
rg -n '\b(Model|denoteOpen|denoteRegion|ConcreteSemanticSimulation|Step\.sound)\b' VisualProof/Concrete VisualProof/Refinement
rg -n 'comprehension(Abstract|Instantiate)|OperationComprehension|Comprehension.*Payload' VisualProof/Concrete VisualProof/Refinement VisualProof/Proof
lake exe visualproof_step_tags
rg -n '\bsorry\b|sorryAx' VisualProof
lake build
git diff --check
```

The semantic-source scans must return no declaration or import. The roster audit is the exact executable-family/absence gate and must pass before any Task 9 family proof is accepted. Dependency output must be checked recursively for the same forbidden owners. Kernel-check the final `Concrete.Step.iteration` constructor, its successful-execution inversion, and the Iteration structural base theorem to verify that the exact `boundaryDisjoint` evidence is carried and consumed; a source-substring check is not acceptance evidence.

### Task 10: Prove request reflection and execution completeness

**Files:**

- Create `VisualProof/Refinement/Complete/{Erasure,WireSever,Iteration,DoubleCut,Vacuity}.lean`
- Create `VisualProof/Refinement/Complete.lean`

For each family, prove an occurrence-reflection theorem: given `StateRepresents source sourceDiagram` and a family witness on `sourceDiagram`, construct the dependent checked finite selection, embedding, boundary assignment, scope proof, and operation payload needed by the corresponding `Concrete.Step` constructor. This is an existence proof over finite data, not a matcher or executable search function.

Define the common completeness property once:

```lean
def Implemented (relation : Rule) : Prop :=
  ∀ {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram targetDiagram : OpenDiagram arity}
    (orientation : Concrete.Orientation),
    StateRepresents source sourceDiagram →
    (match orientation with
     | .forward => relation sourceDiagram targetDiagram
     | .backward => relation targetDiagram sourceDiagram) →
    ∃ (request : Concrete.Step source) (receipt : Concrete.Receipt source),
      Concrete.execute orientation source request = .ok receipt ∧
      StateRepresents receipt.target targetDiagram

theorem Erasure.complete : Implemented Erasure
theorem WireSever.complete : Implemented WireSever
theorem Iteration.complete : Implemented Iteration
theorem DoubleCut.complete : Implemented DoubleCut
theorem Vacuity.complete : Implemented Vacuity
```

The erasure converse case uses the generalized `boundRelationSpawn` payload from Task 6. The open wire-sever case reflects the explicit boundary class split. The Iteration reflection case constructs `selection`, `target`, and `selection.val.explicitWires.Disjoint source.checked.val.boundary` from each reflected `Rule.Iteration.Base` witness before it constructs the concrete request. Completeness ranges over the five-constructor actual `Rule.Step`; standalone Comprehension has no execution-completeness claim.

After each request constructor theorem compiles, prove:

```lean
theorem execute_complete
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram targetDiagram : OpenDiagram arity}
    (orientation : Concrete.Orientation)
    (sourceRep : StateRepresents source sourceDiagram)
    (step : match orientation with
      | .forward => Rule.Step sourceDiagram targetDiagram
      | .backward => Rule.Step targetDiagram sourceDiagram) :
    ∃ (request : Concrete.Step source) (receipt : Concrete.Receipt source),
      Concrete.execute orientation source request = .ok receipt ∧
      StateRepresents receipt.target targetDiagram
```

This task is syntactic only. No theorem may call or define a matcher or mention a model, denotation, semantic implication, `Rule.Soundness`, `Rule.Step.sound`, or `Proof`. Reflection constructs proof-bearing finite request data; it does not execute search. Kernel-check the Iteration completeness theorem through the proof-bearing constructor rather than scanning source text for the legality field. Audit the source and dependency closures of every completeness owner, validate family modules and the aggregate, build, and commit as `Prove concrete execution completeness`.

```bash
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete/Erasure.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete/WireSever.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete/Iteration.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete/DoubleCut.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete/Vacuity.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete.lean
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh documentation
rg -n '^import VisualProof\.(Model|Diagram\.Semantics|Concrete\.Semantics|Rule\.Soundness|Proof)' VisualProof/Refinement/Complete VisualProof/Refinement/Complete.lean
rg -n '(matcher|candidate|search frontier|search status)' VisualProof/Refinement/Complete VisualProof/Refinement/Complete.lean
lake build
git diff --check
```

### Task 11: Prove unconditional rejection correctness

**Files:**

- Modify `VisualProof/Concrete/Step.lean`, `VisualProof/Concrete/Step/**/*.lean`, and the concrete operation/request/splice legality modules reached by an actual failing `Means` branch
- Create `VisualProof/Refinement/Means.lean`
- Create `VisualProof/Refinement/Rejection.lean`
- Modify `VisualProof/Audit.lean` and its Lean audit support

Define request meaning in its own owner `VisualProof.Refinement.Means`, not in `Concrete`: it depends on both concrete requests and actual-rule family relations. Its definition is exhaustive recursion over the ten concrete constructors, relating the supplied data to the corresponding family witness. `Refinement/Rejection.lean` imports this owner and contains same-request completeness and rejection correctness.

```lean
def Means
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    (sourceRep : StateRepresents source sourceDiagram)
    (request : Concrete.Step source)
    (orientation : Concrete.Orientation)
    (targetDiagram : OpenDiagram arity) : Prop
```

Implement `Means` by pattern matching on all ten constructors. The branches, in constructor order, produce the Erasure converse, WireSever converse, Erasure base, WireSever base, Iteration base, Iteration converse, DoubleCut introduction, DoubleCut elimination, Vacuity introduction, and Vacuity elimination witnesses. The Iteration request branch receives the proof-bearing `boundaryDisjoint` field and uses it in its structural correspondence. Every branch body is a proposition defined from the relevant representation, selection/occurrence correspondence, controlling polarity, legality evidence, and family relation. Complete and compile all ten bodies before RED.

`Means` is a syntactic request-meaning relation. It may not mention `Concrete.execute`, success or error results, receipts, models, denotation, semantic implication, or soundness. Each branch fixes the supplied request and contains its structural correspondence, controlling polarity and legality evidence, assigned family witness or converse, and exact target representation/isomorphism.

For that same request, first prove exact-request completeness:

```lean
theorem Means.execute
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram targetDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    (sourceRep : StateRepresents source sourceDiagram)
    (means : Means sourceRep request orientation targetDiagram) :
    ∃ receipt : Concrete.Receipt source,
      Concrete.execute orientation source request = .ok receipt ∧
      StateRepresents receipt.target targetDiagram
```

This is stronger in a different direction from Task 10: Task 10 may construct some request for an abstract step, while this theorem proves success of the already supplied request. If a `Means` branch can reach an executor rejection, repair the executor, add the missing proof-bearing legality evidence to that request, or correct the error contract. Do not exclude an error constructor or add an error-classification premise.

Prove:

```lean
theorem execute_rejects_only_invalid
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    {request : Concrete.Step source}
    {error : Concrete.Error}
    (sourceRep : StateRepresents source sourceDiagram)
    (failure : Concrete.execute orientation source request = .error error) :
    ¬ ∃ targetDiagram, Means sourceRep request orientation targetDiagram
```

Prove the result by contradicting `Means.execute`; it covers every error returned for a fully specified request. Boundary overlap is excluded by request construction, not by a new error or an error-classification premise. Validate the ten branch definitions, including the proof-bearing Iteration branch, same-request completeness, the unconditional rejection signature, semantic-free source and dependency closures, the full build, and kernel axioms. Commit as `Prove concrete rejection correctness`.

```bash
lake env lean -DwarningAsError=true VisualProof/Concrete/Step.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Means.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Rejection.lean
rg -n 'DomainInvalid|invalid :.*DomainInvalid' VisualProof/Refinement/Rejection.lean
rg -n '\b(execute|Receipt|Error|Model|denoteOpen|denoteRegion|sound)\b' VisualProof/Refinement/Means.lean
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh documentation
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake build
git diff --check
```

Both source scans must be empty. Lean dependency inspection must recursively
inspect the elaborated value expression of `Means` and fail if it depends on
`Concrete.execute`, `Concrete.Receipt`, `Concrete.Error`, model/denotation
constants, or soundness constants. Proof completion is validated by
`lake build` followed immediately by
`rg -n '\bsorry\b' VisualProof --glob '*.lean'`.

### Task 12: Factor replay and theorem validity through refinement

**Files:**

- Modify `VisualProof/Proof/Replay.lean`
- Modify `VisualProof/Proof/Schema.lean`
- Modify `VisualProof/Proof/Theorem.lean`
- Modify `VisualProof/Proof/Theory.lean`

Replay stores concrete checked open states and requests. Its correctness theorem obtains a recursive step from `Refinement.execute_sound`, aligns adjacent representatives using representation/isomorphism transport, and applies `Rule.Step.sound`. The theorem schema remains open because it quantifies over ordered boundary arguments.

This is the only layer in which concrete execution is connected to models or denotation. The proof must be a thin composition of `Refinement.execute_sound`, `Rule.Step.sound`, and representation/isomorphism transport. It may not split on the ten request constructors, import a family-specific soundness owner, or perform rule-specific semantic reasoning. Validate those source and dependency constraints, compile all four modules, run `lake build`, kernel-audit the checked-theorem result, and commit as `Factor proof replay through refinement`.

```bash
lake env lean -DwarningAsError=true VisualProof/Proof/Replay.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Schema.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theory.lean
rg -n '\.(boundRelationSpawn|wireJoin|erasure|wireSever|iteration|deiteration|doubleCutIntro|doubleCutElim|vacuousIntro|vacuousElim)\b' VisualProof/Proof
scripts/audit-lean-authority.sh proof
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh documentation
lake env lean -DwarningAsError=true VisualProof/Audit.lean
lake build
git diff --check
```

The constructor-case scan must be empty in semantic proof bodies. The proof-mode import audit must accept only aggregate `Refinement.execute_sound`, aggregate `Rule.Step.sound`, and structural representation/isomorphism transport at the concrete-validity theorem boundary. Lean audit support must inspect that theorem's elaborated value and reject dependencies on concrete semantic declarations, operational soundness declarations, or direct family soundness declarations.

### Task 13: Final authority and repository audit

**Files:**

- Modify `VisualProof.lean`
- Modify `VisualProof/Audit.lean`
- Modify `lakefile.toml`
- Remove only superseded Lean paths identified by `rg` after all imports have moved

**Audit:**

1. `VisualProof.lean` imports diagram syntax/semantics and rule soundness independently from concrete translation/execution and refinement, then imports proof modules that compose the layers.
2. Audit the recursive direction: the dependency closures of every rule relation, every family soundness owner, and `VisualProof/Rule/Soundness.lean` contain no path under `VisualProof/Concrete`, `VisualProof/Refinement`, or the flat implementation tree.
3. Audit the implementation direction: direct source scans and recursive dependency closures for `Concrete.Step`, `Concrete.Translate`, `Concrete.Encode`, `Refinement.Represents`, `Refinement.Step`, `Refinement.Complete`, and `Refinement.Rejection` contain no model, denotation, semantic implication, semantic simulation, `Rule.Soundness`, `Rule.Step.sound`, or `Proof` declaration/import. No semantic module or parallel semantic authority remains under `Concrete/**` or `Refinement/**`.
4. Inspect the elaborated `Means` declaration and its branch bodies: they reference the supplied request type but do not depend on `Concrete.execute`, success/error results, receipts, models, denotation, or soundness, and all ten request constructors have an exact structural branch.
5. `scripts/audit-lean-authority.sh roster` proves the exact five-constructor `Rule.Step` and ten-constructor/tag `Concrete.Step` roster, the standalone Rule Comprehension relation/isomorphism/soundness declarations, and the absence of Comprehension execution declarations or branches and former request names. `scripts/audit-lean-authority.sh documentation` proves the governing files retain the source-derived generic flat-transformation model.
6. `rg -n '\bsorry\b|sorryAx' VisualProof` reports no task-owned production proof.
7. `rg` reports no occurrence-search declaration, import, candidate enumeration, search status, or matcher theorem.
8. Immediately after `lake build`,
   `rg -n '\bsorry\b' VisualProof --glob '*.lean'` reports no unfinished
   production theorem.
9. Run:

```bash
lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Represents.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Step.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Complete.lean
lake env lean -DwarningAsError=true VisualProof/Refinement/Rejection.lean
lake env lean -DwarningAsError=true VisualProof/Proof/Theorem.lean
lake env lean -DwarningAsError=true VisualProof/Audit.lean
rg -n '^import VisualProof\.(Model|Diagram\.Semantics|Concrete\.Semantics|Rule\.Soundness|Proof)' VisualProof/Concrete VisualProof/Refinement
rg -n '\b(Model|denoteOpen|denoteRegion|ConcreteSemanticSimulation|Step\.sound)\b' VisualProof/Concrete VisualProof/Refinement
rg -n 'comprehension(Abstract|Instantiate)|OperationComprehension|Comprehension.*Payload' VisualProof/Concrete VisualProof/Refinement VisualProof/Proof
lake exe visualproof_step_tags
scripts/audit-lean-authority.sh rules
scripts/audit-lean-authority.sh implementation
scripts/audit-lean-authority.sh proof
scripts/audit-lean-authority.sh roster
scripts/audit-lean-authority.sh documentation
lake build
git diff --check
```

Stage only task-owned paths explicitly and commit as `Complete recursive rewrite authority`.

## Acceptance checklist

- [ ] `Region` is the only recursive syntax; `OpenDiagram` is only the ordered open interface.
- [ ] Occurrence is relational context decomposition, never search output.
- [ ] The six recursive family relations are complete and contain only mathematical witnesses; standalone Comprehension and its soundness remain outside the actual ruleset.
- [ ] Positive-context rules, converse under negative polarity, and proved invertibility are the only direction mechanisms in the abstract layer.
- [ ] `Step` has exactly five constructors—Erasure, WireSever, Iteration, DoubleCut, and Vacuity—and `Step.sound` is ordinary implication; Comprehension is not a Step constructor.
- [ ] `scripts/audit-lean-authority.sh roster` passes, proving the exact executable roster and absence boundary while retaining standalone Rule Comprehension mathematics.
- [ ] `scripts/audit-lean-authority.sh documentation` passes, proving the governing files retain source-derived generic flat-transformation refinement.
- [ ] `Step.sound` has no concrete dependency.
- [ ] Concrete and Refinement source and import closures contain no semantic declaration, proof, import, or parallel authority.
- [ ] Concrete execution has exactly ten operation constructors over checked open state and contains no abstraction/instantiation payload, tag, branch, or theorem.
- [ ] `Concrete.Step.iteration` carries exactly `selection.val.explicitWires.Disjoint source.checked.val.boundary`; kernel-checked inversion, Iteration refinement, reflection, and Means carry that proof without a new executor error, rejection branch, or `Rule.Iteration` change.
- [ ] Requests supply every selected occurrence and legality witness; execution performs no search.
- [ ] `Concrete.translate` is validation followed by elaboration.
- [ ] `Represents` is successful translation modulo propositional open-diagram isomorphism.
- [ ] `Concrete.encode` proves representation completeness.
- [ ] Every successful concrete operation refines its assigned family relation.
- [ ] Every abstract step reflects to a concrete request and successful one-step execution.
- [ ] Every executor error on a fully specified request unconditionally refutes that exact request's `Means` relation.
- [ ] Replay and theorem validity are the only concrete-execution semantic bridge and use only refinement, representation/isomorphism transport, and `Step.sound`.
- [ ] The final Lean tree has one semantic authority, no compatibility path, no matcher, no `sorry`, and a passing build.
