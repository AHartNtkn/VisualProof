import VisualProof.Diagram.Concrete.Semantics

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-- Every lambda model has an inhabitant: evaluate the closed identity term.
This is the exact nonemptiness needed when a concrete rewrite introduces a
fresh existential wire. -/
theorem lambdaModel_carrier_nonempty
    (model : Lambda.LambdaModel) : Nonempty model.Carrier :=
  ⟨model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
    Lambda.Term 0 (Fin 0)) Fin.elim0⟩

/-- The direction in which a concrete compiler simulation transports truth. -/
inductive SimulationDirection
  | forward
  | backward
  deriving DecidableEq

namespace SimulationDirection

/-- Negation reverses semantic simulation. -/
def flip : SimulationDirection → SimulationDirection
  | .forward => .backward
  | .backward => .forward

@[simp] theorem flip_forward : flip .forward = .backward := rfl
@[simp] theorem flip_backward : flip .backward = .forward := rfl
@[simp] theorem flip_flip (direction : SimulationDirection) :
    direction.flip.flip = direction := by
  cases direction <;> rfl

end SimulationDirection

/-- Directional entailment between source and target propositions. -/
def SimulationDirection.Entails : SimulationDirection → Prop → Prop → Prop
  | .forward, source, target => source → target
  | .backward, source, target => target → source

theorem SimulationDirection.entails_and
    (direction : SimulationDirection)
    {sourceHead targetHead sourceTail targetTail : Prop}
    (head : direction.Entails sourceHead targetHead)
    (tail : direction.Entails sourceTail targetTail) :
    direction.Entails (sourceHead ∧ sourceTail) (targetHead ∧ targetTail) := by
  cases direction with
  | forward => exact fun source => ⟨head source.1, tail source.2⟩
  | backward => exact fun target => ⟨head target.1, tail target.2⟩

/-- A relation between lexical indices.  It deliberately need not be a
function in either direction: an embedding and a coalescing collapse are both
instances of the same representation. -/
structure ContextIndexRelation (source target : Nat) where
  Rel : Fin source → Fin target → Prop

namespace ContextIndexRelation

/-- The graph of a source-to-target context map. -/
def forwardMap (map : Fin source → Fin target) :
    ContextIndexRelation source target where
  Rel sourceIndex targetIndex := map sourceIndex = targetIndex

/-- The converse graph of a target-to-source context map.  The map may be
non-injective, which is the case needed for wire coalescing. -/
def backwardMap (map : Fin target → Fin source) :
    ContextIndexRelation source target where
  Rel sourceIndex targetIndex := map targetIndex = sourceIndex

/-- Two environments agree on every pair of related lexical indices. -/
def EnvironmentsAgree (relation : ContextIndexRelation source target)
    (sourceEnv : Fin source → D) (targetEnv : Fin target → D) : Prop :=
  ∀ sourceIndex targetIndex, relation.Rel sourceIndex targetIndex →
    sourceEnv sourceIndex = targetEnv targetIndex

@[simp] theorem environmentsAgree_forwardMap
    (map : Fin source → Fin target)
    (sourceEnv : Fin source → D) (targetEnv : Fin target → D) :
    (forwardMap map).EnvironmentsAgree sourceEnv targetEnv ↔
      sourceEnv = targetEnv ∘ map := by
  constructor
  · intro agrees
    funext index
    exact agrees index (map index) rfl
  · intro equality sourceIndex targetIndex related
    subst targetIndex
    exact congrFun equality sourceIndex

@[simp] theorem environmentsAgree_backwardMap
    (map : Fin target → Fin source)
    (sourceEnv : Fin source → D) (targetEnv : Fin target → D) :
    (backwardMap map).EnvironmentsAgree sourceEnv targetEnv ↔
      sourceEnv ∘ map = targetEnv := by
  constructor
  · intro agrees
    funext index
    exact agrees (map index) index rfl
  · intro equality sourceIndex targetIndex related
    subst sourceIndex
    exact congrFun equality targetIndex

end ContextIndexRelation

/-- The canonical relation renaming used by same-context simulations. -/
def identityRelationRenaming (rels : RelCtx) : RelationRenaming rels rels :=
  fun relation => relation

/-- A same-context binder witness expressed without requiring the source and
target diagrams to be definitionally identical. -/
structure IdentityBinderWitness
    (source target : ConcreteDiagram)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels) : Type where
  relationContexts_eq : sourceRels = targetRels
  binders_eq : HEq sourceBinders targetBinders

namespace IdentityBinderWitness

def relationMap
    (witness : IdentityBinderWitness
      (sourceRels := sourceRels) (targetRels := targetRels)
      source target sourceBinders targetBinders) :
    RelationRenaming sourceRels targetRels := by
  cases witness with
  | mk relationContexts_eq _ =>
      subst targetRels
      exact identityRelationRenaming sourceRels

end IdentityBinderWitness

/-- Semantic simulation of two intrinsic items under related environments. -/
def ItemSimulation (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : SimulationDirection)
    (relation : ContextIndexRelation sourceWires targetWires)
    (sourceItem : Item signature sourceWires rels)
    (targetItem : Item signature targetWires rels) : Prop :=
  ∀ (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    relation.EnvironmentsAgree sourceEnv targetEnv →
      direction.Entails
        (denoteItem model named sourceEnv relEnv sourceItem)
        (denoteItem model named targetEnv relEnv targetItem)

/-- Node compilation is semantically invariant when corresponding resolved
ports are related, even when the context relation is genuinely many-to-many
and therefore cannot be represented by one global index-renaming function. -/
theorem compileNode?_itemSimulation_of_related_ports
    {source target : ConcreteDiagram}
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : SimulationDirection)
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (relation : ContextIndexRelation sourceContext.length targetContext.length)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceNode : Fin source.nodeCount)
    (targetNode : Fin target.nodeCount)
    (regionMap : Fin source.regionCount → Fin target.regionCount)
    (binderMap : Fin source.regionCount → Fin target.regionCount)
    (nodeShape : target.nodes targetNode =
      match source.nodes sourceNode with
      | .term region freePorts term =>
          .term (regionMap region) freePorts term
      | .atom region binder =>
          .atom (regionMap region) (binderMap binder)
      | .named region definition arity =>
          .named (regionMap region) definition arity)
    (portsRelated : ∀ port sourceIndex targetIndex,
      resolvePort? source sourceContext sourceNode port = some sourceIndex →
      resolvePort? target targetContext targetNode port = some targetIndex →
      relation.Rel sourceIndex targetIndex)
    (bindersRelated : ∀ region binder arity
      (sourceRelation : RelVar sourceRels arity),
      source.nodes sourceNode = .atom region binder →
      sourceBinders binder = some ⟨arity, sourceRelation⟩ →
      targetBinders (binderMap binder) =
        some ⟨arity, relationMap sourceRelation⟩)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled :
      compileNode? signature source sourceContext sourceBinders sourceNode =
        some sourceItem)
    (targetCompiled :
      compileNode? signature target targetContext targetBinders targetNode =
        some targetItem) :
    ItemSimulation model named direction relation
      (sourceItem.renameRelations relationMap) targetItem := by
  cases sourceNodeShape : source.nodes sourceNode with
  | term region freePorts term =>
      have targetNodeShape :
          target.nodes targetNode =
            .term (regionMap region) freePorts term := by
        simpa only [sourceNodeShape] using nodeShape
      cases sourceOutputResult :
          resolvePort? source sourceContext sourceNode .output with
      | none =>
          simp [compileNode?, sourceNodeShape, sourceOutputResult]
            at sourceCompiled
      | some sourceOutput =>
          cases sourceFreeResult :
              resolvePorts? source sourceContext sourceNode freePorts
                (fun index => .free index) with
          | none =>
              simp [compileNode?, sourceNodeShape, sourceOutputResult,
                sourceFreeResult] at sourceCompiled
          | some sourceFree =>
              simp [compileNode?, sourceNodeShape, sourceOutputResult,
                sourceFreeResult] at sourceCompiled
              subst sourceItem
              cases targetOutputResult :
                  resolvePort? target targetContext targetNode .output with
              | none =>
                  simp [compileNode?, targetNodeShape, targetOutputResult]
                    at targetCompiled
              | some targetOutput =>
                  cases targetFreeResult :
                      resolvePorts? target targetContext targetNode freePorts
                        (fun index => .free index) with
                  | none =>
                      simp [compileNode?, targetNodeShape, targetOutputResult,
                        targetFreeResult] at targetCompiled
                  | some targetFree =>
                      simp [compileNode?, targetNodeShape, targetOutputResult,
                        targetFreeResult] at targetCompiled
                      subst targetItem
                      intro sourceEnv targetEnv relEnv environments
                      have outputEq : sourceEnv sourceOutput =
                          targetEnv targetOutput :=
                        environments sourceOutput targetOutput
                          (portsRelated .output sourceOutput targetOutput
                            sourceOutputResult targetOutputResult)
                      have freeEq : sourceEnv ∘ sourceFree =
                          targetEnv ∘ targetFree := by
                        funext index
                        exact environments (sourceFree index) (targetFree index)
                          (portsRelated (.free index) (sourceFree index)
                            (targetFree index)
                            (VisualProof.Data.Finite.sequenceFin_sound
                              sourceFreeResult index)
                            (VisualProof.Data.Finite.sequenceFin_sound
                              targetFreeResult index))
                      simp only [Item.renameRelations, denoteItem]
                      rw [model.eval_mapFree sourceFree term sourceEnv,
                        model.eval_mapFree targetFree term targetEnv,
                        outputEq, freeEq]
                      cases direction <;> exact id
  | atom region binder =>
      have targetNodeShape :
          target.nodes targetNode =
            .atom (regionMap region) (binderMap binder) := by
        simpa only [sourceNodeShape] using nodeShape
      cases sourceBinderResult : sourceBinders binder with
      | none =>
          simp [compileNode?, sourceNodeShape, sourceBinderResult]
            at sourceCompiled
      | some sourceRelation =>
          cases sourceRelation with
          | mk arity relationVariable =>
              have binderEq :
                  targetBinders (binderMap binder) =
                    some ⟨arity, relationMap relationVariable⟩ :=
                bindersRelated region binder arity relationVariable
                  sourceNodeShape sourceBinderResult
              cases sourceArgumentsResult :
                  resolvePorts? source sourceContext sourceNode arity
                    (fun index => .arg index) with
              | none =>
                  simp [compileNode?, sourceNodeShape, sourceBinderResult,
                    sourceArgumentsResult] at sourceCompiled
              | some sourceArguments =>
                  simp [compileNode?, sourceNodeShape, sourceBinderResult,
                    sourceArgumentsResult] at sourceCompiled
                  subst sourceItem
                  cases targetArgumentsResult :
                      resolvePorts? target targetContext targetNode arity
                        (fun index => .arg index) with
                  | none =>
                      simp [compileNode?, targetNodeShape, binderEq,
                        targetArgumentsResult]
                        at targetCompiled
                  | some targetArguments =>
                      simp [compileNode?, targetNodeShape, binderEq,
                        targetArgumentsResult]
                        at targetCompiled
                      subst targetItem
                      intro sourceEnv targetEnv relEnv environments
                      have argumentsEq : sourceEnv ∘ sourceArguments =
                          targetEnv ∘ targetArguments := by
                        funext index
                        exact environments (sourceArguments index)
                          (targetArguments index)
                          (portsRelated (.arg index) (sourceArguments index)
                            (targetArguments index)
                            (VisualProof.Data.Finite.sequenceFin_sound
                              sourceArgumentsResult index)
                            (VisualProof.Data.Finite.sequenceFin_sound
                              targetArgumentsResult index))
                      rw [Item.renameRelations, denoteItem, argumentsEq]
                      cases direction <;> exact id
  | named region definition arity =>
      have targetNodeShape :
          target.nodes targetNode =
            .named (regionMap region) definition arity := by
        simpa only [sourceNodeShape] using nodeShape
      cases namedResult : namedRel? signature definition arity with
      | none =>
          simp [compileNode?, sourceNodeShape, namedResult] at sourceCompiled
      | some relationVariable =>
          cases sourceArgumentsResult :
              resolvePorts? source sourceContext sourceNode arity
                (fun index => .arg index) with
          | none =>
              simp [compileNode?, sourceNodeShape, namedResult,
                sourceArgumentsResult] at sourceCompiled
          | some sourceArguments =>
              simp [compileNode?, sourceNodeShape, namedResult,
                sourceArgumentsResult] at sourceCompiled
              subst sourceItem
              cases targetArgumentsResult :
                  resolvePorts? target targetContext targetNode arity
                    (fun index => .arg index) with
              | none =>
                  simp [compileNode?, targetNodeShape, namedResult,
                    targetArgumentsResult] at targetCompiled
              | some targetArguments =>
                  simp [compileNode?, targetNodeShape, namedResult,
                    targetArgumentsResult] at targetCompiled
                  subst targetItem
                  intro sourceEnv targetEnv relEnv environments
                  have argumentsEq : sourceEnv ∘ sourceArguments =
                      targetEnv ∘ targetArguments := by
                    funext index
                    exact environments (sourceArguments index)
                      (targetArguments index)
                      (portsRelated (.arg index) (sourceArguments index)
                        (targetArguments index)
                        (VisualProof.Data.Finite.sequenceFin_sound
                          sourceArgumentsResult index)
                        (VisualProof.Data.Finite.sequenceFin_sound
                          targetArgumentsResult index))
                  rw [Item.renameRelations, denoteItem, argumentsEq]
                  cases direction <;> exact id

/-- Semantic simulation of two intrinsic item sequences. -/
def ItemSeqSimulation (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : SimulationDirection)
    (relation : ContextIndexRelation sourceWires targetWires)
    (sourceItems : ItemSeq signature sourceWires rels)
    (targetItems : ItemSeq signature targetWires rels) : Prop :=
  ∀ (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    relation.EnvironmentsAgree sourceEnv targetEnv →
      direction.Entails
        (denoteItemSeq model named sourceEnv relEnv sourceItems)
        (denoteItemSeq model named targetEnv relEnv targetItems)

/-- Semantic simulation of two intrinsic regions under related outer
environments. -/
def RegionSimulation (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : SimulationDirection)
    (relation : ContextIndexRelation sourceOuter targetOuter)
    (sourceRegion : Region signature sourceOuter rels)
    (targetRegion : Region signature targetOuter rels) : Prop :=
  ∀ (sourceEnv : Fin sourceOuter → model.Carrier)
    (targetEnv : Fin targetOuter → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    relation.EnvironmentsAgree sourceEnv targetEnv →
      direction.Entails
        (denoteRegion model named sourceEnv relEnv sourceRegion)
        (denoteRegion model named targetEnv relEnv targetRegion)

/-- The environment on the actual extended lexical context used by
`compileOccurrencesWith?`. -/
def extendedEnvironment
    (context : WireContext diagram) (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (exactScopeWires diagram region).length → D) :
    Fin (context.extend region).length → D :=
  extendWireEnv outerEnv localEnv ∘ Fin.cast (WireContext.length_extend context region)

theorem extendedEnvironment_nil_eq_cast
    (region : Fin diagram.regionCount)
    (localEnv : Fin (exactScopeWires diagram region).length → D) :
    extendedEnvironment ([] : WireContext diagram) region Fin.elim0 localEnv =
      fun index => localEnv
        (Fin.cast (by simp [WireContext.extend]) index) := by
  funext index
  let localIndex : Fin (exactScopeWires diagram region).length :=
    Fin.cast (by simp [WireContext.extend]) index
  have cast_eq :
      Fin.cast (WireContext.length_extend
        ([] : WireContext diagram) region) index =
        Fin.natAdd 0 localIndex := by
    apply Fin.ext
    simp [localIndex]
  rw [extendedEnvironment, Function.comp_apply, cast_eq]
  exact Fin.addCases_right localIndex

/-- Proof-dependent transport of the complete local existential semantics used
by `finishRegion`.  The opposite valuation and its item denotation are produced
together, after the active item denotation is available. -/
def DirectionalLocalTransport
    (direction : SimulationDirection)
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceRegion : Fin source.regionCount) (targetRegion : Fin target.regionCount)
    (outer : ContextIndexRelation sourceContext.length targetContext.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relEnv : RelEnv model.Carrier rels)
    (sourceItems : ItemSeq signature
      (sourceContext.extend sourceRegion).length rels)
    (targetItems : ItemSeq signature
      (targetContext.extend targetRegion).length rels) : Prop :=
  ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
    (targetOuter : Fin targetContext.length → model.Carrier),
    outer.EnvironmentsAgree sourceOuter targetOuter →
      match direction with
      | .forward => ∀ sourceLocal,
          denoteItemSeq model named
            (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
            relEnv sourceItems →
          ∃ targetLocal,
            denoteItemSeq model named
              (extendedEnvironment targetContext targetRegion targetOuter targetLocal)
              relEnv targetItems
      | .backward => ∀ targetLocal,
          denoteItemSeq model named
            (extendedEnvironment targetContext targetRegion targetOuter targetLocal)
            relEnv targetItems →
          ∃ sourceLocal,
            denoteItemSeq model named
              (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
              relEnv sourceItems

/-- Adapter for structurally total simulations.  A raw valuation-selection
function plus pointwise item-sequence simulation yields the authoritative
proof-dependent local transport. -/
theorem directionalLocalTransport_of_agreement
    {source target : ConcreteDiagram}
    (direction : SimulationDirection)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceRegion : Fin source.regionCount) (targetRegion : Fin target.regionCount)
    (outer : ContextIndexRelation sourceContext.length targetContext.length)
    (extended : ContextIndexRelation
      (sourceContext.extend sourceRegion).length
      (targetContext.extend targetRegion).length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature (sourceContext.extend sourceRegion).length rels)
    (targetItems : ItemSeq signature (targetContext.extend targetRegion).length rels)
    (selection :
      ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier),
      outer.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              extended.EnvironmentsAgree
                (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
                (extendedEnvironment targetContext targetRegion targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              extended.EnvironmentsAgree
                (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
                (extendedEnvironment targetContext targetRegion targetOuter targetLocal))
    (items : ItemSeqSimulation model named direction extended sourceItems targetItems) :
    ∀ relEnv, DirectionalLocalTransport direction sourceContext targetContext
      sourceRegion targetRegion outer model named relEnv sourceItems targetItems := by
  intro relEnv sourceOuter targetOuter agrees
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      obtain ⟨targetLocal, extendedAgrees⟩ :=
        selection sourceOuter targetOuter agrees sourceLocal
      exact ⟨targetLocal,
        items
          (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
          (extendedEnvironment targetContext targetRegion targetOuter targetLocal)
          relEnv extendedAgrees sourceDenotes⟩
  | backward =>
      intro targetLocal targetDenotes
      obtain ⟨sourceLocal, extendedAgrees⟩ :=
        selection sourceOuter targetOuter agrees targetLocal
      exact ⟨sourceLocal,
        items
          (extendedEnvironment sourceContext sourceRegion sourceOuter sourceLocal)
          (extendedEnvironment targetContext targetRegion targetOuter targetLocal)
          relEnv extendedAgrees targetDenotes⟩

namespace MaskedCutTransportValidation

private def falseRelation : NamedRel [0] 0 where
  index := 0
  hasArity := rfl

private def falseNamedEnv (D : Type) : NamedEnv D [0] :=
  fun _ _ _ => False

private def maskedCutItems (wires : Nat) : ItemSeq [0] wires [] :=
  .cons
    (.cut (.mk 0
      (.cons (.named falseRelation (fun index => Fin.elim0 index)) .nil)))
    .nil

/-- A cut whose body begins with a false conjunct is true without exposing a
valuation or proof for anything later in that body. -/
private theorem maskedCutItems_denote
    (model : Lambda.LambdaModel)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier []) :
    denoteItemSeq model (falseNamedEnv model.Carrier) env relEnv
      (maskedCutItems wires) := by
  constructor
  · rintro ⟨localEnv, bodyHead, bodyTail⟩
    exact bodyHead
  · trivial

/-- The implication-shaped contract accepts the masked cut directly.  It
chooses only the enclosing region's existential valuation; no valuation from
inside the negative branch is required or manufactured. -/
example
    {source target : ConcreteDiagram}
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceRegion : Fin source.regionCount) (targetRegion : Fin target.regionCount)
    (outer : ContextIndexRelation sourceContext.length targetContext.length)
    (model : Lambda.LambdaModel) :
    DirectionalLocalTransport (rels := []) .forward sourceContext targetContext
      sourceRegion targetRegion outer model (falseNamedEnv model.Carrier)
      PUnit.unit .nil (maskedCutItems (targetContext.extend targetRegion).length) := by
  intro sourceOuter targetOuter outerAgrees sourceLocal sourceDenotes
  let fallback : model.Carrier :=
    model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
      Lambda.Term 0 (Fin 0)) Fin.elim0
  let targetLocal : Fin (exactScopeWires target targetRegion).length →
      model.Carrier := fun _ => fallback
  exact ⟨targetLocal, maskedCutItems_denote model _ PUnit.unit⟩

end MaskedCutTransportValidation

/-- Lift the authoritative local implication through `finishRegion`. -/
theorem finishRegion_denote
    {source target : ConcreteDiagram}
    (direction : SimulationDirection)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceRegion : Fin source.regionCount) (targetRegion : Fin target.regionCount)
    (outer : ContextIndexRelation sourceContext.length targetContext.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature (sourceContext.extend sourceRegion).length rels)
    (targetItems : ItemSeq signature (targetContext.extend targetRegion).length rels)
    (transport : ∀ relEnv, DirectionalLocalTransport direction sourceContext
      targetContext sourceRegion targetRegion outer model named relEnv
      sourceItems targetItems) :
    RegionSimulation model named direction outer
      (finishRegion source sourceContext sourceRegion sourceItems)
      (finishRegion target targetContext targetRegion targetItems) := by
  intro sourceOuter targetOuter relEnv agrees
  letI : Nonempty model.Carrier := lambdaModel_carrier_nonempty model
  unfold finishRegion
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
  cases direction with
  | forward =>
      rintro ⟨sourceLocal, sourceDenotes⟩
      have sourceRaw := (denoteItemSeq_renameWires model named
        (Fin.cast (WireContext.length_extend sourceContext sourceRegion))
        (extendWireEnv sourceOuter sourceLocal) relEnv sourceItems).mp sourceDenotes
      obtain ⟨targetLocal, targetRaw⟩ :=
        transport relEnv sourceOuter targetOuter agrees sourceLocal sourceRaw
      refine ⟨targetLocal, ?_⟩
      exact (denoteItemSeq_renameWires model named
        (Fin.cast (WireContext.length_extend targetContext targetRegion))
        (extendWireEnv targetOuter targetLocal) relEnv targetItems).mpr targetRaw
  | backward =>
      rintro ⟨targetLocal, targetDenotes⟩
      have targetRaw := (denoteItemSeq_renameWires model named
        (Fin.cast (WireContext.length_extend targetContext targetRegion))
        (extendWireEnv targetOuter targetLocal) relEnv targetItems).mp targetDenotes
      obtain ⟨sourceLocal, sourceRaw⟩ :=
        transport relEnv sourceOuter targetOuter agrees targetLocal targetRaw
      refine ⟨sourceLocal, ?_⟩
      exact (denoteItemSeq_renameWires model named
        (Fin.cast (WireContext.length_extend sourceContext sourceRegion))
        (extendWireEnv sourceOuter sourceLocal) relEnv sourceItems).mpr sourceRaw

/-- Relation renaming commutes with packaging compiled local occurrences. -/
theorem finishRegion_renameRelations
    {source : ConcreteDiagram}
    (sourceContext : WireContext source)
    (sourceRegion : Fin source.regionCount)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceItems : ItemSeq signature
      (sourceContext.extend sourceRegion).length sourceRels) :
    (finishRegion source sourceContext sourceRegion sourceItems).renameRelations
        relationMap =
      finishRegion source sourceContext sourceRegion
        (sourceItems.renameRelations relationMap) := by
  simp only [finishRegion, Region.renameRelations,
    ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_renameRelations]

/-- The environment on the concatenated root context used by
`compileRoot?`. -/
def rootEnvironment (ambient locals : WireContext diagram)
    (outerEnv : Fin ambient.length → D)
    (localEnv : Fin locals.length → D) :
    Fin (ambient ++ locals).length → D :=
  extendWireEnv outerEnv localEnv ∘ Fin.cast (by simp)

/-- Proof-dependent transport of the complete hidden-root existential
semantics. -/
def DirectionalRootTransport (direction : SimulationDirection)
    {source target : ConcreteDiagram}
    (sourceAmbient sourceLocals : WireContext source)
    (targetAmbient targetLocals : WireContext target)
    (outer : ContextIndexRelation sourceAmbient.length targetAmbient.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature
      (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq signature
      (targetAmbient ++ targetLocals).length []) : Prop :=
  ∀ (sourceOuter : Fin sourceAmbient.length → model.Carrier)
    (targetOuter : Fin targetAmbient.length → model.Carrier)
    (relEnv : RelEnv model.Carrier []),
    outer.EnvironmentsAgree sourceOuter targetOuter →
      match direction with
      | .forward => ∀ sourceLocal,
          denoteItemSeq model named
            (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
            relEnv sourceItems →
          ∃ targetLocal,
            denoteItemSeq model named
              (rootEnvironment targetAmbient targetLocals targetOuter targetLocal)
              relEnv targetItems
      | .backward => ∀ targetLocal,
          denoteItemSeq model named
            (rootEnvironment targetAmbient targetLocals targetOuter targetLocal)
            relEnv targetItems →
          ∃ sourceLocal,
            denoteItemSeq model named
              (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
              relEnv sourceItems

/-- Structural adapter for root transports. -/
theorem directionalRootTransport_of_agreement
    {source target : ConcreteDiagram}
    (direction : SimulationDirection)
    (sourceAmbient sourceLocals : WireContext source)
    (targetAmbient targetLocals : WireContext target)
    (outer : ContextIndexRelation sourceAmbient.length targetAmbient.length)
    (combined : ContextIndexRelation
      (sourceAmbient ++ sourceLocals).length
      (targetAmbient ++ targetLocals).length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq signature (targetAmbient ++ targetLocals).length [])
    (selection : ∀ (sourceOuter : Fin sourceAmbient.length → model.Carrier)
      (targetOuter : Fin targetAmbient.length → model.Carrier),
      outer.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              combined.EnvironmentsAgree
                (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
                (rootEnvironment targetAmbient targetLocals targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              combined.EnvironmentsAgree
                (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
                (rootEnvironment targetAmbient targetLocals targetOuter targetLocal))
    (items : ItemSeqSimulation model named direction combined sourceItems targetItems) :
    DirectionalRootTransport direction sourceAmbient sourceLocals targetAmbient
      targetLocals outer model named sourceItems targetItems := by
  intro sourceOuter targetOuter relEnv agrees
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      obtain ⟨targetLocal, combinedAgrees⟩ :=
        selection sourceOuter targetOuter agrees sourceLocal
      exact ⟨targetLocal,
        items
          (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
          (rootEnvironment targetAmbient targetLocals targetOuter targetLocal)
          relEnv combinedAgrees sourceDenotes⟩
  | backward =>
      intro targetLocal targetDenotes
      obtain ⟨sourceLocal, combinedAgrees⟩ :=
        selection sourceOuter targetOuter agrees targetLocal
      exact ⟨sourceLocal,
        items
          (rootEnvironment sourceAmbient sourceLocals sourceOuter sourceLocal)
          (rootEnvironment targetAmbient targetLocals targetOuter targetLocal)
          relEnv combinedAgrees targetDenotes⟩

/-- Lift the authoritative root implication through `finishRoot`. -/
theorem finishRoot_denote
    {source target : ConcreteDiagram}
    (direction : SimulationDirection)
    (sourceAmbient sourceLocals : WireContext source)
    (targetAmbient targetLocals : WireContext target)
    (outer : ContextIndexRelation sourceAmbient.length targetAmbient.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceItems : ItemSeq signature (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq signature (targetAmbient ++ targetLocals).length [])
    (transport : DirectionalRootTransport direction sourceAmbient sourceLocals
      targetAmbient targetLocals outer model named sourceItems targetItems) :
    RegionSimulation model named direction outer
      (finishRoot sourceAmbient sourceLocals sourceItems)
      (finishRoot targetAmbient targetLocals targetItems) := by
  intro sourceOuter targetOuter relEnv agrees
  letI : Nonempty model.Carrier := lambdaModel_carrier_nonempty model
  unfold finishRoot
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
  cases direction with
  | forward =>
      rintro ⟨sourceLocal, sourceDenotes⟩
      have sourceRaw := (denoteItemSeq_renameWires model named
        (Fin.cast (by simp)) (extendWireEnv sourceOuter sourceLocal)
        relEnv sourceItems).mp sourceDenotes
      obtain ⟨targetLocal, targetRaw⟩ :=
        transport sourceOuter targetOuter relEnv agrees sourceLocal sourceRaw
      refine ⟨targetLocal, ?_⟩
      exact (denoteItemSeq_renameWires model named
        (Fin.cast (by simp)) (extendWireEnv targetOuter targetLocal)
        relEnv targetItems).mpr targetRaw
  | backward =>
      rintro ⟨targetLocal, targetDenotes⟩
      have targetRaw := (denoteItemSeq_renameWires model named
        (Fin.cast (by simp)) (extendWireEnv targetOuter targetLocal)
        relEnv targetItems).mp targetDenotes
      obtain ⟨sourceLocal, sourceRaw⟩ :=
        transport sourceOuter targetOuter relEnv agrees targetLocal targetRaw
      refine ⟨sourceLocal, ?_⟩
      exact (denoteItemSeq_renameWires model named
        (Fin.cast (by simp)) (extendWireEnv sourceOuter sourceLocal)
        relEnv sourceItems).mpr sourceRaw

/-- The rule-independent data needed to simulate the sole concrete compiler.
A rule-owned witness validates each lexical context pair and projects its
index relation, so this structure does not privilege embeddings over
collapses or erase their concrete provenance. `Allowed` records the semantic
direction available at a region; cuts flip it and bubbles preserve it. -/
structure ConcreteSemanticSimulation (signature : List Nat)
    (source target : ConcreteDiagram) (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) where
  source_wellFormed : source.WellFormed signature
  target_wellFormed : target.WellFormed signature
  regionMap : Fin source.regionCount → Fin target.regionCount
  binderMap : Fin source.regionCount → Fin target.regionCount
  /-- A focused region owns its complete local source/target replacement.  Its
  nodes and descendants need not have pointwise images. -/
  Distinguished : Fin source.regionCount → Prop
  occurrenceMap : ∀ region, ¬ Distinguished region →
    LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount
  occurrenceMap_node : ∀ region (regular : ¬ Distinguished region) node,
    (source.nodes node).region = region →
      ∃ targetNode,
        occurrenceMap region regular (.node node) = .node targetNode
  occurrenceMap_child : ∀ region (regular : ¬ Distinguished region) child,
    occurrenceMap region regular (.child child) = .child (regionMap child)
  root_eq : target.root = regionMap source.root
  /-- Child wrappers in the unchanged frame agree.  A distinguished child may
  still be mapped as one opaque cut/bubble occurrence; only its interior is
  exempt from pointwise correspondence. -/
  region_shape : ∀ parent, ¬ Distinguished parent → ∀ child,
    (source.regions child).parent? = some parent →
    target.regions (regionMap child) =
      match source.regions child with
      | .sheet => .sheet
      | .cut childParent => .cut (regionMap childParent)
      | .bubble childParent arity => .bubble (regionMap childParent) arity
  localOccurrences_map : ∀ region (regular : ¬ Distinguished region),
    localOccurrences target (regionMap region) =
      (localOccurrences source region).map (occurrenceMap region regular)
  BinderWitness : ∀ {sourceRels targetRels : RelCtx},
    BinderContext source sourceRels → BinderContext target targetRels → Type
  relationMap : ∀ {sourceRels targetRels : RelCtx}
    {sourceBinders : BinderContext source sourceRels}
    {targetBinders : BinderContext target targetRels},
    BinderWitness sourceBinders targetBinders →
      RelationRenaming sourceRels targetRels
  binders_empty : BinderWitness BinderContext.empty BinderContext.empty
  binders_push : ∀ {sourceRels targetRels : RelCtx}
    {sourceBinders : BinderContext source sourceRels}
    {targetBinders : BinderContext target targetRels}
    (witness : BinderWitness sourceBinders targetBinders)
    (child parent : Fin source.regionCount) (arity : Nat),
    source.regions child = .bubble parent arity →
      ¬ Distinguished parent →
      BinderWitness (sourceBinders.push child arity)
        (targetBinders.push (regionMap child) arity)
  relationMap_push : ∀ {sourceRels targetRels : RelCtx}
    {sourceBinders : BinderContext source sourceRels}
    {targetBinders : BinderContext target targetRels}
    (witness : BinderWitness sourceBinders targetBinders)
    (child parent : Fin source.regionCount) (arity : Nat)
    (childKind : source.regions child = .bubble parent arity)
    (regular : ¬ Distinguished parent),
    (relationMap
        (binders_push witness child parent arity childKind regular) :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift (relationMap witness) arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels))
  Allowed : SimulationDirection → Fin source.regionCount → Prop
  allowed_cut : ∀ direction child parent,
    source.regions child = .cut parent → ¬ Distinguished parent →
      Allowed direction parent →
      Allowed direction.flip child
  allowed_bubble : ∀ direction child parent arity,
    source.regions child = .bubble parent arity → ¬ Distinguished parent →
      Allowed direction parent →
      Allowed direction child
  /-- Rule-owned evidence that a pair of lexical contexts is related by the
  concrete surgery.  This retains the wire-lookup provenance that a bare
  semantic relation cannot express. -/
  ContextWitness : WireContext source → WireContext target → Type
  /-- Concrete traversal provenance identifying which region is being compiled
  under a validated lexical-context pair.  This prevents focused kernels from
  being invoked at unrelated distinguished regions that merely admit the same
  wire context. -/
  AtRegion : ∀ {sourceContext : WireContext source}
    {targetContext : WireContext target},
    ContextWitness sourceContext targetContext →
      Fin source.regionCount → Prop
  /-- Project the semantic index relation from validated concrete context
  evidence. -/
  indexRelation : ∀ {sourceContext : WireContext source}
    {targetContext : WireContext target},
    ContextWitness sourceContext targetContext →
      ContextIndexRelation sourceContext.length targetContext.length
  /-- Extend validated context evidence across one corresponding lexical
  region. -/
  extendContext : ∀ (sourceContext : WireContext source)
    (targetContext : WireContext target),
    ContextWitness sourceContext targetContext →
      ∀ region,
        (regular : ¬ Distinguished region) →
        (sourceContext.extend region).Exact region →
        (targetContext.extend (regionMap region)).Exact (regionMap region) →
        ContextWitness (sourceContext.extend region)
          (targetContext.extend (regionMap region))
  /-- Extend validated context evidence at the focused region.  The focused
  kernel may still need the authoritative recursive theorem for retained
  frame children, even though pattern material is handled opaquely. -/
  extendFocusedContext : ∀ (sourceContext : WireContext source)
    (targetContext : WireContext target),
    (context : ContextWitness sourceContext targetContext) →
      ∀ region,
        AtRegion context region →
        Distinguished region →
        (sourceContext.extend region).Exact region →
        (targetContext.extend (regionMap region)).Exact (regionMap region) →
        ContextWitness (sourceContext.extend region)
          (targetContext.extend (regionMap region))
  /-- The recursive compiler reaches a child only through the actual
  direct-parent occurrence currently being traversed. -/
  at_child : ∀ (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (parent : Fin source.regionCount)
    (regular : ¬ Distinguished parent)
    (sourceExact : (sourceContext.extend parent).Exact parent)
    (targetExact :
      (targetContext.extend (regionMap parent)).Exact (regionMap parent))
    (child : Fin source.regionCount),
    (atParent : AtRegion context parent) →
      (source.regions child).parent? = some parent →
      AtRegion
        (extendContext sourceContext targetContext context parent regular
          sourceExact targetExact)
        child
  /-- Extending the lexical wire context preserves traversal provenance for
  compiling the current region's direct occurrences. -/
  at_extended : ∀ (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (region : Fin source.regionCount)
    (regular : ¬ Distinguished region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (regionMap region)).Exact (regionMap region)),
    AtRegion context region →
      AtRegion
        (extendContext sourceContext targetContext context region regular
          sourceExact targetExact)
        region
  /-- A child under a focused region is recursively available only when it is
  a direct child on both sides.  This excludes opaque replacement material
  whose source regions collapse to the target focus. -/
  at_focused_child : ∀ (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (parent : Fin source.regionCount)
    (focused : Distinguished parent)
    (sourceExact : (sourceContext.extend parent).Exact parent)
    (targetExact :
      (targetContext.extend (regionMap parent)).Exact (regionMap parent))
    (child : Fin source.regionCount),
    (atParent : AtRegion context parent) →
      (source.regions child).parent? = some parent →
      (target.regions (regionMap child)).parent? = some (regionMap parent) →
      AtRegion
        (extendFocusedContext sourceContext targetContext context parent
          atParent focused sourceExact targetExact)
        child
  localTransport : ∀ {sourceRels targetRels : RelCtx} direction
    (fuelSource fuelTarget : Nat)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (binderWitness : BinderWitness sourceBinders targetBinders)
    (region : Fin source.regionCount),
    AtRegion context region →
      (regular : ¬ Distinguished region) → Allowed direction region →
      ∀ (sourceExact : (sourceContext.extend region).Exact region)
        (targetExact : (targetContext.extend (regionMap region)).Exact
          (regionMap region)),
      sourceBinders.Covers region →
      targetBinders.Covers (regionMap region) →
      BinderContext.Enumeration source sourceBinders region →
      BinderContext.Enumeration target targetBinders (regionMap region) →
      ∀ (sourceItems : ItemSeq signature
          (sourceContext.extend region).length sourceRels)
        (targetItems : ItemSeq signature
          (targetContext.extend (regionMap region)).length targetRels),
      compileOccurrencesWith? signature source
          (compileRegion? signature source fuelSource)
          (sourceContext.extend region) sourceBinders
          (localOccurrences source region) = some sourceItems →
      compileOccurrencesWith? signature target
          (compileRegion? signature target fuelTarget)
          (targetContext.extend (regionMap region)) targetBinders
          (localOccurrences target (regionMap region)) = some targetItems →
      ItemSeqSimulation model named direction
        (indexRelation (extendContext sourceContext targetContext context region
          regular sourceExact targetExact))
        (sourceItems.renameRelations (relationMap binderWitness)) targetItems →
      ∀ relEnv,
        DirectionalLocalTransport direction sourceContext targetContext
          region (regionMap region) (indexRelation context)
          model named relEnv
          (sourceItems.renameRelations (relationMap binderWitness)) targetItems
  /-- The distinguished local logical law.  Unchanged nodes normally use a
  public `compileNode?` mapping kernel; a rewritten node supplies its own
  semantic law here. -/
  nodeSemantic : ∀ {sourceRels targetRels : RelCtx} direction
    (region : Fin source.regionCount)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (atRegion : AtRegion context region)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels),
    Allowed direction region →
      (binderWitness : BinderWitness sourceBinders targetBinders) →
      ∀ (sourceNode : Fin source.nodeCount)
        (targetNode : Fin target.nodeCount),
      ∀ (regular : ¬ Distinguished region),
      occurrenceMap region regular (.node sourceNode) = .node targetNode →
      (source.nodes sourceNode).region = region →
      ∀ (sourceItem : Item signature sourceContext.length sourceRels)
        (targetItem : Item signature targetContext.length targetRels),
      compileNode? signature source sourceContext sourceBinders sourceNode =
          some sourceItem →
      compileNode? signature target targetContext targetBinders targetNode =
          some targetItem →
      ItemSimulation model named direction (indexRelation context)
        (sourceItem.renameRelations (relationMap binderWitness)) targetItem
  /-- The one rule-specific region kernel for a focused replacement.  It owns
  the existential local witnesses, so a target witness may depend on the
  source denotation proof. Both sides compile independently and may add or
  delete nodes and descendant regions. -/
  focusedRegionKernel : ∀ {sourceRels targetRels : RelCtx} direction
    (fuelSource fuelTarget : Nat) (region : Fin source.regionCount)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (context : ContextWitness sourceContext targetContext)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels),
    (atRegion : AtRegion context region) →
      (focused : Distinguished region) →
      (allowed : Allowed direction region) →
      (binderWitness : BinderWitness sourceBinders targetBinders) →
      (sourceExact : (sourceContext.extend region).Exact region) →
      (targetExact :
        (targetContext.extend (regionMap region)).Exact (regionMap region)) →
      (sourceBindersCover : sourceBinders.Covers region) →
      (targetBindersCover : targetBinders.Covers (regionMap region)) →
      (sourceEnumeration :
        BinderContext.Enumeration source sourceBinders region) →
      (targetEnumeration :
        BinderContext.Enumeration target targetBinders (regionMap region)) →
      (∀ {childDirection : SimulationDirection}
        {child : Fin source.regionCount}
        {childSourceRels childTargetRels : RelCtx}
        {childSourceBinders : BinderContext source childSourceRels}
        {childTargetBinders : BinderContext target childTargetRels}
        {sourceBody : Region signature
          (sourceContext.extend region).length childSourceRels}
        {targetBody : Region signature
          (targetContext.extend (regionMap region)).length childTargetRels},
        (source.regions child).parent? = some region →
        (target.regions (regionMap child)).parent? = some (regionMap region) →
        Allowed childDirection child →
        (childBinderWitness :
          BinderWitness childSourceBinders childTargetBinders) →
        childSourceBinders.Covers child →
        childTargetBinders.Covers (regionMap child) →
        BinderContext.Enumeration source childSourceBinders child →
        BinderContext.Enumeration target childTargetBinders
          (regionMap child) →
        compileRegion? signature source fuelSource child
            (sourceContext.extend region) childSourceBinders = some sourceBody →
        compileRegion? signature target fuelTarget (regionMap child)
            (targetContext.extend (regionMap region)) childTargetBinders =
          some targetBody →
        RegionSimulation model named childDirection
          (indexRelation
            (extendFocusedContext sourceContext targetContext context region
              atRegion focused sourceExact targetExact))
          (sourceBody.renameRelations (relationMap childBinderWitness))
          targetBody) →
      -- Focused rewrites may reparent retained material through fresh wrappers.
      (∀ {childDirection : SimulationDirection}
        {child : Fin source.regionCount}
        {childSourceRels childTargetRels : RelCtx}
        {childSourceBinders : BinderContext source childSourceRels}
        {childTargetBinders : BinderContext target childTargetRels}
        (childFuelTarget : Nat)
        (childSourceContext : WireContext source)
        (childTargetContext : WireContext target)
        (childContext : ContextWitness childSourceContext childTargetContext),
        AtRegion childContext child →
        Allowed childDirection child →
        (childBinderWitness :
          BinderWitness childSourceBinders childTargetBinders) →
        childSourceBinders.Covers child →
        childTargetBinders.Covers (regionMap child) →
        BinderContext.Enumeration source childSourceBinders child →
        BinderContext.Enumeration target childTargetBinders
          (regionMap child) →
        (childSourceContext.extend child).Exact child →
        (childTargetContext.extend (regionMap child)).Exact
          (regionMap child) →
        ∀ (sourceBody : Region signature
            childSourceContext.length childSourceRels)
          (targetBody : Region signature
            childTargetContext.length childTargetRels),
        compileRegion? signature source fuelSource child
            childSourceContext childSourceBinders = some sourceBody →
        compileRegion? signature target childFuelTarget (regionMap child)
            childTargetContext childTargetBinders = some targetBody →
        RegionSimulation model named childDirection
          (indexRelation childContext)
          (sourceBody.renameRelations
            (relationMap childBinderWitness))
          targetBody) →
      ∀ (sourceItems : ItemSeq signature
          (sourceContext.extend region).length sourceRels)
        (targetItems : ItemSeq signature
          (targetContext.extend (regionMap region)).length targetRels),
      compileOccurrencesWith? signature source
          (compileRegion? signature source fuelSource)
          (sourceContext.extend region) sourceBinders
          (localOccurrences source region) = some sourceItems →
      compileOccurrencesWith? signature target
          (compileRegion? signature target fuelTarget)
          (targetContext.extend (regionMap region)) targetBinders
          (localOccurrences target (regionMap region)) = some targetItems →
      RegionSimulation model named direction (indexRelation context)
        ((finishRegion source sourceContext region sourceItems).renameRelations
          (relationMap binderWitness))
        (finishRegion target targetContext (regionMap region) targetItems)

namespace ConcreteSemanticSimulation

private theorem relationRenaming_empty_eq_identity
    (relationMap : RelationRenaming [] []) :
    (relationMap : RelationRenaming [] []) =
      (identityRelationRenaming [] : RelationRenaming [] []) := by
  apply @funext
  intro arity
  funext relation
  exact Fin.elim0 relation.index

private theorem Region.renameRelations_empty
    (region : Region signature wires [])
    (relationMap : RelationRenaming [] []) :
    region.renameRelations relationMap = region := by
  rw [relationRenaming_empty_eq_identity relationMap]
  exact Region.renameRelations_id region

private theorem ItemSeq.renameRelations_empty
    (items : ItemSeq signature wires [])
    (relationMap : RelationRenaming [] []) :
    items.renameRelations relationMap = items := by
  rw [relationRenaming_empty_eq_identity relationMap]
  exact ItemSeq.renameRelations_id items

private theorem parent_mapped
    (simulation : ConcreteSemanticSimulation signature source target model named)
    {child parent : Fin source.regionCount}
    (regular : ¬ simulation.Distinguished parent)
    (hparent : (source.regions child).parent? = some parent) :
    (target.regions (simulation.regionMap child)).parent? =
      some (simulation.regionMap parent) := by
  have shape := simulation.region_shape parent regular child hparent
  cases hkind : source.regions child with
  | sheet =>
      rw [hkind] at hparent
      simp [CRegion.parent?] at hparent
  | cut actualParent =>
      rw [hkind] at hparent
      have : actualParent = parent := Option.some.inj hparent
      subst actualParent
      simpa [hkind] using congrArg CRegion.parent? shape
  | bubble actualParent arity =>
      rw [hkind] at hparent
      have : actualParent = parent := Option.some.inj hparent
      subst actualParent
      simpa [hkind] using congrArg CRegion.parent? shape

/-- Generic semantic simulation of one mapped direct occurrence.  Nodes use
the distinguished local kernel; cuts and bubbles are discharged here from the
recursive region simulation, including polarity reversal under cuts. -/
theorem compileOccurrence_denote
    (simulation : ConcreteSemanticSimulation signature source target model named)
    {sourceRels targetRels : RelCtx} (direction : SimulationDirection)
    (fuelSource fuelTarget : Nat) (region : Fin source.regionCount)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (context : simulation.ContextWitness sourceContext targetContext)
    (atRegion : simulation.AtRegion context region)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (allowed : simulation.Allowed direction region)
    (regular : ¬ simulation.Distinguished region)
    (binderWitness : simulation.BinderWitness sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers region)
    (targetBindersCover :
      targetBinders.Covers (simulation.regionMap region))
    (sourceEnumeration :
      BinderContext.Enumeration source sourceBinders region)
    (targetEnumeration :
      BinderContext.Enumeration target targetBinders
        (simulation.regionMap region))
    (recurse : ∀ {childDirection : SimulationDirection}
      {child : Fin source.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : BinderContext source childSourceRels}
      {childTargetBinders : BinderContext target childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      (source.regions child).parent? = some region →
      simulation.Allowed childDirection child →
      (childBinderWitness :
        simulation.BinderWitness childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (simulation.regionMap child) →
      BinderContext.Enumeration source childSourceBinders child →
      BinderContext.Enumeration target childTargetBinders
        (simulation.regionMap child) →
      compileRegion? signature source fuelSource child sourceContext
          childSourceBinders = some sourceBody →
      compileRegion? signature target fuelTarget (simulation.regionMap child)
          targetContext childTargetBinders = some targetBody →
      RegionSimulation model named childDirection (simulation.indexRelation context)
        (sourceBody.renameRelations
          (simulation.relationMap childBinderWitness)) targetBody)
    (occurrence : LocalOccurrence source.regionCount source.nodeCount)
    (member : occurrence ∈ localOccurrences source region)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : compileOccurrenceWith? signature source
      (compileRegion? signature source fuelSource) sourceContext sourceBinders
      occurrence = some sourceItem)
    (targetCompiled : compileOccurrenceWith? signature target
      (compileRegion? signature target fuelTarget) targetContext targetBinders
      (simulation.occurrenceMap region regular occurrence) = some targetItem) :
    ItemSimulation model named direction (simulation.indexRelation context)
      (sourceItem.renameRelations (simulation.relationMap binderWitness))
      targetItem := by
  cases occurrence with
  | node node =>
      have nodeRegion := (mem_localOccurrences_node source region node).mp member
      obtain ⟨targetNode, mapped⟩ :=
        simulation.occurrenceMap_node region regular node nodeRegion
      rw [mapped] at targetCompiled
      exact simulation.nodeSemantic direction region sourceContext targetContext
        context atRegion sourceNodup targetNodup sourceBinders targetBinders allowed
        binderWitness node targetNode regular mapped
        nodeRegion sourceItem targetItem sourceCompiled targetCompiled
  | child child =>
      have parent := (mem_localOccurrences_child source region child).mp member
      rw [simulation.occurrenceMap_child region regular] at targetCompiled
      cases kind : source.regions child with
      | sheet =>
          simp [compileOccurrenceWith?, kind] at sourceCompiled
      | cut actualParent =>
          have parentEq : actualParent = region := by
            rw [kind] at parent
            exact Option.some.inj parent
          subst actualParent
          have targetKind := simulation.region_shape region regular child parent
          simp only [kind] at targetKind
          cases sourceResult : compileRegion? signature source fuelSource child
              sourceContext sourceBinders with
          | none =>
              simp [compileOccurrenceWith?, kind, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [compileOccurrenceWith?, kind, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : compileRegion? signature target fuelTarget
                  (simulation.regionMap child) targetContext targetBinders with
              | none =>
                  simp [compileOccurrenceWith?, targetKind, targetResult]
                    at targetCompiled
              | some targetBody =>
                  simp [compileOccurrenceWith?, targetKind, targetResult]
                    at targetCompiled
                  subst targetItem
                  have bodies := recurse
                    parent
                    (simulation.allowed_cut direction child region kind regular allowed)
                    binderWitness
                    (BinderContext.covers_cut_child sourceBindersCover kind)
                    (BinderContext.covers_cut_child targetBindersCover targetKind)
                    (sourceEnumeration.cutChild simulation.source_wellFormed kind)
                    (targetEnumeration.cutChild simulation.target_wellFormed
                      targetKind)
                    sourceResult targetResult
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment := bodies sourceEnv targetEnv
                    relEnv environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble actualParent arity =>
          have parentEq : actualParent = region := by
            rw [kind] at parent
            exact Option.some.inj parent
          subst actualParent
          have targetKind := simulation.region_shape region regular child parent
          simp only [kind] at targetKind
          let sourcePushed := sourceBinders.push child arity
          let targetPushed := targetBinders.push (simulation.regionMap child) arity
          cases sourceResult : compileRegion? signature source fuelSource child
              sourceContext sourcePushed with
          | none =>
              simp [compileOccurrenceWith?, kind, sourcePushed, sourceResult]
                at sourceCompiled
          | some sourceBody =>
              simp [compileOccurrenceWith?, kind, sourcePushed, sourceResult]
                at sourceCompiled
              subst sourceItem
              cases targetResult : compileRegion? signature target fuelTarget
                  (simulation.regionMap child) targetContext targetPushed with
              | none =>
                  simp [compileOccurrenceWith?, targetKind, targetPushed,
                    targetResult] at targetCompiled
              | some targetBody =>
                  simp [compileOccurrenceWith?, targetKind, targetPushed,
                    targetResult] at targetCompiled
                  subst targetItem
                  let pushedWitness := simulation.binders_push binderWitness
                    child region arity kind regular
                  have bodies := recurse
                    parent
                    (simulation.allowed_bubble direction child region arity kind
                      regular allowed)
                    pushedWitness
                    (BinderContext.push_covers_bubble_child sourceBindersCover kind)
                    (BinderContext.push_covers_bubble_child targetBindersCover
                      targetKind)
                    (sourceEnumeration.bubbleChild simulation.source_wellFormed
                      kind)
                    (targetEnumeration.bubbleChild simulation.target_wellFormed
                      targetKind)
                    sourceResult targetResult
                  have pushedMap :
                      (simulation.relationMap pushedWitness :
                        RelationRenaming (arity :: sourceRels)
                          (arity :: targetRels)) =
                        (RelationRenaming.lift
                          (simulation.relationMap binderWitness) arity :
                            RelationRenaming (arity :: sourceRels)
                              (arity :: targetRels)) := by
                    simpa only [pushedWitness] using
                      simulation.relationMap_push binderWitness child region
                        arity kind regular
                  rw [pushedMap] at bodies
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv
                          (relationValue, relEnv) environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv
                          (relationValue, relEnv) environments targetDenotes⟩

/-- Lift an arbitrary pointwise occurrence simulation to the compiled
conjunction.  This is the focused-rewrite seam: the occurrence map need not be
the regular frame map, so retained material may be reparented through freshly
inserted wrappers. -/
theorem compileOccurrences_denote_of_pointwise
    {source target : ConcreteDiagram}
    {sourceRels targetRels : RelCtx}
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : SimulationDirection)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin source.regionCount) → (context : WireContext source) →
        BinderContext source rels →
          Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin target.regionCount) → (context : WireContext target) →
        BinderContext target rels →
          Option (Region signature context.length rels))
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (relation : ContextIndexRelation sourceContext.length targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (mapOccurrence : LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount)
    (occurrences : List
      (LocalOccurrence source.regionCount source.nodeCount))
    (pointwise : ∀ occurrence, occurrence ∈ occurrences →
      ∀ (sourceItem : Item signature sourceContext.length sourceRels)
        (targetItem : Item signature targetContext.length targetRels),
      compileOccurrenceWith? signature source sourceRecurse sourceContext
          sourceBinders occurrence = some sourceItem →
      compileOccurrenceWith? signature target targetRecurse targetContext
          targetBinders (mapOccurrence occurrence) = some targetItem →
      ItemSimulation model named direction relation
        (sourceItem.renameRelations relationMap) targetItem)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : compileOccurrencesWith? signature source sourceRecurse
      sourceContext sourceBinders occurrences = some sourceItems)
    (targetCompiled : compileOccurrencesWith? signature target targetRecurse
      targetContext targetBinders (occurrences.map mapOccurrence) =
        some targetItems) :
    ItemSeqSimulation model named direction relation
      (sourceItems.renameRelations relationMap) targetItems := by
  induction occurrences generalizing sourceItems targetItems with
  | nil =>
      simp [compileOccurrencesWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      intro sourceEnv targetEnv relEnv environments
      cases direction <;>
        simp [ItemSeq.renameRelations, SimulationDirection.Entails]
  | cons occurrence rest induction =>
      simp only [compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceHeadResult : compileOccurrenceWith? signature source
          sourceRecurse sourceContext sourceBinders occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult : compileOccurrencesWith? signature source
              sourceRecurse sourceContext sourceBinders rest with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              cases targetHeadResult : compileOccurrenceWith? signature target
                  targetRecurse targetContext targetBinders
                  (mapOccurrence occurrence) with
              | none => simp [targetHeadResult] at targetCompiled
              | some targetHead =>
                  cases targetTailResult : compileOccurrencesWith?
                      signature target targetRecurse targetContext targetBinders
                      (rest.map mapOccurrence) with
                  | none =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                  | some targetTail =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                      subst targetItems
                      have head := pointwise occurrence (by simp) sourceHead
                        targetHead sourceHeadResult targetHeadResult
                      have tail := induction
                        (fun current currentMember sourceItem targetItem =>
                          pointwise current (by simp [currentMember])
                            sourceItem targetItem)
                        sourceTail targetTail sourceTailResult targetTailResult
                      intro sourceEnv targetEnv relEnv environments
                      exact direction.entails_and
                        (head sourceEnv targetEnv relEnv environments)
                        (tail sourceEnv targetEnv relEnv environments)

/-- Lift pointwise mapped-occurrence simulation to the compiled conjunction. -/
theorem compileOccurrences_denote
    (simulation : ConcreteSemanticSimulation signature source target model named)
    {sourceRels targetRels : RelCtx} (direction : SimulationDirection)
    (fuelSource fuelTarget : Nat) (region : Fin source.regionCount)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (context : simulation.ContextWitness sourceContext targetContext)
    (atRegion : simulation.AtRegion context region)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (allowed : simulation.Allowed direction region)
    (regular : ¬ simulation.Distinguished region)
    (binderWitness : simulation.BinderWitness sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers region)
    (targetBindersCover :
      targetBinders.Covers (simulation.regionMap region))
    (sourceEnumeration :
      BinderContext.Enumeration source sourceBinders region)
    (targetEnumeration :
      BinderContext.Enumeration target targetBinders
        (simulation.regionMap region))
    (recurse : ∀ {childDirection : SimulationDirection}
      {child : Fin source.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : BinderContext source childSourceRels}
      {childTargetBinders : BinderContext target childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      (source.regions child).parent? = some region →
      simulation.Allowed childDirection child →
      (childBinderWitness :
        simulation.BinderWitness childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (simulation.regionMap child) →
      BinderContext.Enumeration source childSourceBinders child →
      BinderContext.Enumeration target childTargetBinders
        (simulation.regionMap child) →
      compileRegion? signature source fuelSource child sourceContext
          childSourceBinders = some sourceBody →
      compileRegion? signature target fuelTarget (simulation.regionMap child)
          targetContext childTargetBinders = some targetBody →
      RegionSimulation model named childDirection (simulation.indexRelation context)
        (sourceBody.renameRelations
          (simulation.relationMap childBinderWitness)) targetBody)
    (occurrences : List (LocalOccurrence source.regionCount source.nodeCount))
    (members : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences source region)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : compileOccurrencesWith? signature source
      (compileRegion? signature source fuelSource) sourceContext sourceBinders
      occurrences = some sourceItems)
    (targetCompiled : compileOccurrencesWith? signature target
      (compileRegion? signature target fuelTarget) targetContext targetBinders
      (occurrences.map (simulation.occurrenceMap region regular)) =
        some targetItems) :
    ItemSeqSimulation model named direction (simulation.indexRelation context)
      (sourceItems.renameRelations (simulation.relationMap binderWitness))
      targetItems := by
  induction occurrences generalizing sourceItems targetItems with
  | nil =>
      simp [compileOccurrencesWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      intro sourceEnv targetEnv relEnv environments
      cases direction <;>
        simp [ItemSeq.renameRelations, SimulationDirection.Entails]
  | cons occurrence rest induction =>
      simp only [compileOccurrencesWith?, List.map_cons]
        at sourceCompiled targetCompiled
      cases sourceHeadResult : compileOccurrenceWith? signature source
          (compileRegion? signature source fuelSource) sourceContext sourceBinders
          occurrence with
      | none => simp [sourceHeadResult] at sourceCompiled
      | some sourceHead =>
          cases sourceTailResult : compileOccurrencesWith? signature source
              (compileRegion? signature source fuelSource) sourceContext
              sourceBinders rest with
          | none => simp [sourceHeadResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              simp [sourceHeadResult, sourceTailResult] at sourceCompiled
              subst sourceItems
              cases targetHeadResult : compileOccurrenceWith? signature target
                  (compileRegion? signature target fuelTarget) targetContext
                  targetBinders
                  (simulation.occurrenceMap region regular occurrence) with
              | none => simp [targetHeadResult] at targetCompiled
              | some targetHead =>
                  cases targetTailResult : compileOccurrencesWith? signature target
                      (compileRegion? signature target fuelTarget) targetContext
                      targetBinders
                      (rest.map (simulation.occurrenceMap region regular)) with
                  | none =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                  | some targetTail =>
                      simp [targetHeadResult, targetTailResult] at targetCompiled
                      subst targetItems
                      have head := simulation.compileOccurrence_denote direction
                        fuelSource fuelTarget region sourceContext targetContext
                        context atRegion sourceNodup targetNodup sourceBinders
                        targetBinders
                        allowed regular binderWitness
                        sourceBindersCover targetBindersCover sourceEnumeration
                        targetEnumeration
                        recurse occurrence (members occurrence (by simp))
                        sourceHead targetHead sourceHeadResult targetHeadResult
                      have tail := induction
                        (fun current currentMember => members current (by
                          simp [currentMember])) sourceTail targetTail
                        sourceTailResult targetTailResult
                      intro sourceEnv targetEnv relEnv environments
                      exact direction.entails_and
                        (head sourceEnv targetEnv relEnv environments)
                        (tail sourceEnv targetEnv relEnv environments)

/-- The authoritative fuelled region theorem.  Regular frame regions recurse
through mapped occurrences; a distinguished region is discharged exactly once
by `focusedKernel`.  All context extension, binder transport, cut polarity,
bubble witnesses, and `finishRegion` existentials are owned here. -/
theorem compileRegion_denote
    (simulation : ConcreteSemanticSimulation signature source target model named) :
    ∀ {sourceRels targetRels : RelCtx} (direction : SimulationDirection)
      (fuelSource fuelTarget : Nat) (region : Fin source.regionCount)
      (sourceContext : WireContext source) (targetContext : WireContext target)
      (context : simulation.ContextWitness sourceContext targetContext)
      (atRegion : simulation.AtRegion context region)
      (sourceBinders : BinderContext source sourceRels)
      (targetBinders : BinderContext target targetRels),
      simulation.Allowed direction region →
      (binderWitness :
        simulation.BinderWitness sourceBinders targetBinders) →
      sourceBinders.Covers region →
      targetBinders.Covers (simulation.regionMap region) →
      BinderContext.Enumeration source sourceBinders region →
      BinderContext.Enumeration target targetBinders
        (simulation.regionMap region) →
      (sourceContext.extend region).Exact region →
      (targetContext.extend (simulation.regionMap region)).Exact
        (simulation.regionMap region) →
      ∀ (sourceBody : Region signature sourceContext.length sourceRels)
        (targetBody : Region signature targetContext.length targetRels),
      compileRegion? signature source fuelSource region sourceContext
          sourceBinders = some sourceBody →
      compileRegion? signature target fuelTarget (simulation.regionMap region)
          targetContext targetBinders = some targetBody →
      RegionSimulation model named direction (simulation.indexRelation context)
        (sourceBody.renameRelations (simulation.relationMap binderWitness))
        targetBody := by
  intro sourceRels targetRels direction fuelSource
  induction fuelSource generalizing sourceRels targetRels direction with
  | zero =>
      intro fuelTarget region sourceContext targetContext context atRegion
        sourceBinders targetBinders allowed binderWitness sourceBindersCover
        targetBindersCover sourceEnumeration targetEnumeration sourceExact
        targetExact sourceBody targetBody sourceCompiled targetCompiled
      simp [compileRegion?] at sourceCompiled
  | succ fuelSource induction =>
      intro fuelTarget
      cases fuelTarget with
      | zero =>
          intro region sourceContext targetContext context atRegion sourceBinders
            targetBinders allowed binderWitness sourceBindersCover
            targetBindersCover sourceEnumeration targetEnumeration sourceExact
            targetExact sourceBody targetBody sourceCompiled targetCompiled
          simp [compileRegion?] at targetCompiled
      | succ fuelTarget =>
          intro region sourceContext targetContext context atRegion sourceBinders
            targetBinders allowed binderWitness sourceBindersCover
            targetBindersCover sourceEnumeration targetEnumeration sourceExact
            targetExact sourceBody targetBody sourceCompiled targetCompiled
          simp only [compileRegion?] at sourceCompiled targetCompiled
          let sourceExtended := sourceContext.extend region
          let targetExtended :=
            targetContext.extend (simulation.regionMap region)
          by_cases focused : simulation.Distinguished region
          · cases sourceItemsResult : compileOccurrencesWith? signature source
                (compileRegion? signature source fuelSource) sourceExtended
                sourceBinders (localOccurrences source region) with
            | none =>
                simp [sourceExtended, sourceItemsResult] at sourceCompiled
            | some sourceItems =>
                simp [sourceExtended, sourceItemsResult] at sourceCompiled
                subst sourceBody
                cases targetItemsResult : compileOccurrencesWith? signature target
                    (compileRegion? signature target fuelTarget) targetExtended
                    targetBinders
                    (localOccurrences target (simulation.regionMap region)) with
                | none =>
                    simp [targetExtended, targetItemsResult] at targetCompiled
                | some targetItems =>
                    simp [targetExtended, targetItemsResult] at targetCompiled
                    subst targetBody
                    let focusedContext :=
                      simulation.extendFocusedContext sourceContext targetContext
                        context region atRegion focused sourceExact targetExact
                    have recurse : ∀
                        {childDirection : SimulationDirection}
                        {child : Fin source.regionCount}
                        {childSourceRels childTargetRels : RelCtx}
                        {childSourceBinders :
                          BinderContext source childSourceRels}
                        {childTargetBinders :
                          BinderContext target childTargetRels}
                        {sourceChild : Region signature sourceExtended.length
                          childSourceRels}
                        {targetChild : Region signature targetExtended.length
                          childTargetRels},
                        (source.regions child).parent? = some region →
                        (target.regions (simulation.regionMap child)).parent? =
                          some (simulation.regionMap region) →
                        simulation.Allowed childDirection child →
                        (childBinderWitness : simulation.BinderWitness
                          childSourceBinders childTargetBinders) →
                        childSourceBinders.Covers child →
                        childTargetBinders.Covers
                          (simulation.regionMap child) →
                        BinderContext.Enumeration source childSourceBinders
                          child →
                        BinderContext.Enumeration target childTargetBinders
                          (simulation.regionMap child) →
                        compileRegion? signature source fuelSource child
                            sourceExtended childSourceBinders =
                          some sourceChild →
                        compileRegion? signature target fuelTarget
                            (simulation.regionMap child) targetExtended
                            childTargetBinders = some targetChild →
                        RegionSimulation model named childDirection
                          (simulation.indexRelation focusedContext)
                          (sourceChild.renameRelations
                            (simulation.relationMap childBinderWitness))
                          targetChild := by
                      intro childDirection child childSourceRels childTargetRels
                        childSourceBinders
                        childTargetBinders sourceChild targetChild sourceParent
                        targetParent childAllowed childBinderWitness
                        childSourceBindersCover childTargetBindersCover
                        childSourceEnumeration childTargetEnumeration
                        sourceChildCompiled targetChildCompiled
                      exact induction childDirection fuelTarget child
                        sourceExtended targetExtended focusedContext
                        (simulation.at_focused_child sourceContext targetContext
                          context region focused sourceExact targetExact child
                          atRegion sourceParent targetParent)
                        childSourceBinders childTargetBinders childAllowed
                        childBinderWitness childSourceBindersCover
                        childTargetBindersCover childSourceEnumeration
                        childTargetEnumeration
                        (sourceExact.extend_child simulation.source_wellFormed
                          sourceParent)
                        (targetExact.extend_child simulation.target_wellFormed
                          targetParent)
                        sourceChild targetChild sourceChildCompiled
                        targetChildCompiled
                    exact simulation.focusedRegionKernel direction
                      fuelSource fuelTarget region sourceContext targetContext
                      context sourceBinders targetBinders atRegion focused allowed
                      binderWitness sourceExact targetExact sourceBindersCover
                      targetBindersCover sourceEnumeration targetEnumeration recurse
                      (by
                        intro childDirection child childSourceRels
                          childTargetRels childSourceBinders childTargetBinders
                          childFuelTarget childSourceContext childTargetContext
                          childContext
                          childAt childAllowed childBinderWitness
                          childSourceBindersCover childTargetBindersCover
                          childSourceEnumeration childTargetEnumeration
                          childSourceExact childTargetExact sourceChild
                          targetChild sourceChildCompiled targetChildCompiled
                        exact induction childDirection childFuelTarget child
                          childSourceContext childTargetContext childContext
                          childAt childSourceBinders childTargetBinders
                          childAllowed childBinderWitness
                          childSourceBindersCover childTargetBindersCover
                          childSourceEnumeration childTargetEnumeration
                          childSourceExact childTargetExact sourceChild targetChild
                          sourceChildCompiled targetChildCompiled)
                      sourceItems targetItems sourceItemsResult targetItemsResult
          · rw [simulation.localOccurrences_map region focused] at targetCompiled
            let extendedContext := simulation.extendContext sourceContext targetContext
              context region focused sourceExact targetExact
            let extendedRelation := simulation.indexRelation extendedContext
            cases sourceItemsResult : compileOccurrencesWith? signature source
                (compileRegion? signature source fuelSource) sourceExtended
                sourceBinders (localOccurrences source region) with
            | none =>
                simp [sourceExtended, sourceItemsResult] at sourceCompiled
            | some sourceItems =>
                simp [sourceExtended, sourceItemsResult] at sourceCompiled
                subst sourceBody
                cases targetItemsResult : compileOccurrencesWith? signature target
                    (compileRegion? signature target fuelTarget) targetExtended
                    targetBinders
                    ((localOccurrences source region).map
                      (simulation.occurrenceMap region focused)) with
                | none =>
                    simp [targetExtended, targetItemsResult] at targetCompiled
                | some targetItems =>
                    simp [targetExtended, targetItemsResult] at targetCompiled
                    subst targetBody
                    have targetItemsCompiled :
                        compileOccurrencesWith? signature target
                            (compileRegion? signature target fuelTarget)
                            targetExtended targetBinders
                            (localOccurrences target
                              (simulation.regionMap region)) = some targetItems := by
                      rw [simulation.localOccurrences_map region focused]
                      exact targetItemsResult
                    have recurse : ∀ {childDirection : SimulationDirection}
                        {child : Fin source.regionCount}
                        {childSourceRels childTargetRels : RelCtx}
                        {childSourceBinders :
                          BinderContext source childSourceRels}
                        {childTargetBinders :
                          BinderContext target childTargetRels}
                        {sourceChild : Region signature sourceExtended.length
                          childSourceRels}
                        {targetChild : Region signature targetExtended.length
                          childTargetRels},
                        (source.regions child).parent? = some region →
                        simulation.Allowed childDirection child →
                        (childBinderWitness : simulation.BinderWitness
                          childSourceBinders childTargetBinders) →
                        childSourceBinders.Covers child →
                        childTargetBinders.Covers
                          (simulation.regionMap child) →
                        BinderContext.Enumeration source childSourceBinders
                          child →
                        BinderContext.Enumeration target childTargetBinders
                          (simulation.regionMap child) →
                        compileRegion? signature source fuelSource child
                            sourceExtended childSourceBinders = some sourceChild →
                        compileRegion? signature target fuelTarget
                            (simulation.regionMap child) targetExtended
                            childTargetBinders = some targetChild →
                        RegionSimulation model named childDirection
                          (simulation.indexRelation extendedContext)
                          (sourceChild.renameRelations
                            (simulation.relationMap childBinderWitness))
                          targetChild := by
                      intro childDirection child childSourceRels childTargetRels
                        childSourceBinders
                        childTargetBinders sourceChild targetChild parent childAllowed
                        childBinderWitness childSourceBindersCover
                        childTargetBindersCover childSourceEnumeration
                        childTargetEnumeration sourceChildCompiled
                        targetChildCompiled
                      exact induction childDirection fuelTarget child sourceExtended
                        targetExtended extendedContext
                        (simulation.at_child sourceContext targetContext context
                          region focused sourceExact targetExact child atRegion parent)
                        childSourceBinders
                        childTargetBinders childAllowed childBinderWitness
                        childSourceBindersCover childTargetBindersCover
                        childSourceEnumeration childTargetEnumeration
                        (sourceExact.extend_child simulation.source_wellFormed parent)
                        (targetExact.extend_child simulation.target_wellFormed
                          (simulation.parent_mapped focused parent))
                        sourceChild targetChild sourceChildCompiled
                        targetChildCompiled
                    have itemSemantics := simulation.compileOccurrences_denote
                      direction fuelSource fuelTarget region sourceExtended
                      targetExtended extendedContext
                      (simulation.at_extended sourceContext targetContext context
                        region focused sourceExact targetExact atRegion)
                      sourceExact.nodup
                      targetExact.nodup sourceBinders targetBinders allowed focused
                      binderWitness sourceBindersCover targetBindersCover
                      sourceEnumeration targetEnumeration recurse
                      (localOccurrences source region) (fun _ member => member)
                      sourceItems targetItems sourceItemsResult targetItemsResult
                    rw [finishRegion_renameRelations sourceContext region
                      (simulation.relationMap binderWitness) sourceItems]
                    exact finishRegion_denote direction sourceContext targetContext
                      region (simulation.regionMap region)
                      (simulation.indexRelation context)
                      model named
                      (sourceItems.renameRelations
                        (simulation.relationMap binderWitness))
                      targetItems
                      (simulation.localTransport direction fuelSource fuelTarget
                        sourceContext targetContext context sourceBinders
                        targetBinders binderWitness region atRegion focused
                        allowed sourceExact targetExact sourceBindersCover
                        targetBindersCover sourceEnumeration targetEnumeration
                        sourceItems targetItems sourceItemsResult
                        targetItemsCompiled itemSemantics)

/-- Root ambient/local partitions and their proof-dependent semantic
transport. -/
structure RootContextSimulation
    {source target : ConcreteDiagram}
    {model : Lambda.LambdaModel}
    {named : NamedEnv model.Carrier signature}
    (simulation : ConcreteSemanticSimulation signature source target model named)
    (direction : SimulationDirection)
    (sourceAmbient sourceLocals : WireContext source)
    (targetAmbient targetLocals : WireContext target) where
  outer : ContextIndexRelation sourceAmbient.length targetAmbient.length
  context : simulation.ContextWitness (sourceAmbient ++ sourceLocals)
    (targetAmbient ++ targetLocals)
  atRoot : simulation.AtRegion context source.root
  atRootChild : ¬ simulation.Distinguished source.root → ∀ child,
    (source.regions child).parent? = some source.root →
      simulation.AtRegion context child
  atFocusedRootChild : simulation.Distinguished source.root → ∀ child,
    (source.regions child).parent? = some source.root →
      (target.regions (simulation.regionMap child)).parent? =
        some (simulation.regionMap source.root) →
      simulation.AtRegion context child
  transport : ¬ simulation.Distinguished source.root →
    simulation.Allowed direction source.root →
    ∀ (sourceItems : ItemSeq signature
      (sourceAmbient ++ sourceLocals).length [])
    (targetItems : ItemSeq signature
      (targetAmbient ++ targetLocals).length []),
    compileOccurrencesWith? signature source
        (compileRegion? signature source source.regionCount)
        (sourceAmbient ++ sourceLocals) BinderContext.empty
        (localOccurrences source source.root) = some sourceItems →
    compileOccurrencesWith? signature target
        (compileRegion? signature target target.regionCount)
        (targetAmbient ++ targetLocals) BinderContext.empty
        (localOccurrences target (simulation.regionMap source.root)) =
          some targetItems →
    ItemSeqSimulation model named direction
      (simulation.indexRelation context)
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems →
    DirectionalRootTransport direction sourceAmbient sourceLocals
      targetAmbient targetLocals outer model named
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems
  /-- A distinguished root owns its complete existential semantics directly;
  regular roots may derive their transport from shared item simulation. -/
  focusedRootKernel : simulation.AtRegion context source.root →
    simulation.Distinguished source.root →
    simulation.Allowed direction source.root →
    (∀ {childDirection : SimulationDirection}
      {child : Fin source.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : BinderContext source childSourceRels}
      {childTargetBinders : BinderContext target childTargetRels}
      {sourceBody : Region signature
        (sourceAmbient ++ sourceLocals).length childSourceRels}
      {targetBody : Region signature
        (targetAmbient ++ targetLocals).length childTargetRels},
      (source.regions child).parent? = some source.root →
      (target.regions (simulation.regionMap child)).parent? =
        some (simulation.regionMap source.root) →
      simulation.Allowed childDirection child →
      (childBinderWitness :
        simulation.BinderWitness childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (simulation.regionMap child) →
      BinderContext.Enumeration source childSourceBinders child →
      BinderContext.Enumeration target childTargetBinders
        (simulation.regionMap child) →
      compileRegion? signature source source.regionCount child
          (sourceAmbient ++ sourceLocals) childSourceBinders = some sourceBody →
      compileRegion? signature target target.regionCount
          (simulation.regionMap child) (targetAmbient ++ targetLocals)
          childTargetBinders = some targetBody →
      RegionSimulation model named childDirection
        (simulation.indexRelation context)
        (sourceBody.renameRelations
          (simulation.relationMap childBinderWitness))
        targetBody) →
    (∀ {childDirection : SimulationDirection}
      {child : Fin source.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : BinderContext source childSourceRels}
      {childTargetBinders : BinderContext target childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : WireContext source)
      (childTargetContext : WireContext target)
      (childContext :
        simulation.ContextWitness childSourceContext childTargetContext),
      simulation.AtRegion childContext child →
      simulation.Allowed childDirection child →
      (childBinderWitness :
        simulation.BinderWitness childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (simulation.regionMap child) →
      BinderContext.Enumeration source childSourceBinders child →
      BinderContext.Enumeration target childTargetBinders
        (simulation.regionMap child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend (simulation.regionMap child)).Exact
        (simulation.regionMap child) →
      ∀ (sourceBody : Region signature
          childSourceContext.length childSourceRels)
        (targetBody : Region signature
          childTargetContext.length childTargetRels),
      compileRegion? signature source source.regionCount child
          childSourceContext childSourceBinders = some sourceBody →
      compileRegion? signature target childFuelTarget
          (simulation.regionMap child) childTargetContext
          childTargetBinders = some targetBody →
      RegionSimulation model named childDirection
        (simulation.indexRelation childContext)
        (sourceBody.renameRelations
          (simulation.relationMap childBinderWitness))
        targetBody) →
    ∀ (sourceItems : ItemSeq signature
        (sourceAmbient ++ sourceLocals).length [])
      (targetItems : ItemSeq signature
        (targetAmbient ++ targetLocals).length []),
    compileOccurrencesWith? signature source
        (compileRegion? signature source source.regionCount)
        (sourceAmbient ++ sourceLocals) BinderContext.empty
        (localOccurrences source source.root) = some sourceItems →
    compileOccurrencesWith? signature target
        (compileRegion? signature target target.regionCount)
        (targetAmbient ++ targetLocals) BinderContext.empty
        (localOccurrences target (simulation.regionMap source.root)) =
          some targetItems →
    RegionSimulation model named direction outer
      ((finishRoot sourceAmbient sourceLocals sourceItems).renameRelations
        (simulation.relationMap simulation.binders_empty))
      (finishRoot targetAmbient targetLocals targetItems)

/-- Ordered boundary-assignment transport.  This keeps repeated positions
positional while requiring their exposed classes to carry equal related
values. -/
def DirectionalBoundaryWitness (direction : SimulationDirection)
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (relation : ContextIndexRelation source.externalClasses
      target.externalClasses)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (targetArgs : Fin targetArity → model.Carrier) :
    Prop :=
  match direction with
  | .forward => ∀ sourceAssignment : BoundaryAssignment source model.Carrier,
      sourceAssignment.args = sourceArgs →
      denoteRegion (relCtx := []) model named sourceAssignment.classes PUnit.unit
        source.body →
        ∃ targetAssignment : BoundaryAssignment target model.Carrier,
          targetAssignment.args = targetArgs ∧
            relation.EnvironmentsAgree sourceAssignment.classes
              targetAssignment.classes
  | .backward => ∀ targetAssignment : BoundaryAssignment target model.Carrier,
      targetAssignment.args = targetArgs →
      denoteRegion (relCtx := []) model named targetAssignment.classes PUnit.unit
        target.body →
        ∃ sourceAssignment : BoundaryAssignment source model.Carrier,
          sourceAssignment.args = sourceArgs ∧
            relation.EnvironmentsAgree sourceAssignment.classes
              targetAssignment.classes

/-- Lift body simulation through ordered open-boundary assignments. -/
theorem denoteOpen_lift
    (direction : SimulationDirection)
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (relation : ContextIndexRelation source.externalClasses
      target.externalClasses)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (targetArgs : Fin targetArity → model.Carrier)
    (boundary : DirectionalBoundaryWitness direction source target relation
      model named sourceArgs targetArgs)
    (body : RegionSimulation model named direction relation source.body target.body) :
    direction.Entails (denoteOpen model named source sourceArgs)
      (denoteOpen model named target targetArgs) := by
  unfold denoteOpen
  cases direction with
  | forward =>
      rintro ⟨sourceAssignment, sourceArgsEq, sourceDenotes⟩
      obtain ⟨targetAssignment, targetArgsEq, environments⟩ :=
        boundary sourceAssignment sourceArgsEq sourceDenotes
      exact ⟨targetAssignment, targetArgsEq,
        body sourceAssignment.classes targetAssignment.classes
          PUnit.unit environments sourceDenotes⟩
  | backward =>
      rintro ⟨targetAssignment, targetArgsEq, targetDenotes⟩
      obtain ⟨sourceAssignment, sourceArgsEq, environments⟩ :=
        boundary targetAssignment targetArgsEq targetDenotes
      exact ⟨sourceAssignment, sourceArgsEq,
        body sourceAssignment.classes targetAssignment.classes
          PUnit.unit environments targetDenotes⟩

/-- Lift a concrete simulation through `compileRoot?` and `finishRoot`. -/
theorem compileRoot_denote
    (simulation : ConcreteSemanticSimulation signature source target model named)
    (direction : SimulationDirection)
    (sourceAmbient sourceLocals : WireContext source)
    (targetAmbient targetLocals : WireContext target)
    (rootContext : RootContextSimulation simulation direction sourceAmbient
      sourceLocals targetAmbient targetLocals)
    (allowed : simulation.Allowed direction source.root)
    (sourceExact : (sourceAmbient ++ sourceLocals).Exact source.root)
    (targetExact : (targetAmbient ++ targetLocals).Exact target.root)
    (sourceBody : Region signature sourceAmbient.length [])
    (targetBody : Region signature targetAmbient.length [])
    (sourceCompiled : compileRoot? signature source sourceAmbient sourceLocals =
      some sourceBody)
    (targetCompiled : compileRoot? signature target targetAmbient targetLocals =
      some targetBody) :
    RegionSimulation model named direction rootContext.outer sourceBody targetBody := by
  let sourceRootContext := sourceAmbient ++ sourceLocals
  let targetRootContext := targetAmbient ++ targetLocals
  have targetRootExact : targetRootContext.Exact
      (simulation.regionMap source.root) := by
    simpa only [simulation.root_eq] using targetExact
  unfold compileRoot? at sourceCompiled targetCompiled
  rw [simulation.root_eq] at targetCompiled
  by_cases focused : simulation.Distinguished source.root
  · cases sourceItemsResult : compileOccurrencesWith? signature source
        (compileRegion? signature source source.regionCount) sourceRootContext
        BinderContext.empty (localOccurrences source source.root) with
    | none => simp [sourceRootContext, sourceItemsResult] at sourceCompiled
    | some sourceItems =>
        simp [sourceRootContext, sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult : compileOccurrencesWith? signature target
            (compileRegion? signature target target.regionCount) targetRootContext
            BinderContext.empty
            (localOccurrences target (simulation.regionMap source.root)) with
        | none => simp [targetRootContext, targetItemsResult] at targetCompiled
        | some targetItems =>
            simp [targetRootContext, targetItemsResult] at targetCompiled
            subst targetBody
            have recurse : ∀ {childDirection : SimulationDirection}
                {child : Fin source.regionCount}
                {childSourceRels childTargetRels : RelCtx}
                {childSourceBinders :
                  BinderContext source childSourceRels}
                {childTargetBinders :
                  BinderContext target childTargetRels}
                {sourceChild : Region signature sourceRootContext.length
                  childSourceRels}
                {targetChild : Region signature targetRootContext.length
                  childTargetRels},
                (source.regions child).parent? = some source.root →
                (target.regions (simulation.regionMap child)).parent? =
                  some (simulation.regionMap source.root) →
                simulation.Allowed childDirection child →
                (childBinderWitness : simulation.BinderWitness
                  childSourceBinders childTargetBinders) →
                childSourceBinders.Covers child →
                childTargetBinders.Covers (simulation.regionMap child) →
                BinderContext.Enumeration source childSourceBinders child →
                BinderContext.Enumeration target childTargetBinders
                  (simulation.regionMap child) →
                compileRegion? signature source source.regionCount child
                    sourceRootContext childSourceBinders = some sourceChild →
                compileRegion? signature target target.regionCount
                    (simulation.regionMap child) targetRootContext
                    childTargetBinders = some targetChild →
                RegionSimulation model named childDirection
                  (simulation.indexRelation rootContext.context)
                  (sourceChild.renameRelations
                    (simulation.relationMap childBinderWitness))
                  targetChild := by
              intro childDirection child childSourceRels childTargetRels
                childSourceBinders
                childTargetBinders sourceChild targetChild sourceParent
                targetParent childAllowed childBinderWitness
                childSourceBindersCover childTargetBindersCover
                childSourceEnumeration childTargetEnumeration
                sourceChildCompiled targetChildCompiled
              exact simulation.compileRegion_denote childDirection
                source.regionCount target.regionCount child sourceRootContext
                targetRootContext rootContext.context
                (rootContext.atFocusedRootChild focused child sourceParent
                  targetParent)
                childSourceBinders childTargetBinders childAllowed
                childBinderWitness childSourceBindersCover
                childTargetBindersCover childSourceEnumeration
                childTargetEnumeration
                (sourceExact.extend_child simulation.source_wellFormed
                  sourceParent)
                (targetRootExact.extend_child simulation.target_wellFormed
                  targetParent)
                sourceChild targetChild sourceChildCompiled targetChildCompiled
            simpa only [Region.renameRelations_empty] using
              rootContext.focusedRootKernel rootContext.atRoot focused allowed
                recurse
                (by
                  intro childDirection child childSourceRels childTargetRels
                    childSourceBinders childTargetBinders childFuelTarget
                    childSourceContext childTargetContext childContext childAt
                    childAllowed
                    childBinderWitness childSourceBindersCover
                    childTargetBindersCover childSourceEnumeration
                    childTargetEnumeration childSourceExact childTargetExact
                    sourceChild targetChild sourceChildCompiled
                    targetChildCompiled
                  exact simulation.compileRegion_denote childDirection
                    source.regionCount childFuelTarget child
                    childSourceContext childTargetContext childContext childAt
                    childSourceBinders childTargetBinders childAllowed
                    childBinderWitness childSourceBindersCover
                    childTargetBindersCover childSourceEnumeration
                    childTargetEnumeration childSourceExact childTargetExact
                    sourceChild targetChild sourceChildCompiled
                    targetChildCompiled)
                sourceItems targetItems sourceItemsResult targetItemsResult

  · rw [simulation.localOccurrences_map source.root focused]
        at targetCompiled
    cases sourceItemsResult : compileOccurrencesWith? signature source
        (compileRegion? signature source source.regionCount) sourceRootContext
        BinderContext.empty (localOccurrences source source.root) with
    | none => simp [sourceRootContext, sourceItemsResult] at sourceCompiled
    | some sourceItems =>
        simp [sourceRootContext, sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult : compileOccurrencesWith? signature target
            (compileRegion? signature target target.regionCount) targetRootContext
            BinderContext.empty
            ((localOccurrences source source.root).map
              (simulation.occurrenceMap source.root focused)) with
        | none => simp [targetRootContext, targetItemsResult] at targetCompiled
        | some targetItems =>
            simp [targetRootContext, targetItemsResult] at targetCompiled
            subst targetBody
            have recurse : ∀ {childDirection : SimulationDirection}
                {child : Fin source.regionCount}
                {childSourceRels childTargetRels : RelCtx}
                {childSourceBinders :
                  BinderContext source childSourceRels}
                {childTargetBinders :
                  BinderContext target childTargetRels}
                {sourceChild : Region signature sourceRootContext.length
                  childSourceRels}
                {targetChild : Region signature targetRootContext.length
                  childTargetRels},
                (source.regions child).parent? = some source.root →
                simulation.Allowed childDirection child →
                (childBinderWitness : simulation.BinderWitness
                  childSourceBinders childTargetBinders) →
                childSourceBinders.Covers child →
                childTargetBinders.Covers (simulation.regionMap child) →
                BinderContext.Enumeration source childSourceBinders child →
                BinderContext.Enumeration target childTargetBinders
                  (simulation.regionMap child) →
                compileRegion? signature source source.regionCount child
                    sourceRootContext childSourceBinders = some sourceChild →
                compileRegion? signature target target.regionCount
                    (simulation.regionMap child) targetRootContext
                    childTargetBinders = some targetChild →
                RegionSimulation model named childDirection
                  (simulation.indexRelation rootContext.context)
                  (sourceChild.renameRelations
                    (simulation.relationMap childBinderWitness))
                  targetChild := by
              intro childDirection child childSourceRels childTargetRels
                childSourceBinders
                childTargetBinders sourceChild targetChild parent childAllowed
                childBinderWitness childSourceBindersCover
                childTargetBindersCover childSourceEnumeration
                childTargetEnumeration sourceChildCompiled targetChildCompiled
              exact simulation.compileRegion_denote childDirection
                source.regionCount target.regionCount child sourceRootContext
                targetRootContext rootContext.context
                (rootContext.atRootChild focused child parent)
                childSourceBinders
                childTargetBinders childAllowed childBinderWitness
                childSourceBindersCover childTargetBindersCover
                childSourceEnumeration childTargetEnumeration
                (sourceExact.extend_child simulation.source_wellFormed parent)
                (targetRootExact.extend_child simulation.target_wellFormed
                  (simulation.parent_mapped focused parent))
                sourceChild targetChild sourceChildCompiled targetChildCompiled
            have itemSemantics := simulation.compileOccurrences_denote direction
              source.regionCount target.regionCount source.root sourceRootContext
              targetRootContext rootContext.context rootContext.atRoot
              sourceExact.nodup
              targetRootExact.nodup BinderContext.empty BinderContext.empty
              allowed focused simulation.binders_empty
              (BinderContext.empty_covers_root simulation.source_wellFormed)
              (by
                simpa only [← simulation.root_eq] using
                  BinderContext.empty_covers_root simulation.target_wellFormed)
              (BinderContext.Enumeration.empty source)
              (by
                simpa only [← simulation.root_eq] using
                  BinderContext.Enumeration.empty target)
              recurse
              (localOccurrences source source.root) (fun _ member => member)
              sourceItems targetItems sourceItemsResult targetItemsResult
            have targetItemsCompiled :
                compileOccurrencesWith? signature target
                    (compileRegion? signature target target.regionCount)
                    targetRootContext BinderContext.empty
                    (localOccurrences target
                      (simulation.regionMap source.root)) = some targetItems := by
              rw [simulation.localOccurrences_map source.root focused]
              exact targetItemsResult
            simpa only [ItemSeq.renameRelations_empty] using
              finishRoot_denote direction sourceAmbient sourceLocals
                targetAmbient targetLocals rootContext.outer
                model named
                (sourceItems.renameRelations
                  (simulation.relationMap simulation.binders_empty))
                targetItems
                (rootContext.transport focused allowed sourceItems targetItems
                  sourceItemsResult targetItemsCompiled itemSemantics)

/-- The canonical exposed/hidden root context is exact.  Kept public here
because root simulation clients must construct the same authoritative compiler
context rather than duplicate the elaborator's private proof. -/
theorem checkedOpen_rootContext_exact
    (checked : CheckedOpenDiagram signature) :
    WireContext.Exact checked.val.rootWires checked.val.diagram.root := by
  constructor
  · exact checked.val.rootWires_nodup
  · intro wire
    rw [OpenConcreteDiagram.mem_rootWires_iff checked.val checked.property]
    constructor
    · intro scope
      rw [scope]
      exact ConcreteDiagram.Encloses.refl _ _
    · exact encloses_sheet_eq
        checked.property.diagram_well_formed.root_is_sheet

/-- Boundary-parametric denotation lifting for checked open concrete diagrams.
The caller supplies only the concrete simulation instance, root context
relation, allowed root direction, and ordered boundary witness. -/
theorem elaborateOpen_denote
    (sourceOpen : CheckedOpenDiagram signature)
    (targetOpen : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (simulation : ConcreteSemanticSimulation signature
      sourceOpen.val.diagram targetOpen.val.diagram model named)
    (direction : SimulationDirection)
    (rootContext : RootContextSimulation simulation direction
      sourceOpen.val.exposedWires sourceOpen.val.hiddenWires
      targetOpen.val.exposedWires targetOpen.val.hiddenWires)
    (allowed : simulation.Allowed direction sourceOpen.val.diagram.root)
    (sourceArgs : Fin sourceOpen.val.boundary.length → model.Carrier)
    (targetArgs : Fin targetOpen.val.boundary.length → model.Carrier)
    (boundary : DirectionalBoundaryWitness direction sourceOpen.elaborate
      targetOpen.elaborate rootContext.outer model named sourceArgs targetArgs) :
    direction.Entails (sourceOpen.denote model named sourceArgs)
      (targetOpen.denote model named targetArgs) := by
  obtain ⟨sourceBody, sourceCompiled, sourceBodyEq⟩ :=
    CheckedOpenDiagram.elaborate_body_computation sourceOpen
  obtain ⟨targetBody, targetCompiled, targetBodyEq⟩ :=
    CheckedOpenDiagram.elaborate_body_computation targetOpen
  have sourceExact :
      WireContext.Exact
        (sourceOpen.val.exposedWires ++ sourceOpen.val.hiddenWires)
        sourceOpen.val.diagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      checkedOpen_rootContext_exact sourceOpen
  have targetExact :
      WireContext.Exact
        (targetOpen.val.exposedWires ++ targetOpen.val.hiddenWires)
        targetOpen.val.diagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      checkedOpen_rootContext_exact targetOpen
  have compiledBodies := simulation.compileRoot_denote direction
    sourceOpen.val.exposedWires sourceOpen.val.hiddenWires
    targetOpen.val.exposedWires targetOpen.val.hiddenWires rootContext allowed
    sourceExact targetExact sourceBody targetBody sourceCompiled targetCompiled
  have elaboratedBodies : RegionSimulation model named direction rootContext.outer
      sourceOpen.elaborate.body targetOpen.elaborate.body := by
    rw [sourceBodyEq, targetBodyEq]
    exact compiledBodies
  exact denoteOpen_lift direction sourceOpen.elaborate targetOpen.elaborate
    rootContext.outer model named sourceArgs targetArgs boundary elaboratedBodies

end ConcreteSemanticSimulation

end VisualProof.Diagram.ConcreteElaboration
