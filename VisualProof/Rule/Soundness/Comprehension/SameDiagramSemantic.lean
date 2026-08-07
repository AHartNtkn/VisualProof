import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceBackwardAligned

namespace VisualProof.Rule.InstantiationSemantic

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- An exact correspondence between two lexical wire lists for the same
concrete diagram.  The compiler may enumerate the same visible wires in
different orders. -/
structure SameDiagramContext
    (diagram : Concrete.Diagram)
    (source target : Concrete.Elaboration.WireContext diagram) where
  index : FiniteEquiv (Fin source.length) (Fin target.length)
  get : ∀ sourceIndex,
    target.get (index sourceIndex) = source.get sourceIndex

namespace SameDiagramContext

def indexRelation
    (context : SameDiagramContext diagram source target) :
    Concrete.Elaboration.ContextIndexRelation source.length target.length :=
  Concrete.Elaboration.ContextIndexRelation.forwardMap context.index

def extend
    (context : SameDiagramContext diagram source target)
    (region : Fin diagram.regionCount) :
    SameDiagramContext diagram (source.extend region) (target.extend region) :=
  {
    index := Concrete.Elaboration.extendedContextEquiv
      (Concrete.Iso.refl diagram) source target context.index region
    get := by
      simpa [Concrete.Iso.refl, FiniteEquiv.refl] using
        (Concrete.Elaboration.WireContextsAgree.extend
          (iso := Concrete.Iso.refl diagram) context.get region)
  }

/-- Equivalent exact inherited contexts determine the canonical same-diagram
context correspondence used at a compiled region. -/
noncomputable def ofExact
    (region : Fin diagram.regionCount)
    (source target : Concrete.Elaboration.WireContext diagram)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region) :
    SameDiagramContext diagram source target := by
  let index := inheritedWireEquivIso (Concrete.Iso.refl diagram) region
    source target sourceExact targetExact
  exact {
    index := index
    get := by
      intro sourceIndex
      simpa [Concrete.Iso.refl, FiniteEquiv.refl] using
        (inheritedWireEquivIso_spec (Concrete.Iso.refl diagram) region source
          target sourceExact targetExact sourceIndex)
  }

theorem localSelection
    (context : SameDiagramContext diagram source target)
    (direction : Concrete.Elaboration.SimulationDirection)
    (region : Fin diagram.regionCount)
    (model : Model) :
    ∀ (sourceOuter : Fin source.length → model.Carrier)
      (targetOuter : Fin target.length → model.Carrier),
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              (context.extend region).indexRelation.EnvironmentsAgree
                (Concrete.Elaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (Concrete.Elaboration.extendedEnvironment target region
                  targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              (context.extend region).indexRelation.EnvironmentsAgree
                (Concrete.Elaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (Concrete.Elaboration.extendedEnvironment target region
                  targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgreement
  have outerEq : sourceOuter = targetOuter ∘ context.index :=
    (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
      context.index sourceOuter targetOuter).mp outerAgreement
  let localEquiv := Concrete.Elaboration.localWireEquiv
    (Concrete.Iso.refl diagram) region
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := sourceLocal ∘ localEquiv.invFun
      refine ⟨targetLocal, ?_⟩
      apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (context.extend region).index _ _).mpr
      funext index
      let split : Fin (source.length +
          (Concrete.Elaboration.exactScopeWires diagram region).length) :=
        Fin.cast (Concrete.Elaboration.WireContext.length_extend source region)
          index
      have recover : Fin.cast
          (Concrete.Elaboration.WireContext.length_extend source region).symm
          split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
      · simp [SameDiagramContext.extend, indexRelation,
          Concrete.Elaboration.extendedContextEquiv,
          Concrete.Elaboration.castFinEquiv,
          Concrete.Elaboration.localWireEquiv, Concrete.Iso.refl,
          FiniteEquiv.refl,
          Concrete.Elaboration.extendedEnvironment, outerEq,
          Function.comp_def]
        simp [extendWireEnv, outerEq, Function.comp_def]
      · simp [SameDiagramContext.extend, indexRelation,
          Concrete.Elaboration.extendedContextEquiv,
          Concrete.Elaboration.castFinEquiv,
          Concrete.Elaboration.localWireEquiv, Concrete.Iso.refl,
          FiniteEquiv.refl,
          Concrete.Elaboration.extendedEnvironment, targetLocal,
          Function.comp_def]
        simp only [extendWireEnv, Fin.addCases_right, Function.comp_apply]
        change sourceLocal localIndex =
          sourceLocal (localEquiv.invFun (localEquiv localIndex))
        exact (congrArg sourceLocal (localEquiv.left_inv localIndex)).symm
  | backward =>
      intro targetLocal
      let sourceLocal := targetLocal ∘ localEquiv
      refine ⟨sourceLocal, ?_⟩
      apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (context.extend region).index _ _).mpr
      funext index
      let split : Fin (source.length +
          (Concrete.Elaboration.exactScopeWires diagram region).length) :=
        Fin.cast (Concrete.Elaboration.WireContext.length_extend source region)
          index
      have recover : Fin.cast
          (Concrete.Elaboration.WireContext.length_extend source region).symm
          split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
      · simp [SameDiagramContext.extend, indexRelation,
          Concrete.Elaboration.extendedContextEquiv,
          Concrete.Elaboration.castFinEquiv,
          Concrete.Elaboration.localWireEquiv, Concrete.Iso.refl,
          FiniteEquiv.refl,
          Concrete.Elaboration.extendedEnvironment, outerEq,
          Function.comp_def]
        simp [extendWireEnv, outerEq, Function.comp_def]
      · simp [SameDiagramContext.extend, indexRelation,
          Concrete.Elaboration.extendedContextEquiv,
          Concrete.Elaboration.castFinEquiv,
          Concrete.Elaboration.localWireEquiv, Concrete.Iso.refl,
          FiniteEquiv.refl,
          Concrete.Elaboration.extendedEnvironment, sourceLocal,
          Function.comp_def]
        simp only [extendWireEnv, Fin.addCases_right, Function.comp_apply]
        change targetLocal (localEquiv localIndex) =
          targetLocal (localEquiv localIndex)
        rfl

end SameDiagramContext

/-- Relation variables in two compiler binder contexts are paired by their
common concrete binder owner. -/
structure SameDiagramBinderWitness
    (diagram : Concrete.Diagram)
    {sourceRels targetRels : RelCtx}
    (source : Concrete.Elaboration.BinderContext diagram sourceRels)
    (target : Concrete.Elaboration.BinderContext diagram targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  mapped : ∀ region arity (relation : RelVar sourceRels arity),
    source region = some ⟨arity, relation⟩ →
      target region = some ⟨arity, relationMap relation⟩

namespace SameDiagramBinderWitness

def empty (diagram : Concrete.Diagram) :
    SameDiagramBinderWitness diagram
      Concrete.Elaboration.BinderContext.empty
      Concrete.Elaboration.BinderContext.empty where
  relationMap := Concrete.Elaboration.identityRelationRenaming []
  mapped := by
    intro region arity relation
    exact Fin.elim0 relation.index

def push
    (witness : SameDiagramBinderWitness diagram source target)
    (child : Fin diagram.regionCount)
    (arity : Nat) :
    SameDiagramBinderWitness diagram (source.push child arity)
      (target.push child arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  mapped := by
    intro region binderArity relation sourceLookup
    by_cases equality : region = child
    · subst region
      simp only [Concrete.Elaboration.BinderContext.push_self]
        at sourceLookup ⊢
      cases Option.some.inj sourceLookup
      rfl
    · rw [Concrete.Elaboration.BinderContext.push_other _ arity equality]
        at sourceLookup ⊢
      cases sourceEq : source region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          simp [sourceEq] at sourceLookup
          rcases sourceLookup with ⟨arityEq, relationEq⟩
          subst binderArity
          have relationEq' := eq_of_heq relationEq
          subst relation
          rw [witness.mapped region actualArity actualRelation sourceEq]
          rfl

@[simp] theorem relationMap_push
    (witness : SameDiagramBinderWitness diagram
      (sourceRels := sourceRels) (targetRels := targetRels) source target)
    (child : Fin diagram.regionCount)
    (arity : Nat) :
    ((witness.push child arity).relationMap :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

private theorem relation_exists
    (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount)
    (source : Concrete.Elaboration.BinderContext diagram sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      diagram source region)
    (target : Concrete.Elaboration.BinderContext diagram targetRels)
    (targetCover : target.Covers region)
    {arity : Nat} (relation : RelVar sourceRels arity) :
    ∃ targetRelation : RelVar targetRels arity,
      target (sourceEnumeration.binder relation.index) =
        some ⟨arity, targetRelation⟩ := by
  obtain ⟨parent, bubbleShape⟩ := sourceEnumeration.bubble relation.index
  have bubbleShape' : diagram.regions
      (sourceEnumeration.binder relation.index) = .bubble parent arity := by
    rw [relation.hasArity] at bubbleShape
    exact bubbleShape
  exact targetCover (sourceEnumeration.binder relation.index) parent arity
    bubbleShape' (sourceEnumeration.encloses relation.index)

/-- Canonical owner-preserving relation-variable correspondence. -/
noncomputable def ofEnumeration
    (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount)
    (source : Concrete.Elaboration.BinderContext diagram sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      diagram source region)
    (target : Concrete.Elaboration.BinderContext diagram targetRels)
    (targetCover : target.Covers region) :
    SameDiagramBinderWitness diagram source target := by
  let relationMap : RelationRenaming sourceRels targetRels :=
    fun relation => Classical.choose
      (relation_exists diagram region source sourceEnumeration target
        targetCover relation)
  refine {
    relationMap := relationMap
    mapped := ?_
  }
  intro owner arity relation sourceLookup
  have ownerEq : sourceEnumeration.binder relation.index = owner :=
    sourceEnumeration.lookup_owner relation sourceLookup
  rw [← ownerEq]
  exact Classical.choose_spec
    (relation_exists diagram region source sourceEnumeration target
      targetCover relation)

end SameDiagramBinderWitness

/-- Semantic invariance of recompiling one well-formed diagram under exact
wire contexts and owner-aligned binder contexts. -/
noncomputable def sameDiagramSemanticSimulation
    (diagram : Concrete.Diagram)
    (wellFormed : diagram.WellFormed )
    (model : Model)
    :
    Concrete.Elaboration.ConcreteSemanticSimulation  diagram diagram
      model  where
  source_wellFormed := wellFormed
  target_wellFormed := wellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by simp
  occurrenceMap_child := by simp
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    cases shape : diagram.regions child <;> simp [shape]
  localOccurrences_map := by simp
  BinderWitness := fun source target =>
    SameDiagramBinderWitness diagram source target
  relationMap := fun witness => witness.relationMap
  binders_empty := SameDiagramBinderWitness.empty diagram
  binders_push := by
    intro sourceRels targetRels source target witness child parent arity
      childKind regular
    exact witness.push child arity
  relationMap_push := by
    intro sourceRels targetRels source target witness child parent arity
      childKind regular
    exact witness.relationMap_push child arity
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := SameDiagramContext diagram
  AtRegion := fun _ _ => True
  indexRelation := fun context => context.indexRelation
  extendContext := by
    intro source target context region regular sourceExact targetExact
    exact context.extend region
  extendFocusedContext := by
    intro source target context region atRegion focused sourceExact targetExact
    exact False.elim focused
  at_child := by simp
  at_extended := by simp
  at_focused_child := by
    intro source target context parent focused
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget source target
      context sourceBinders targetBinders binderWitness region atRegion regular
      allowed sourceExact targetExact sourceCover targetCover sourceEnumeration
      targetEnumeration sourceItems targetItems sourceCompiled targetCompiled
      itemSimulation
    exact Concrete.Elaboration.directionalLocalTransport_of_agreement direction
      source target region region context.indexRelation
      (context.extend region).indexRelation model
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
      (context.localSelection direction region model) itemSimulation
  nodeSemantic := by
    intro sourceRels targetRels direction region source target context atRegion
      sourceNodup targetNodup sourceBinders targetBinders allowed binderWitness
      sourceNode targetNode regular mapped nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
    have nodeEq : targetNode = sourceNode :=
      Concrete.Elaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
      model  direction source target context.indexRelation sourceBinders
      targetBinders binderWitness.relationMap sourceNode sourceNode id id
    · cases diagram.nodes sourceNode <;> rfl
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      obtain ⟨sourceOwner, sourceOccurs, sourceGet⟩ :=
        Concrete.Elaboration.resolvePort?_sound sourceResolved
      obtain ⟨targetOwner, targetOccurs, targetGet⟩ :=
        Concrete.Elaboration.resolvePort?_sound targetResolved
      have ownerEq : sourceOwner = targetOwner :=
        Concrete.Elaboration.endpoint_wire_unique
          wellFormed.wire_endpoints_are_disjoint sourceOccurs targetOccurs
      have mappedGet : target.get (context.index sourceIndex) = sourceOwner := by
        rw [context.get]
        simpa only [List.get_eq_getElem] using sourceGet
      have targetGet' : target.get targetIndex = targetOwner := by
        simpa only [List.get_eq_getElem] using targetGet
      have indexEq : context.index sourceIndex = targetIndex := by
        apply Fin.ext
        apply (List.getElem_inj targetNodup).mp
        have sameGet : target.get (context.index sourceIndex) =
            target.get targetIndex := mappedGet.trans
          (ownerEq.trans targetGet'.symm)
        simpa only [List.get_eq_getElem] using sameGet
      exact indexEq
    · intro owner binder arity relation sourceShape sourceLookup
      exact binderWitness.mapped binder arity relation sourceLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region source
      target context sourceBinders targetBinders atRegion focused
    exact False.elim focused

end VisualProof.Rule.InstantiationSemantic
