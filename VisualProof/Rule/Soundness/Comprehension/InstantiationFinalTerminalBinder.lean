import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalBinder
import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceBackwardExternal
import VisualProof.Rule.Soundness.Modal.VacuousEliminationAncestor

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The inherited context of the promoted focus is exactly the inherited
context of the terminal parent before the eliminated bubble is reinserted. -/
theorem terminalParent_exact
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (sourceExact : (sourceContext.extend
      (trace.targetIndex targetWellFormed)).Exact
        (trace.targetIndex targetWellFormed)) :
    @ConcreteElaboration.WireContext.Exact input
      (@ConcreteElaboration.WireContext.extend input sourceContext trace.parent)
      trace.parent := by
  have sourceNodup :
      (sourceContext ++ ConcreteElaboration.exactScopeWires
        trace.sourceDiagram (trace.targetIndex targetWellFormed)).Nodup := by
    simpa [ConcreteElaboration.WireContext.extend] using sourceExact.nodup
  have sourceParts := List.nodup_append.mp sourceNodup
  constructor
  · rw [ConcreteElaboration.WireContext.extend, List.nodup_append]
    refine ⟨sourceParts.1,
      ConcreteElaboration.exactScopeWires_nodup input trace.parent, ?_⟩
    intro left leftMember right rightMember equality
    subst right
    have focusMember := trace.parentWire_mem_focusExact targetWellFormed left
      rightMember
    exact sourceParts.2.2 left leftMember left focusMember rfl
  · intro wire
    constructor
    · intro member
      rcases List.mem_append.mp member with outerMember | localMember
      · have sourceVisible := (sourceExact.mem_iff wire).1
            (List.mem_append_left _ outerMember)
        let sourceScope := (trace.sourceDiagram.wires wire).scope
        have sourceScopeNe : sourceScope ≠ trace.targetIndex targetWellFormed := by
          intro equality
          have focusMember : wire ∈ ConcreteElaboration.exactScopeWires
              trace.sourceDiagram (trace.targetIndex targetWellFormed) :=
            (ConcreteElaboration.mem_exactScopeWires _ _ _).2 equality
          exact sourceParts.2.2 wire outerMember wire focusMember rfl
        have originalScope : (input.wires wire).scope =
            trace.origin sourceScope :=
          (trace.promotedWire_scope_eq_regular_iff targetWellFormed wire
            sourceScope sourceScopeNe).1 rfl
        have mapped := trace.sourceEnclosesFocus_iff_forward targetWellFormed
          sourceWellFormed sourceScope sourceVisible
        simpa [originalScope] using mapped
      · have scope : (input.wires wire).scope = trace.parent :=
          (ConcreteElaboration.mem_exactScopeWires _ _ _).1 localMember
        rw [scope]
        exact ConcreteDiagram.Encloses.refl input trace.parent
    · intro visible
      by_cases isLocal : (input.wires wire).scope = trace.parent
      · exact List.mem_append_right sourceContext
          ((ConcreteElaboration.mem_exactScopeWires _ _ _).2 isLocal)
      · obtain ⟨sourceAncestor, originEq, sourceVisible⟩ :=
          trace.sourceEnclosesFocus_iff_backward targetWellFormed
            sourceWellFormed (input.wires wire).scope visible
        have sourceAncestorNe :
            sourceAncestor ≠ trace.targetIndex targetWellFormed := by
          intro equality
          subst sourceAncestor
          have focusOrigin : trace.origin (trace.targetIndex targetWellFormed) =
              trace.parent := trace.targetIndex_origin targetWellFormed
          exact isLocal (originEq.symm.trans focusOrigin)
        have sourceScope : (trace.sourceDiagram.wires wire).scope =
            sourceAncestor :=
          (trace.promotedWire_scope_eq_regular_iff targetWellFormed wire
            sourceAncestor sourceAncestorNe).2 originEq.symm
        have sourceMember : wire ∈ sourceContext.extend
            (trace.targetIndex targetWellFormed) :=
          (sourceExact.mem_iff wire).2 (by simpa [sourceScope] using sourceVisible)
        rcases List.mem_append.mp sourceMember with outerMember | focusMember
        · exact List.mem_append_left _ outerMember
        · have focusScope : (trace.sourceDiagram.wires wire).scope =
              trace.targetIndex targetWellFormed :=
            (ConcreteElaboration.mem_exactScopeWires _ _ _).1 focusMember
          exact False.elim (sourceAncestorNe (sourceScope.symm.trans focusScope))

/-- A binder context covering an executor state also covers the atom-dropped
compiler view, whose regions and enclosure relation are unchanged. -/
theorem binderCover_to_drop
    {signature : List Nat}
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (cover : @ConcreteElaboration.BinderContext.Covers state.diagram.val rels
      context region) :
    @ConcreteElaboration.BinderContext.Covers (dropInstantiationAtomsRaw state)
      rels context region := by
  intro binder parent arity bubbleEq encloses
  apply cover binder parent arity
  · simpa only [InstantiationDrop.raw_regions] using bubbleEq
  · exact (InstantiationDrop.raw_encloses_iff state binder region).1 encloses

/-- Exact binder enumeration is preserved when executor-owned atoms are
deleted from the compiler view. -/
def binderEnumeration_to_drop
    {signature : List Nat}
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      state.diagram.val context region) :
    ConcreteElaboration.BinderContext.Enumeration
      (dropInstantiationAtomsRaw state) context region where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := by
    intro index
    obtain ⟨parent, bubbleEq⟩ := enumeration.bubble index
    exact ⟨parent, by simpa only [InstantiationDrop.raw_regions] using bubbleEq⟩
  encloses := by
    intro index
    exact (InstantiationDrop.raw_encloses_iff state _ _).2
      (enumeration.encloses index)
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

/-- Pull an original lexical binder context forward along the injective frame
region map.  Executor-created regions carry no unrelated binder. -/
noncomputable def traceBinderContext
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (external : ConcreteElaboration.BinderContext state.diagram.val rels) :
    ConcreteElaboration.BinderContext result.diagram.val rels :=
  fun region =>
    if image : ∃ source, trace.regionMap source = region then
      external (Classical.choose image)
    else none

@[simp] theorem traceBinderContext_regionMap
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (external : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount) :
    traceBinderContext trace external (trace.regionMap region) =
      external region := by
  unfold traceBinderContext
  have image : ∃ source, trace.regionMap source = trace.regionMap region :=
    ⟨region, rfl⟩
  rw [dif_pos image]
  have chosen : Classical.choose image = region :=
    trace.regionMap_injective (Classical.choose_spec image)
  rw [chosen]

/-- Pulling a context that covers the original quantified parent forward
covers the copied terminal parent.  The proof uses the selected bubble as the
ancestry anchor, excluding the deleted child itself. -/
theorem traceBinderContext_covers_parent
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (external : ConcreteElaboration.BinderContext input.val rels)
    (externalCover : external.Covers payload.parent) :
    (traceBinderContext trace external).Covers
      (trace.regionMap payload.parent) := by
  intro targetBinder targetParent arity targetShape targetEnclosesParent
  have mappedBubbleShape := trace.regionMap_shape bubble
  simp only [initialInstantiationState] at mappedBubbleShape
  rw [payload.bubble_eq] at mappedBubbleShape
  have bubbleMap := trace.regionMap_bubble
  change trace.regionMap bubble = result.bubble at bubbleMap
  have terminalBubbleShape : result.diagram.val.regions result.bubble =
      .bubble (trace.regionMap payload.parent) payload.arity := by
    rw [← bubbleMap]
    exact mappedBubbleShape
  have parentEnclosesBubble : result.diagram.val.Encloses
      (trace.regionMap payload.parent) result.bubble := by
    refine ⟨⟨1, by have := result.bubble.isLt; omega⟩, ?_⟩
    simp [ConcreteDiagram.climb, terminalBubbleShape, CRegion.parent?]
  have targetEnclosesBubble := ConcreteElaboration.checked_encloses_trans
    result.diagram.property targetEnclosesParent parentEnclosesBubble
  obtain ⟨sourceBinder, sourceEnclosesBubble, sourceMap⟩ :=
    trace.ancestor_preimage targetBinder targetEnclosesBubble
  subst targetBinder
  have mappedShape := trace.regionMap_shape sourceBinder
  simp only [initialInstantiationState] at sourceEnclosesBubble mappedShape
  have shapeEq := targetShape.symm.trans mappedShape
  cases sourceShape : input.val.regions sourceBinder with
  | sheet =>
      rw [sourceShape] at shapeEq
      contradiction
  | cut sourceParent =>
      rw [sourceShape] at shapeEq
      contradiction
  | bubble sourceParent sourceArity =>
      rw [sourceShape] at shapeEq
      have arityEq : sourceArity = arity :=
        (CRegion.bubble.inj shapeEq).2.symm
      subst sourceArity
      have sourceParentEq : (input.val.regions bubble).parent? =
          some payload.parent := by
        simp [payload.bubble_eq, CRegion.parent?]
      rcases ConcreteElaboration.encloses_direct_child sourceParentEq
          sourceEnclosesBubble with sourceIsBubble | sourceEnclosesParent
      · subst sourceBinder
        rw [bubbleMap] at targetEnclosesParent
        have terminalParentEq :
            (result.diagram.val.regions result.bubble).parent? =
              some (trace.regionMap payload.parent) := by
          simp [terminalBubbleShape, CRegion.parent?]
        exact False.elim
          (ConcreteElaboration.checked_direct_child_not_encloses_parent
            result.diagram.property terminalParentEq targetEnclosesParent)
      · obtain ⟨relation, externalLookup⟩ := externalCover sourceBinder
          sourceParent arity sourceShape sourceEnclosesParent
        refine ⟨relation, ?_⟩
        simpa using externalLookup

/-- Exact binder enumeration transported through the composite frame map. -/
noncomputable def traceBinderEnumeration
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (external : ConcreteElaboration.BinderContext state.diagram.val rels)
    (region : Fin state.diagram.val.regionCount)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      state.diagram.val external region) :
    ConcreteElaboration.BinderContext.Enumeration result.diagram.val
      (traceBinderContext trace external) (trace.regionMap region) where
  binder := fun index => trace.regionMap (enumeration.binder index)
  binder_injective := fun _ _ equality => enumeration.binder_injective
    (trace.regionMap_injective equality)
  bubble := by
    intro index
    obtain ⟨parent, shape⟩ := enumeration.bubble index
    exact ⟨trace.regionMap parent, by
      simpa [shape] using trace.regionMap_shape (enumeration.binder index)⟩
  encloses := by
    intro index
    exact trace.regionMap_encloses (enumeration.encloses index)
  lookup := by
    intro index
    simpa using enumeration.lookup index
  lookup_owner := by
    intro candidate arity relation lookup
    unfold traceBinderContext at lookup
    split at lookup
    next image =>
      have owner := enumeration.lookup_owner relation lookup
      rw [owner]
      exact Classical.choose_spec image
    next notImage => simp at lookup

/-- The canonical external relation map for a copied binder context, extended
by the moving bubble itself, preserves every intrinsic relation variable. -/
theorem traceExternalRelationMap_traceBinderContext_push
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    {rels : RelCtx}
    (external : ConcreteElaboration.BinderContext input.val rels)
    (arity : Nat)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      result.diagram.val
      ((traceBinderContext trace external).push result.bubble arity)
      result.bubble)
    (targetCover : (external.push bubble arity).Covers bubble)
    (fallback : Fin input.val.regionCount) :
    (traceExternalRelationMap trace
        ((traceBinderContext trace external).push result.bubble arity)
        sourceEnumeration (external.push bubble arity) targetCover fallback :
      RelationRenaming (arity :: rels) (arity :: rels)) =
      (ConcreteElaboration.identityRelationRenaming (arity :: rels) :
        RelationRenaming (arity :: rels) (arity :: rels)) := by
  apply @funext
  intro binderArity
  funext relation
  let owner := sourceEnumeration.binder relation.index
  have sourceLookup :
      (traceBinderContext trace external).push result.bubble arity owner =
        some ⟨binderArity, relation⟩ := by
    rcases relation with ⟨index, arityEq⟩
    subst binderArity
    simpa [owner] using sourceEnumeration.lookup index
  have targetLookup :
      (external.push bubble arity)
          (traceRegionPreimage trace fallback owner) =
        some ⟨binderArity, relation⟩ := by
    by_cases ownerEq : owner = result.bubble
    · rw [ownerEq] at sourceLookup ⊢
      have bubbleMap : trace.regionMap bubble = result.bubble := by
        simpa [initialInstantiationState] using trace.regionMap_bubble
      have preimageBubble :
          traceRegionPreimage trace fallback result.bubble = bubble := by
        rw [← bubbleMap, traceRegionPreimage_image]
      rw [preimageBubble]
      simpa only [ConcreteElaboration.BinderContext.push_self] using sourceLookup
    · rw [ConcreteElaboration.BinderContext.push_other _ arity ownerEq]
        at sourceLookup
      unfold traceBinderContext at sourceLookup
      split at sourceLookup
      next image =>
        let source := Classical.choose image
        have sourceMap : trace.regionMap source = owner :=
          Classical.choose_spec image
        have preimageEq : traceRegionPreimage trace fallback owner = source := by
          rw [← sourceMap, traceRegionPreimage_image]
        have sourceNe : source ≠ bubble := by
          intro equality
          rw [equality] at sourceMap
          have bubbleMap : trace.regionMap bubble = result.bubble := by
            simpa [initialInstantiationState] using trace.regionMap_bubble
          exact ownerEq (sourceMap.symm.trans bubbleMap)
        rw [preimageEq]
        rw [ConcreteElaboration.BinderContext.push_other external arity sourceNe]
        simpa only [source] using sourceLookup
      next noImage => simp at sourceLookup
  have mappedLookup := traceExternalRelationMap_spec trace
    ((traceBinderContext trace external).push result.bubble arity)
    sourceEnumeration (external.push bubble arity) targetCover fallback relation
    sourceLookup
  have pairEq := Option.some.inj (targetLookup.symm.trans mappedLookup)
  exact (eq_of_heq (Sigma.ext_iff.mp pairEq).2).symm

end InstantiationSemantic

namespace InstantiationTrace

/-- At every admissible final compiler binder, the vacuous origin is the
copy-trace image of the authoritative reverse region. -/
theorem origin_eq_regionMap_reverse_of_admissible
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (region : Fin elimTrace.sourceDiagram.regionCount)
    (admissible : copyTrace.FinalAdmissible elimTrace finalWellFormed region) :
    elimTrace.origin region = copyTrace.regionMap
      (copyTrace.reverseRegionMap elimTrace finalWellFormed region) := by
  rcases admissible with regular | focus
  · have spec := copyTrace.reverseRegionMap_spec elimTrace finalWellFormed
      region regular
    have notBubble : copyTrace.reverseRegionMap elimTrace finalWellFormed
        region ≠ bubble := by
      intro equality
      apply spec.1.1
      rw [equality]
      exact ConcreteDiagram.Encloses.refl input.val bubble
    calc
      elimTrace.origin region = elimTrace.origin
          (copyTrace.finalRegionMap elimTrace finalWellFormed
            (copyTrace.reverseRegionMap elimTrace finalWellFormed region)) :=
        congrArg elimTrace.origin spec.2.symm
      _ = copyTrace.regionMap
          (copyTrace.reverseRegionMap elimTrace finalWellFormed region) :=
        copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
          finalWellFormed _ notBubble
  · subst region
    calc
      elimTrace.origin (elimTrace.targetIndex finalWellFormed) =
          elimTrace.parent := elimTrace.targetIndex_origin finalWellFormed
      _ = copyTrace.regionMap payload.parent :=
        (copyTrace.regionMap_parent_eq_elimParent elimTrace).symm
      _ = copyTrace.regionMap
          (copyTrace.reverseRegionMap elimTrace finalWellFormed
            (elimTrace.targetIndex finalWellFormed)) := by
        rw [copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed]

/-- The final-to-original binder witness factors through the terminal copied
frame context before the eliminated bubble is reconstructed. -/
noncomputable def terminalMappedBinderWitness
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    {finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input.val targetRels}
    (witness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders) :
    VacuousElimTrace.MappedBinderWitness elimTrace sourceBinders
      (InstantiationSemantic.traceBinderContext copyTrace targetBinders) where
  relationMap := witness.relationMap
  bindersMapped := by
    intro region arity relation lookup
    rw [copyTrace.origin_eq_regionMap_reverse_of_admissible elimTrace
      finalWellFormed region (witness.admissible region arity relation lookup)]
    simpa using witness.bindersMapped region arity relation lookup

/-- The unchanged wire list is the canonical pre-focus context on the
terminal side of vacuous reconstruction. -/
def terminalPromotedContext
    (elimTrace : VacuousElimTrace input bubble raw)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram) :
    VacuousElimTrace.PromotedContextWitness elimTrace sourceContext
      sourceContext where
  target_subset_source := fun _ member => member
  source_subset_target_or_bubble := fun _ member => Or.inl member

end InstantiationTrace

end VisualProof.Rule
