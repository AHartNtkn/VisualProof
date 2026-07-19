import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalBinder
import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceBackwardExternal

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

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
