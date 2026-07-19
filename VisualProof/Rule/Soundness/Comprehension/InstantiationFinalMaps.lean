import VisualProof.Rule.Soundness.Comprehension.InstantiationDropWellFormed
import VisualProof.Rule.Soundness.Modal.VacuousElimination

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace VacuousElimTrace

/-- Total region map implemented by vacuous bubble elimination.  The deleted
bubble and its surviving parent both map to the promoted parent focus; every
other region maps to its exact survivor index. -/
def liftRegion
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin input.regionCount) :
    Fin trace.sourceDiagram.regionCount :=
  if equal : region = bubble then
    trace.targetIndex wellFormed
  else
    (vacuousRegionDomain input bubble).index region
      ((vacuousRegionDomain_survives input bubble region).2 equal)

@[simp] theorem liftRegion_bubble
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.liftRegion wellFormed bubble = trace.targetIndex wellFormed := by
  simp [liftRegion]

theorem liftRegion_of_ne
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin input.regionCount)
    (notBubble : region ≠ bubble) :
    trace.liftRegion wellFormed region =
      (vacuousRegionDomain input bubble).index region
        ((vacuousRegionDomain_survives input bubble region).2 notBubble) := by
  simp [liftRegion, notBubble]

theorem origin_liftRegion_of_ne
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin input.regionCount)
    (notBubble : region ≠ bubble) :
    trace.origin (trace.liftRegion wellFormed region) = region := by
  rw [trace.liftRegion_of_ne wellFormed region notBubble]
  exact SurvivorDomain.origin_index _ _ _

@[simp] theorem origin_liftRegion_bubble
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.origin (trace.liftRegion wellFormed bubble) = trace.parent := by
  rw [trace.liftRegion_bubble]
  exact trace.targetIndex_origin wellFormed

theorem liftRegion_eq_targetIndex_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin input.regionCount) :
    trace.liftRegion wellFormed region = trace.targetIndex wellFormed ↔
      region = trace.parent ∨ region = bubble := by
  by_cases bubbleEq : region = bubble
  · subst region
    simp
  · constructor
    · intro mapped
      left
      have origins := congrArg trace.origin mapped
      rw [trace.origin_liftRegion_of_ne wellFormed region bubbleEq] at origins
      exact origins.trans (trace.targetIndex_origin wellFormed)
    · rintro (parentEq | impossible)
      · apply trace.origin_injective
        rw [trace.origin_liftRegion_of_ne wellFormed region bubbleEq]
        exact parentEq.trans (trace.targetIndex_origin wellFormed).symm
      · exact False.elim (bubbleEq impossible)

theorem liftRegion_ne_targetIndex
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin input.regionCount)
    (notParent : region ≠ trace.parent)
    (notBubble : region ≠ bubble) :
    trace.liftRegion wellFormed region ≠ trace.targetIndex wellFormed := by
  intro equal
  exact (trace.liftRegion_eq_targetIndex_iff wellFormed region).1 equal
    |>.elim notParent notBubble

theorem liftRegion_root
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.liftRegion wellFormed input.root = trace.sourceDiagram.root := by
  have rootNe : input.root ≠ bubble := by
    intro equal
    have rootShape : input.regions input.root = .sheet :=
      wellFormed.root_is_sheet
    rw [equal, trace.bubble_eq] at rootShape
    cases rootShape
  apply trace.origin_injective
  rw [trace.origin_liftRegion_of_ne wellFormed input.root rootNe]
  exact trace.promotion.root_origin.symm

/-- Vacuous promotion carries a wire scope through `liftRegion`; wire and
endpoint identities themselves are unchanged. -/
theorem liftWire_scope
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount) :
    (trace.sourceDiagram.wires wire).scope =
      trace.liftRegion wellFormed (input.wires wire).scope := by
  have result := trace.promotion.wire_result wire
  change promoteWire? (vacuousRegionDomain input bubble) bubble trace.parent
      (input.wires wire) = some (trace.promotion.wires wire) at result
  unfold promoteWire? at result
  by_cases hlocal : (input.wires wire).scope = bubble
  · simp only [hlocal, if_pos] at result
    have parentIndex := (vacuousRegionDomain input bubble).index?_index
      trace.parent (trace.domain_parent wellFormed)
    rw [parentIndex] at result
    have wireEq := Option.some.inj result
    have scopeEq := congrArg CWire.scope wireEq
    simpa [sourceDiagram, liftRegion, hlocal] using scopeEq.symm
  · simp only [if_neg hlocal] at result
    have scopeIndex := (vacuousRegionDomain input bubble).index?_index
      (input.wires wire).scope
      ((vacuousRegionDomain_survives input bubble _).2 hlocal)
    rw [scopeIndex] at result
    have wireEq := Option.some.inj result
    have scopeEq := congrArg CWire.scope wireEq
    simpa [sourceDiagram, liftRegion, hlocal] using scopeEq.symm

end VacuousElimTrace

namespace InstantiationTrace

/-- Composite region map from the original quantified diagram through every
accepted splice, processed-atom deletion, and final vacuous promotion. -/
def finalRegionMap
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
    (region : Fin input.val.regionCount) :
    Fin elimTrace.sourceDiagram.regionCount :=
  elimTrace.liftRegion finalWellFormed (copyTrace.regionMap region)

/-- Composite old-wire map into the final promoted executor diagram. -/
def finalWireMap
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
    (wire : Fin input.val.wireCount) :
    Fin elimTrace.sourceDiagram.wireCount :=
  copyTrace.wireMap wire

@[simp] theorem finalRegionMap_bubble
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
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    copyTrace.finalRegionMap elimTrace finalWellFormed bubble =
      elimTrace.targetIndex finalWellFormed := by
  unfold finalRegionMap
  have mapped := copyTrace.regionMap_bubble
  change copyTrace.regionMap bubble = result.bubble at mapped
  rw [mapped]
  exact elimTrace.liftRegion_bubble finalWellFormed

theorem finalRegionMap_root
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
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    copyTrace.finalRegionMap elimTrace finalWellFormed input.val.root =
      elimTrace.sourceDiagram.root := by
  unfold finalRegionMap
  have mapped := copyTrace.regionMap_root
  change copyTrace.regionMap input.val.root = result.diagram.val.root at mapped
  rw [mapped]
  exact elimTrace.liftRegion_root finalWellFormed

/-- The copy trace preserves the quantified bubble's parent, and the final
vacuous receipt identifies that copied parent as its promoted parent. -/
theorem regionMap_parent_eq_elimParent
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
      result.bubble raw) :
    copyTrace.regionMap payload.parent = elimTrace.parent := by
  have copiedShape := copyTrace.regionMap_shape bubble
  simp only [initialInstantiationState] at copiedShape
  rw [payload.bubble_eq] at copiedShape
  simp only at copiedShape
  have bubbleMap := copyTrace.regionMap_bubble
  change copyTrace.regionMap bubble = result.bubble at bubbleMap
  have eliminatedShape : result.diagram.val.regions result.bubble =
      .bubble elimTrace.parent elimTrace.arity := by
    simpa only [InstantiationDrop.raw_regions] using elimTrace.bubble_eq
  have copiedParent :
      (result.diagram.val.regions (copyTrace.regionMap bubble)).parent? =
        some (copyTrace.regionMap payload.parent) := by
    exact congrArg CRegion.parent? copiedShape
  have eliminatedParent :
      (result.diagram.val.regions result.bubble).parent? =
        some elimTrace.parent := by
    exact congrArg CRegion.parent? eliminatedShape
  have sameParent := congrArg
    (fun region => (result.diagram.val.regions region).parent?) bubbleMap
  apply Option.some.inj
  exact copiedParent.symm.trans (sameParent.trans eliminatedParent)

/-- The quantified bubble is an immediate child of the payload parent. -/
theorem payload_parent_encloses_bubble
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    input.val.Encloses payload.parent bubble := by
  have positive : 0 < input.val.regionCount := Nat.zero_lt_of_lt bubble.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  have parentEq : (input.val.regions bubble).parent? =
      some payload.parent := by
    rw [payload.bubble_eq]
    rfl
  simp only [ConcreteDiagram.climb, parentEq]

/-- The quantified bubble cannot enclose its own immediate parent in a checked
diagram.  This is the exact outside-frame fact needed to transport the
parent's ordered local traversal through the copy trace. -/
theorem payload_bubble_not_encloses_parent
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    ¬ input.val.Encloses bubble payload.parent := by
  apply ConcreteElaboration.checked_direct_child_not_encloses_parent
    input.property
  rw [payload.bubble_eq]
  rfl

/-- The original parent of the quantified bubble maps to the final promoted
focus.  This identifies the unique compiler location at which the complete
instantiation law is discharged. -/
theorem finalRegionMap_parent
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
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    copyTrace.finalRegionMap elimTrace finalWellFormed payload.parent =
      elimTrace.targetIndex finalWellFormed := by
  unfold finalRegionMap
  rw [copyTrace.regionMap_parent_eq_elimParent elimTrace]
  exact (elimTrace.liftRegion_eq_targetIndex_iff finalWellFormed
    elimTrace.parent).2 (Or.inl rfl)

/-- The final promotion coalesces exactly the original quantified bubble and
its parent at the target focus.  Injectivity of the copy trace rules out every
other preimage. -/
theorem finalRegionMap_eq_targetIndex_iff
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
    (region : Fin input.val.regionCount) :
    copyTrace.finalRegionMap elimTrace finalWellFormed region =
        elimTrace.targetIndex finalWellFormed ↔
      region = payload.parent ∨ region = bubble := by
  unfold finalRegionMap
  rw [elimTrace.liftRegion_eq_targetIndex_iff]
  have bubbleMap := copyTrace.regionMap_bubble
  change copyTrace.regionMap bubble = result.bubble at bubbleMap
  have parentMap := copyTrace.regionMap_parent_eq_elimParent elimTrace
  constructor
  · rintro (mappedParent | mappedBubble)
    · exact Or.inl (copyTrace.regionMap_injective
        (mappedParent.trans parentMap.symm))
    · exact Or.inr (copyTrace.regionMap_injective
        (mappedBubble.trans bubbleMap.symm))
  · rintro (rfl | rfl)
    · exact Or.inl parentMap
    · exact Or.inr bubbleMap

theorem finalRegionMap_ne_targetIndex_of_not_enclosed
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
    (region : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent region) :
    copyTrace.finalRegionMap elimTrace finalWellFormed region ≠
      elimTrace.targetIndex finalWellFormed := by
  intro mapped
  rcases (copyTrace.finalRegionMap_eq_targetIndex_iff elimTrace
    finalWellFormed region).1 mapped with parentEq | bubbleEq
  · subst region
    exact regular (ConcreteDiagram.Encloses.refl input.val payload.parent)
  · subst region
    exact regular (payload_parent_encloses_bubble payload)

theorem finalWireMap_injective
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
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    Function.Injective (copyTrace.finalWireMap elimTrace) := by
  exact copyTrace.wireMap_injective boundaryNodup

theorem finalWireMap_scope
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (wire : Fin input.val.wireCount) :
    (elimTrace.sourceDiagram.wires
        (copyTrace.finalWireMap elimTrace wire)).scope =
      copyTrace.finalRegionMap elimTrace finalWellFormed
        (input.val.wires wire).scope := by
  unfold finalWireMap finalRegionMap
  rw [elimTrace.liftWire_scope finalWellFormed]
  rw [InstantiationDrop.raw_wire_scope]
  rw [copyTrace.wireMap_scope boundaryNodup]
  rfl

end InstantiationTrace

end VisualProof.Rule
