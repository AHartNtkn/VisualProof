import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- A final region is regular precisely when it has a pointwise-preserved
source-frame preimage.  Copied material and the promoted focus have none. -/
def FinalRegularPreimage
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount) : Prop :=
  ∃ originalRegion,
    FrameRegular payload originalRegion ∧
      copyTrace.finalRegionMap elimTrace finalWellFormed originalRegion =
        finalRegion

/-- Total reverse region map used by the final-to-original simulation.  A
regular final region chooses its unique frame origin; all opaque material is
sent to the original parent focus. -/
noncomputable def reverseRegionMap
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount) :
    Fin input.val.regionCount := by
  classical
  exact if preimage : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion then Classical.choose preimage else payload.parent

theorem reverseRegionMap_spec
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    FrameRegular payload
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion) ∧
      copyTrace.finalRegionMap elimTrace finalWellFormed
          (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion) =
        finalRegion := by
  simp only [reverseRegionMap, dif_pos regular]
  exact Classical.choose_spec regular

theorem finalRegionMap_injective_of_frameRegular
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
    {first second : Fin input.val.regionCount}
    (firstRegular : FrameRegular payload first)
    (secondRegular : FrameRegular payload second)
    (mapped : copyTrace.finalRegionMap elimTrace finalWellFormed first =
      copyTrace.finalRegionMap elimTrace finalWellFormed second) :
    first = second := by
  have firstNeBubble : first ≠ bubble := by
    intro equal
    subst first
    exact firstRegular.1 (ConcreteDiagram.Encloses.refl input.val bubble)
  have secondNeBubble : second ≠ bubble := by
    intro equal
    subst second
    exact secondRegular.1 (ConcreteDiagram.Encloses.refl input.val bubble)
  have firstOrigin := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed first firstNeBubble
  have secondOrigin := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed second secondNeBubble
  apply copyTrace.regionMap_injective
  rw [← firstOrigin, ← secondOrigin, mapped]

@[simp] theorem reverseRegionMap_finalRegionMap
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
    (originalRegion : Fin input.val.regionCount)
    (regular : FrameRegular payload originalRegion) :
    copyTrace.reverseRegionMap elimTrace finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed originalRegion) =
      originalRegion := by
  let finalRegion := copyTrace.finalRegionMap elimTrace finalWellFormed
    originalRegion
  have preimage : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion := ⟨originalRegion, regular, rfl⟩
  have chosen := copyTrace.reverseRegionMap_spec elimTrace finalWellFormed
    finalRegion preimage
  exact copyTrace.finalRegionMap_injective_of_frameRegular elimTrace
    finalWellFormed chosen.1 regular chosen.2

theorem finalRegionMap_reverseRegionMap
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    copyTrace.finalRegionMap elimTrace finalWellFormed
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion) =
      finalRegion :=
  (copyTrace.reverseRegionMap_spec elimTrace finalWellFormed finalRegion
    regular).2

/-- The total reverse map carries the executor's final root back to the
authoritative original root, including the case where the quantified parent
itself is the root focus. -/
theorem reverseRegionMap_root
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
    copyTrace.reverseRegionMap elimTrace finalWellFormed
        elimTrace.sourceDiagram.root = input.val.root := by
  have mappedRoot := copyTrace.finalRegionMap_root elimTrace finalWellFormed
  by_cases rootFocus : input.val.root = payload.parent
  · have sourceTarget : elimTrace.sourceDiagram.root =
        elimTrace.targetIndex finalWellFormed := by
      rw [← mappedRoot, rootFocus]
      exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
    have noPreimage : ¬ copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed elimTrace.sourceDiagram.root := by
      rintro ⟨candidate, candidateRegular, mapped⟩
      have candidateTarget : copyTrace.finalRegionMap elimTrace
          finalWellFormed candidate = elimTrace.targetIndex finalWellFormed :=
        mapped.trans sourceTarget
      rcases (copyTrace.finalRegionMap_eq_targetIndex_iff elimTrace
        finalWellFormed candidate).1 candidateTarget with
        candidateParent | candidateBubble
      · exact candidateRegular.2 candidateParent
      · subst candidate
        exact candidateRegular.1
          (ConcreteDiagram.Encloses.refl input.val bubble)
    simp [reverseRegionMap, noPreimage, rootFocus]
  · have rootRegular : FrameRegular payload input.val.root := by
      constructor
      · intro enclosed
        have bubbleRoot := ConcreteElaboration.encloses_sheet_eq
          input.property.root_is_sheet enclosed
        have bubbleShape := payload.bubble_eq
        have sameShape := congrArg input.val.regions bubbleRoot
        have impossible := bubbleShape.symm.trans
          (sameShape.trans input.property.root_is_sheet)
        cases impossible
      · exact rootFocus
    rw [← mappedRoot]
    exact copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
      input.val.root rootRegular

theorem reverseRegionMap_child_of_frameRegular_parent
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
    {parent child : Fin input.val.regionCount}
    (parentRegular : FrameRegular payload parent)
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (childParent : (input.val.regions child).parent? = some parent) :
    copyTrace.reverseRegionMap elimTrace finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed child) = child := by
  by_cases childFocus : child = payload.parent
  · subst child
    have noPreimage : ¬ copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed payload.parent) := by
      rintro ⟨candidate, candidateRegular, mapped⟩
      have focus := copyTrace.finalRegionMap_parent elimTrace finalWellFormed
      rcases (copyTrace.finalRegionMap_eq_targetIndex_iff elimTrace
        finalWellFormed candidate).1 (mapped.trans focus) with
        candidateParent | candidateBubble
      · exact candidateRegular.2 candidateParent
      · subst candidate
        exact candidateRegular.1
          (ConcreteDiagram.Encloses.refl input.val bubble)
    simp [reverseRegionMap, noPreimage]
  · have childRegular : FrameRegular payload child := by
      constructor
      · intro enclosed
        rcases ConcreteElaboration.encloses_direct_child childParent enclosed with
          bubbleEq | parentEnclosed
        · have childBubble : child = bubble := bubbleEq.symm
          have direct := childParent
          rw [childBubble, payload.bubble_eq] at direct
          have parentEq : payload.parent = parent :=
            Option.some.inj (by simpa [CRegion.parent?] using direct)
          exact parentRegular.2 parentEq.symm
        · exact parentRegular.1 parentEnclosed
      · exact childFocus
    exact copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
      child childRegular

/-- Any enclosing binder of a regular original region is recovered after
forward and reverse region transport.  The original parent focus is handled
by the opaque fallback; every other enclosing binder is itself regular. -/
theorem reverseRegionMap_finalRegionMap_of_enclosing_regular
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
    (regular : FrameRegular payload region)
    (binder : Fin input.val.regionCount)
    (encloses : input.val.Encloses binder region) :
    copyTrace.reverseRegionMap elimTrace finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed binder) = binder := by
  by_cases binderFocus : binder = payload.parent
  · subst binder
    have noPreimage : ¬ copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed payload.parent) := by
      rintro ⟨candidate, candidateRegular, mapped⟩
      have focus := copyTrace.finalRegionMap_parent elimTrace finalWellFormed
      rcases (copyTrace.finalRegionMap_eq_targetIndex_iff elimTrace
        finalWellFormed candidate).1 (mapped.trans focus) with
        candidateParent | candidateBubble
      · exact candidateRegular.2 candidateParent
      · subst candidate
        exact candidateRegular.1
          (ConcreteDiagram.Encloses.refl input.val bubble)
    simp [reverseRegionMap, noPreimage]
  · have binderRegular : FrameRegular payload binder := by
      constructor
      · intro bubbleEnclosesBinder
        exact regular.1 (ConcreteElaboration.checked_encloses_trans
          input.property bubbleEnclosesBinder encloses)
      · exact binderFocus
    exact copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
      binder binderRegular

theorem finalNodeMap_injective
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
    {first second : Fin input.val.nodeCount}
    (firstOutside : ¬ input.val.Encloses bubble
      (input.val.nodes first).region)
    (secondOutside : ¬ input.val.Encloses bubble
      (input.val.nodes second).region)
    (mapped : copyTrace.finalNodeMap elimTrace first firstOutside =
      copyTrace.finalNodeMap elimTrace second secondOutside) :
    first = second := by
  have origins := congrArg (instantiationAtomDomain result).origin mapped
  change (instantiationAtomDomain result).origin
        (copyTrace.droppedNodeMap first firstOutside) =
      (instantiationAtomDomain result).origin
        (copyTrace.droppedNodeMap second secondOutside) at origins
  rw [copyTrace.droppedNodeMap_origin first firstOutside,
    copyTrace.droppedNodeMap_origin second secondOutside] at origins
  exact copyTrace.nodeMap_injective origins

/-- A final node at a regular final region has a certified original frame
node preimage. -/
def FinalNodePreimage
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount) : Prop :=
  ∃ (originalNode : Fin input.val.nodeCount)
      (nodeRegion : (input.val.nodes originalNode).region =
        copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion),
    copyTrace.finalNodeMap elimTrace originalNode
        (node_outside_bubble_of_regular payload
          (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)
          (copyTrace.reverseRegionMap_spec elimTrace finalWellFormed finalRegion
            regular).1 originalNode nodeRegion) =
      finalNode

/-- Reverse occurrence map for a regular final region.  Node preimages are
chosen only when certified; arbitrary off-region nodes use a harmless child
fallback, while child occurrences always use the total reverse region map. -/
noncomputable def reverseOccurrenceMap
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    ConcreteElaboration.LocalOccurrence elimTrace.sourceDiagram.regionCount
        elimTrace.sourceDiagram.nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount
  | .child child =>
      .child (copyTrace.reverseRegionMap elimTrace finalWellFormed child)
  | .node node => by
      classical
      exact if preimage : copyTrace.FinalNodePreimage elimTrace finalWellFormed
          finalRegion regular node then
        .node (Classical.choose preimage)
      else
        .child (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)

theorem finalNode_preimage_of_regular
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion) :
    copyTrace.FinalNodePreimage elimTrace finalWellFormed finalRegion regular
      finalNode := by
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let originalRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed finalRegion regular).1
  have mappedRegion := copyTrace.finalRegionMap_reverseRegionMap elimTrace
    finalWellFormed finalRegion regular
  have finalOccurrences := copyTrace.final_localOccurrences_of_regular elimTrace
    finalWellFormed originalRegion originalRegular
  have finalMember : ConcreteElaboration.LocalOccurrence.node finalNode ∈
      ConcreteElaboration.localOccurrences elimTrace.sourceDiagram
        (copyTrace.finalRegionMap elimTrace finalWellFormed originalRegion) := by
    apply (ConcreteElaboration.mem_localOccurrences_node _ _ _).2
    exact nodeRegion.trans mappedRegion.symm
  rw [finalOccurrences] at finalMember
  obtain ⟨originalOccurrence, originalMember, mapped⟩ :=
    List.mem_map.mp finalMember
  cases originalOccurrence with
  | node originalNode =>
      have originalNodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val originalRegion
          originalNode).1 originalMember
      refine ⟨originalNode, originalNodeRegion, ?_⟩
      have mapped' : ConcreteElaboration.LocalOccurrence.node
          (regions := elimTrace.sourceDiagram.regionCount)
          (copyTrace.finalNodeMap elimTrace originalNode
            (node_outside_bubble_of_regular payload originalRegion
              originalRegular originalNode originalNodeRegion)) =
          ConcreteElaboration.LocalOccurrence.node
            (regions := elimTrace.sourceDiagram.regionCount) finalNode := by
        simpa [finalFrameOccurrenceMap, originalNodeRegion] using mapped
      exact ConcreteElaboration.LocalOccurrence.node.inj mapped'
  | child originalChild =>
      simp [finalFrameOccurrenceMap] at mapped

theorem reverseOccurrenceMap_node_of_regular
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion) :
    ∃ originalNode,
      copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
          regular (.node finalNode) = .node originalNode := by
  let preimage := copyTrace.finalNode_preimage_of_regular elimTrace
    finalWellFormed finalRegion regular finalNode nodeRegion
  refine ⟨Classical.choose preimage, ?_⟩
  simp [reverseOccurrenceMap, preimage]

/-- The original node selected by the certified reverse occurrence map. -/
noncomputable def reverseNodeMap
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion) : Fin input.val.nodeCount :=
  Classical.choose (copyTrace.finalNode_preimage_of_regular elimTrace
    finalWellFormed finalRegion regular finalNode nodeRegion)

@[simp] theorem reverseOccurrenceMap_node_eq
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion) :
    copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
        regular (.node finalNode) =
      .node (copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion
        regular finalNode nodeRegion) := by
  let preimage := copyTrace.finalNode_preimage_of_regular elimTrace
    finalWellFormed finalRegion regular finalNode nodeRegion
  simp [reverseOccurrenceMap, reverseNodeMap, preimage]

@[simp] theorem reverseOccurrenceMap_child
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (child : Fin elimTrace.sourceDiagram.regionCount) :
    copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion regular
        (.child child) =
      .child (copyTrace.reverseRegionMap elimTrace finalWellFormed child) :=
  rfl

theorem reverseOccurrenceMap_finalFrameOccurrenceMap_of_mem
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
    (originalRegion : Fin input.val.regionCount)
    (originalRegular : FrameRegular payload originalRegion)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val originalRegion) :
    let finalRegion := copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion
    let finalRegular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
        finalRegion := ⟨originalRegion, originalRegular, rfl⟩
    copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
        finalRegular
        (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
          originalRegion originalRegular occurrence) = occurrence := by
  classical
  dsimp only
  let finalRegion := copyTrace.finalRegionMap elimTrace finalWellFormed
    originalRegion
  let finalRegular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion := ⟨originalRegion, originalRegular, rfl⟩
  have reverseOriginal := copyTrace.reverseRegionMap_finalRegionMap elimTrace
    finalWellFormed originalRegion originalRegular
  cases occurrence with
  | node originalNode =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val originalRegion
          originalNode).1 member
      let outside := node_outside_bubble_of_regular payload originalRegion
        originalRegular originalNode nodeRegion
      let finalNode := copyTrace.finalNodeMap elimTrace originalNode outside
      have preimage : copyTrace.FinalNodePreimage elimTrace finalWellFormed
          finalRegion finalRegular finalNode := by
        refine ⟨originalNode, ?_, ?_⟩
        · exact nodeRegion.trans reverseOriginal.symm
        · rfl
      rw [show copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
          originalRegion originalRegular
          (ConcreteElaboration.LocalOccurrence.node originalNode) =
          ConcreteElaboration.LocalOccurrence.node finalNode by
        simp [finalFrameOccurrenceMap, nodeRegion, finalNode, outside]]
      change (if actualPreimage : copyTrace.FinalNodePreimage elimTrace
          finalWellFormed finalRegion finalRegular finalNode then
          ConcreteElaboration.LocalOccurrence.node
            (Classical.choose actualPreimage)
        else ConcreteElaboration.LocalOccurrence.child
          (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)) =
        ConcreteElaboration.LocalOccurrence.node originalNode
      rw [dif_pos preimage]
      have chosenSpec := Classical.choose_spec preimage
      have chosenRegion := chosenSpec.1
      have chosenMapped := chosenSpec.2
      have chosenOutside := node_outside_bubble_of_regular payload
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)
        (copyTrace.reverseRegionMap_spec elimTrace finalWellFormed finalRegion
          finalRegular).1 (Classical.choose preimage) chosenRegion
      have chosenEq : Classical.choose preimage = originalNode :=
        copyTrace.finalNodeMap_injective elimTrace chosenOutside outside
          chosenMapped
      exact congrArg ConcreteElaboration.LocalOccurrence.node chosenEq
  | child originalChild =>
      have childParent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val originalRegion
          originalChild).1 member
      change ConcreteElaboration.LocalOccurrence.child
          (copyTrace.reverseRegionMap elimTrace finalWellFormed
            (copyTrace.finalRegionMap elimTrace finalWellFormed originalChild)) =
        ConcreteElaboration.LocalOccurrence.child originalChild
      exact congrArg ConcreteElaboration.LocalOccurrence.child
        (reverseRegionMap_child_of_frameRegular_parent originalRegular copyTrace
          elimTrace finalWellFormed childParent)

/-- Reverse occurrence transport recovers the authoritative original ordered
traversal at every regular final region. -/
theorem reverse_localOccurrences
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    ConcreteElaboration.localOccurrences input.val
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion) =
      (ConcreteElaboration.localOccurrences elimTrace.sourceDiagram
        finalRegion).map
        (copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
          regular) := by
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let originalRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed finalRegion regular).1
  have mappedRegion := copyTrace.finalRegionMap_reverseRegionMap elimTrace
    finalWellFormed finalRegion regular
  have forward := copyTrace.final_localOccurrences_of_regular elimTrace
    finalWellFormed originalRegion originalRegular
  rw [mappedRegion] at forward
  rw [forward]
  let occurrences := ConcreteElaboration.localOccurrences input.val
    originalRegion
  have pointwise : ∀ occurrence ∈ occurrences,
      copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
          regular
          (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
            originalRegion originalRegular occurrence) = occurrence := by
    intro occurrence member
    have canonical := copyTrace.reverseOccurrenceMap_finalFrameOccurrenceMap_of_mem
      elimTrace finalWellFormed originalRegion originalRegular occurrence member
    simpa [originalRegion, originalRegular, mappedRegion] using canonical
  have mappedBack :
      (occurrences.map
          (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
            originalRegion originalRegular)).map
          (copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
            regular) = occurrences := by
    have mapPointwise : ∀ values : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        (∀ occurrence ∈ values,
          copyTrace.reverseOccurrenceMap elimTrace finalWellFormed finalRegion
              regular
              (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                originalRegion originalRegular occurrence) = occurrence) →
        (values.map
            (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
              originalRegion originalRegular)).map
            (copyTrace.reverseOccurrenceMap elimTrace finalWellFormed
              finalRegion regular) = values := by
      intro values allPointwise
      induction values with
      | nil => rfl
      | cons occurrence rest ih =>
          have headEq := allPointwise occurrence List.mem_cons_self
          have tailPointwise : ∀ value ∈ rest,
              copyTrace.reverseOccurrenceMap elimTrace finalWellFormed
                  finalRegion regular
                  (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                    originalRegion originalRegular value) = value := by
            intro value member
            exact allPointwise value
              (List.mem_cons_of_mem occurrence member)
          have tailEq := ih tailPointwise
          change copyTrace.reverseOccurrenceMap elimTrace finalWellFormed
                finalRegion regular
                (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                  originalRegion originalRegular occurrence) :: _ =
              occurrence :: _
          rw [headEq]
          congr 1
    exact mapPointwise occurrences pointwise
  exact mappedBack.symm

/-- Every final child of a regular frame region is the image of one original
direct child, and the total reverse map recovers that same child. -/
theorem finalChild_preimage_of_regular_parent
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
    (finalParent : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalParent)
    (finalChild : Fin elimTrace.sourceDiagram.regionCount)
    (childParent : (elimTrace.sourceDiagram.regions finalChild).parent? =
      some finalParent) :
    ∃ originalChild : Fin input.val.regionCount,
      (input.val.regions originalChild).parent? = some
          (copyTrace.reverseRegionMap elimTrace finalWellFormed finalParent) ∧
        copyTrace.finalRegionMap elimTrace finalWellFormed originalChild =
          finalChild ∧
        copyTrace.reverseRegionMap elimTrace finalWellFormed finalChild =
          originalChild := by
  let originalParent := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalParent
  let originalRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed finalParent regular).1
  have mappedParent := copyTrace.finalRegionMap_reverseRegionMap elimTrace
    finalWellFormed finalParent regular
  have finalMember : ConcreteElaboration.LocalOccurrence.child finalChild ∈
      ConcreteElaboration.localOccurrences elimTrace.sourceDiagram
        (copyTrace.finalRegionMap elimTrace finalWellFormed originalParent) := by
    apply (ConcreteElaboration.mem_localOccurrences_child _ _ _).2
    exact childParent.trans (congrArg some mappedParent.symm)
  have forward := copyTrace.final_localOccurrences_of_regular elimTrace
    finalWellFormed originalParent originalRegular
  rw [forward] at finalMember
  obtain ⟨originalOccurrence, originalMember, mapped⟩ :=
    List.mem_map.mp finalMember
  cases originalOccurrence with
  | node originalNode =>
      have originalRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val originalParent
          originalNode).1 originalMember
      simp [finalFrameOccurrenceMap, originalRegion] at mapped
  | child originalChild =>
      have originalChildParent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val originalParent
          originalChild).1 originalMember
      have mappedChild : copyTrace.finalRegionMap elimTrace finalWellFormed
          originalChild = finalChild := by
        change ConcreteElaboration.LocalOccurrence.child
            (copyTrace.finalRegionMap elimTrace finalWellFormed originalChild) =
          ConcreteElaboration.LocalOccurrence.child finalChild at mapped
        exact ConcreteElaboration.LocalOccurrence.child.inj mapped
      refine ⟨originalChild, originalChildParent, mappedChild, ?_⟩
      rw [← mappedChild]
      exact reverseRegionMap_child_of_frameRegular_parent
        originalRegular copyTrace elimTrace finalWellFormed originalChildParent

/-- On every regular final frame, reverse transport preserves each direct
child wrapper exactly.  Distinguished children remain opaque wrappers while
their interiors are intentionally outside this theorem. -/
theorem reverse_region_shape_of_regular
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
    (finalParent : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalParent)
    (finalChild : Fin elimTrace.sourceDiagram.regionCount)
    (childParent : (elimTrace.sourceDiagram.regions finalChild).parent? =
      some finalParent) :
    input.val.regions
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalChild) =
      match elimTrace.sourceDiagram.regions finalChild with
      | .sheet => .sheet
      | .cut owner =>
          .cut (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
      | .bubble owner arity =>
          .bubble
            (copyTrace.reverseRegionMap elimTrace finalWellFormed owner) arity := by
  obtain ⟨originalChild, originalChildParent, mappedChild, reverseChild⟩ :=
    copyTrace.finalChild_preimage_of_regular_parent elimTrace finalWellFormed
      finalParent regular finalChild childParent
  let originalParent := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalParent
  let originalRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed finalParent regular).1
  have forwardShape := copyTrace.final_region_shape_of_regular elimTrace
    finalWellFormed originalParent originalRegular originalChild
      originalChildParent
  rw [mappedChild] at forwardShape
  rw [reverseChild]
  cases originalShape : input.val.regions originalChild with
  | sheet =>
      rw [originalShape] at originalChildParent
      simp [CRegion.parent?] at originalChildParent
  | cut originalOwner =>
      have ownerEq : originalOwner = originalParent := by
        rw [originalShape] at originalChildParent
        exact Option.some.inj originalChildParent
      subst originalOwner
      rw [originalShape] at forwardShape
      rw [forwardShape]
      simp [copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
        originalParent originalRegular]
  | bubble originalOwner arity =>
      have ownerEq : originalOwner = originalParent := by
        rw [originalShape] at originalChildParent
        exact Option.some.inj originalChildParent
      subst originalOwner
      rw [originalShape] at forwardShape
      rw [forwardShape]
      simp [copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
        originalParent originalRegular]

/-- A node occurring in a regular final frame is exactly the forward image of
its selected original node.  Reversing the owner and atom binder therefore
recovers the authoritative original constructor. -/
theorem reverse_node_shape_of_regular
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
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion) :
    input.val.nodes
        (copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion regular
          finalNode nodeRegion) =
      match elimTrace.sourceDiagram.nodes finalNode with
      | .term owner freePorts term =>
          .term (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            freePorts term
      | .atom owner binder =>
          .atom (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            (copyTrace.reverseRegionMap elimTrace finalWellFormed binder)
      | .named owner definition arity =>
          .named (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            definition arity := by
  let preimage := copyTrace.finalNode_preimage_of_regular elimTrace
    finalWellFormed finalRegion regular finalNode nodeRegion
  let originalNode := Classical.choose preimage
  have originalSpec := Classical.choose_spec preimage
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let originalRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed finalRegion regular).1
  have forwardShape := copyTrace.final_node_shape_of_regular elimTrace
    finalWellFormed originalRegion originalRegular originalNode originalSpec.1
  dsimp only at forwardShape
  rw [originalSpec.2] at forwardShape
  change input.val.nodes originalNode = _
  cases originalShape : input.val.nodes originalNode with
  | term originalOwner freePorts term =>
      have ownerEq : originalOwner = originalRegion := by
        have shapeRegion := congrArg CNode.region originalShape
        exact shapeRegion.symm.trans originalSpec.1
      subst originalOwner
      rw [originalShape] at forwardShape
      simp only at forwardShape
      rw [forwardShape]
      simp [copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
        originalRegion originalRegular]
  | atom originalOwner originalBinder =>
      have ownerEq : originalOwner = originalRegion := by
        have shapeRegion := congrArg CNode.region originalShape
        exact shapeRegion.symm.trans originalSpec.1
      subst originalOwner
      have binderEncloses := input.property.atom_binders_enclose originalNode
      rw [originalShape] at binderEncloses
      have reverseBinder :=
        copyTrace.reverseRegionMap_finalRegionMap_of_enclosing_regular elimTrace
          finalWellFormed originalRegion originalRegular originalBinder
            binderEncloses
      rw [originalShape] at forwardShape
      simp only at forwardShape
      rw [forwardShape]
      simp [copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
        originalRegion originalRegular, reverseBinder]
  | named originalOwner definition arity =>
      have ownerEq : originalOwner = originalRegion := by
        have shapeRegion := congrArg CNode.region originalShape
        exact shapeRegion.symm.trans originalSpec.1
      subst originalOwner
      rw [originalShape] at forwardShape
      simp only at forwardShape
      rw [forwardShape]
      simp [copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
        originalRegion originalRegular]

end InstantiationTrace

end VisualProof.Rule
