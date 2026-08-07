import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalReverse

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- Concrete lexical-context evidence for the final-to-original simulation.
Every original wire in the target context has its certified final image in the
source context.  The source may additionally contain executor-created focus
wires, which remain locally existential. -/
structure FinalContextWitness
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : Concrete.Elaboration.WireContext input.val) : Prop where
  mapped_mem : ∀ wire, wire ∈ targetContext →
    copyTrace.finalWireMap elimTrace wire ∈ sourceContext

namespace FinalContextWitness

def empty
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw) :
    FinalContextWitness copyTrace elimTrace [] [] where
  mapped_mem := by simp

noncomputable def sourceIndex
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) : Fin sourceContext.length :=
  Classical.choose (Concrete.Elaboration.WireContext.lookup?_complete
    (witness.mapped_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_lookup
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.lookup?
        (copyTrace.finalWireMap elimTrace (targetContext.get targetIndex)) =
      some (witness.sourceIndex targetIndex) :=
  Classical.choose_spec (Concrete.Elaboration.WireContext.lookup?_complete
    (witness.mapped_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_get
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.get (witness.sourceIndex targetIndex) =
      copyTrace.finalWireMap elimTrace (targetContext.get targetIndex) :=
  Concrete.Elaboration.WireContext.lookup?_sound
    (witness.sourceIndex_lookup targetIndex)

noncomputable def indexRelation
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext) :
    Concrete.Elaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  Concrete.Elaboration.ContextIndexRelation.backwardMap witness.sourceIndex

noncomputable def targetEnvironment
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceEnvironment : Fin sourceContext.length → D) :
    Fin targetContext.length → D :=
  sourceEnvironment ∘ witness.sourceIndex

theorem targetEnvironment_agrees
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceEnvironment : Fin sourceContext.length → D) :
    witness.indexRelation.EnvironmentsAgree sourceEnvironment
      (witness.targetEnvironment sourceEnvironment) := by
  apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
    _ _ _).2
  rfl

noncomputable def localSourceIndex
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (Concrete.Elaboration.exactScopeWires input.val
      originalRegion).length) :
    Fin (Concrete.Elaboration.exactScopeWires elimTrace.sourceDiagram
      finalRegion).length :=
  Classical.choose (Concrete.Elaboration.WireContext.lookup?_complete (by
    apply (Concrete.Elaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires
        ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
          targetIndex)).scope = originalRegion :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).1
        (List.get_mem _ targetIndex)
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed]
    exact (congrArg
      (copyTrace.finalRegionMap elimTrace finalWellFormed) targetScope).trans
        mappedRegion))

theorem localSourceIndex_lookup
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (Concrete.Elaboration.exactScopeWires input.val
      originalRegion).length) :
    Concrete.Elaboration.WireContext.lookup?
        (Concrete.Elaboration.exactScopeWires elimTrace.sourceDiagram
          finalRegion)
        (copyTrace.finalWireMap elimTrace
          ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
            targetIndex)) =
      some (localSourceIndex finalWellFormed finalRegion
        originalRegion mappedRegion targetIndex) :=
  Classical.choose_spec (Concrete.Elaboration.WireContext.lookup?_complete (by
    apply (Concrete.Elaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires
        ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
          targetIndex)).scope = originalRegion :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).1
        (List.get_mem _ targetIndex)
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
      targetScope, mappedRegion]))

theorem localSourceIndex_get
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (Concrete.Elaboration.exactScopeWires input.val
      originalRegion).length) :
    (Concrete.Elaboration.exactScopeWires elimTrace.sourceDiagram
        finalRegion).get
        (localSourceIndex finalWellFormed finalRegion
          originalRegion mappedRegion targetIndex) =
      copyTrace.finalWireMap elimTrace
        ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
          targetIndex) :=
  Concrete.Elaboration.WireContext.lookup?_sound
    (localSourceIndex_lookup finalWellFormed finalRegion
      originalRegion mappedRegion targetIndex)

theorem localSourceIndex_injective
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion) :
    Function.Injective (localSourceIndex finalWellFormed
      finalRegion originalRegion mappedRegion) := by
  intro first second indicesEq
  have mappedWiresEq : copyTrace.finalWireMap elimTrace
        ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
          first) =
      copyTrace.finalWireMap elimTrace
        ((Concrete.Elaboration.exactScopeWires input.val originalRegion).get
          second) := by
    rw [← localSourceIndex_get finalWellFormed finalRegion
      originalRegion mappedRegion first,
      ← localSourceIndex_get finalWellFormed finalRegion
        originalRegion mappedRegion second, indicesEq]
  have wiresEq := copyTrace.finalWireMap_injective elimTrace
    mappedWiresEq
  let targetWires := Concrete.Elaboration.exactScopeWires input.val
    originalRegion
  obtain ⟨canonical, canonicalLookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete
      (List.get_mem targetWires first)
  have firstEq : first = canonical :=
    Concrete.Elaboration.WireContext.lookup?_unique
      (Concrete.Elaboration.exactScopeWires_nodup input.val originalRegion)
      canonicalLookup rfl
  have secondEq : second = canonical :=
    Concrete.Elaboration.WireContext.lookup?_unique
      (Concrete.Elaboration.exactScopeWires_nodup input.val originalRegion)
      canonicalLookup wiresEq.symm
  exact firstEq.trans secondEq.symm

def extendMapped
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    {sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : Concrete.Elaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend finalRegion)
      (targetContext.extend originalRegion) := by
  refine ⟨?_⟩
  intro wire member
  rcases List.mem_append.mp member with outerMember | localMember
  · exact List.mem_append_left _ (witness.mapped_mem wire outerMember)
  · apply List.mem_append_right sourceContext
    apply (Concrete.Elaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires wire).scope = originalRegion :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).1 localMember
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed]
    exact (congrArg
      (copyTrace.finalRegionMap elimTrace finalWellFormed) targetScope).trans
        mappedRegion

def extendRegular
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    {sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : Concrete.Elaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend finalRegion)
      (targetContext.extend
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)) :=
  witness.extendMapped finalWellFormed finalRegion
    (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)
    (copyTrace.finalRegionMap_reverseRegionMap elimTrace finalWellFormed
      finalRegion regular)

def extendFocused
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    {sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : Concrete.Elaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
      (targetContext.extend payload.parent) :=
  witness.extendMapped finalWellFormed
    (elimTrace.targetIndex finalWellFormed) payload.parent
    (copyTrace.finalRegionMap_parent elimTrace finalWellFormed)

/-- At the promoted focus, both the original parent-local wires and the
selected bubble-local wires have their certified final images in the single
source focus context. -/
def extendSelected
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : Concrete.Diagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    {sourceContext : Concrete.Elaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : Concrete.Elaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
      ((targetContext.extend payload.parent).extend bubble) := by
  refine ⟨?_⟩
  intro wire member
  rcases List.mem_append.mp member with beforeBubble | bubbleLocal
  · rcases List.mem_append.mp beforeBubble with base | parentLocal
    · exact List.mem_append_left _ (witness.mapped_mem wire base)
    · apply List.mem_append_right sourceContext
      apply (Concrete.Elaboration.mem_exactScopeWires _ _ _).2
      have scope : (input.val.wires wire).scope = payload.parent :=
        (Concrete.Elaboration.mem_exactScopeWires _ _ _).1 parentLocal
      rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
        scope]
      exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
  · apply List.mem_append_right sourceContext
    apply (Concrete.Elaboration.mem_exactScopeWires _ _ _).2
    have scope : (input.val.wires wire).scope = bubble :=
      (Concrete.Elaboration.mem_exactScopeWires _ _ _).1 bubbleLocal
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
      scope]
    exact copyTrace.finalRegionMap_bubble elimTrace finalWellFormed

end FinalContextWitness

end InstantiationTrace

end VisualProof.Rule
