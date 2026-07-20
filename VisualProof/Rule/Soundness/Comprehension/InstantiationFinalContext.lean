import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalReverse

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- Concrete lexical-context evidence for the final-to-original simulation.
Every original wire in the target context has its certified final image in the
source context.  The source may additionally contain executor-created focus
wires, which remain locally existential. -/
structure FinalContextWitness
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
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val) : Prop where
  mapped_mem : ∀ wire, wire ∈ targetContext →
    copyTrace.finalWireMap elimTrace wire ∈ sourceContext

namespace FinalContextWitness

def empty
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
    FinalContextWitness copyTrace elimTrace [] [] where
  mapped_mem := by simp

noncomputable def sourceIndex
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) : Fin sourceContext.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (witness.mapped_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_lookup
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.lookup?
        (copyTrace.finalWireMap elimTrace (targetContext.get targetIndex)) =
      some (witness.sourceIndex targetIndex) :=
  Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
    (witness.mapped_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_get
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.get (witness.sourceIndex targetIndex) =
      copyTrace.finalWireMap elimTrace (targetContext.get targetIndex) :=
  ConcreteElaboration.WireContext.lookup?_sound
    (witness.sourceIndex_lookup targetIndex)

noncomputable def indexRelation
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  ConcreteElaboration.ContextIndexRelation.backwardMap witness.sourceIndex

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
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    _ _ _).2
  rfl

noncomputable def localSourceIndex
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length) :
    Fin (ConcreteElaboration.exactScopeWires elimTrace.sourceDiagram
      finalRegion).length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete (by
    apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires
        ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
          targetIndex)).scope = originalRegion :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1
        (List.get_mem _ targetIndex)
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed]
    exact (congrArg
      (copyTrace.finalRegionMap elimTrace finalWellFormed) targetScope).trans
        mappedRegion))

theorem localSourceIndex_lookup
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length) :
    ConcreteElaboration.WireContext.lookup?
        (ConcreteElaboration.exactScopeWires elimTrace.sourceDiagram
          finalRegion)
        (copyTrace.finalWireMap elimTrace
          ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
            targetIndex)) =
      some (localSourceIndex finalWellFormed boundaryNodup finalRegion
        originalRegion mappedRegion targetIndex) :=
  Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete (by
    apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires
        ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
          targetIndex)).scope = originalRegion :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1
        (List.get_mem _ targetIndex)
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
      targetScope, mappedRegion]))

theorem localSourceIndex_get
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length) :
    (ConcreteElaboration.exactScopeWires elimTrace.sourceDiagram
        finalRegion).get
        (localSourceIndex finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion targetIndex) =
      copyTrace.finalWireMap elimTrace
        ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
          targetIndex) :=
  ConcreteElaboration.WireContext.lookup?_sound
    (localSourceIndex_lookup finalWellFormed boundaryNodup finalRegion
      originalRegion mappedRegion targetIndex)

theorem localSourceIndex_injective
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion) :
    Function.Injective (localSourceIndex finalWellFormed boundaryNodup
      finalRegion originalRegion mappedRegion) := by
  intro first second indicesEq
  have mappedWiresEq : copyTrace.finalWireMap elimTrace
        ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
          first) =
      copyTrace.finalWireMap elimTrace
        ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
          second) := by
    rw [← localSourceIndex_get finalWellFormed boundaryNodup finalRegion
      originalRegion mappedRegion first,
      ← localSourceIndex_get finalWellFormed boundaryNodup finalRegion
        originalRegion mappedRegion second, indicesEq]
  have wiresEq := copyTrace.finalWireMap_injective elimTrace
    mappedWiresEq
  let targetWires := ConcreteElaboration.exactScopeWires input.val
    originalRegion
  obtain ⟨canonical, canonicalLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete
      (List.get_mem targetWires first)
  have firstEq : first = canonical :=
    ConcreteElaboration.WireContext.lookup?_unique
      (ConcreteElaboration.exactScopeWires_nodup input.val originalRegion)
      canonicalLookup rfl
  have secondEq : second = canonical :=
    ConcreteElaboration.WireContext.lookup?_unique
      (ConcreteElaboration.exactScopeWires_nodup input.val originalRegion)
      canonicalLookup wiresEq.symm
  exact firstEq.trans secondEq.symm

def extendMapped
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    {sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input.val}
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
    apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
    have targetScope : (input.val.wires wire).scope = originalRegion :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 localMember
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed]
    exact (congrArg
      (copyTrace.finalRegionMap elimTrace finalWellFormed) targetScope).trans
        mappedRegion

def extendRegular
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    {sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend finalRegion)
      (targetContext.extend
        (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)) :=
  witness.extendMapped finalWellFormed boundaryNodup finalRegion
    (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)
    (copyTrace.finalRegionMap_reverseRegionMap elimTrace finalWellFormed
      finalRegion regular)

def extendFocused
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    {sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input.val}
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext) :
    FinalContextWitness copyTrace elimTrace
      (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
      (targetContext.extend payload.parent) :=
  witness.extendMapped finalWellFormed boundaryNodup
    (elimTrace.targetIndex finalWellFormed) payload.parent
    (copyTrace.finalRegionMap_parent elimTrace finalWellFormed)

/-- At the promoted focus, both the original parent-local wires and the
selected bubble-local wires have their certified final images in the single
source focus context. -/
def extendSelected
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
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    {sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input.val}
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
      apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
      have scope : (input.val.wires wire).scope = payload.parent :=
        (ConcreteElaboration.mem_exactScopeWires _ _ _).1 parentLocal
      rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
        scope]
      exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
  · apply List.mem_append_right sourceContext
    apply (ConcreteElaboration.mem_exactScopeWires _ _ _).2
    have scope : (input.val.wires wire).scope = bubble :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 bubbleLocal
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed,
      scope]
    exact copyTrace.finalRegionMap_bubble elimTrace finalWellFormed

end FinalContextWitness

end InstantiationTrace

end VisualProof.Rule
