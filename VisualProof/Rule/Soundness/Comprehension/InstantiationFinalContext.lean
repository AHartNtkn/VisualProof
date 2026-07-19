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
    rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed boundaryNodup]
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

end FinalContextWitness

end InstantiationTrace

end VisualProof.Rule
