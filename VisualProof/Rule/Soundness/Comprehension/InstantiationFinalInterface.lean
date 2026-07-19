import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalRootSimulation
import VisualProof.Rule.Soundness.Modal.VacuousEliminationRootSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- The executor's accumulated logical interface carries every ordered
root boundary through exactly the same composite host-wire map as the
instantiation trace.  Repeated boundary positions remain repeated. -/
theorem interface_transportBoundary_eq_map
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (boundary : List (Fin origin.val.wireCount))
    (current : List (Fin state.diagram.val.wireCount))
    (stateTransport : state.interface.transportBoundary boundary = some current)
    (currentRoot : ∀ wire, wire ∈ current →
      (state.diagram.val.wires wire).scope = state.diagram.val.root)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    result.interface.transportBoundary boundary =
      some (current.map trace.wireMap) := by
  induction trace with
  | done fuel state pending_empty =>
      simpa [wireMap] using stateTransport
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      let oneMap : Fin state.diagram.val.wireCount →
          Fin layout.plugRaw.wireCount := fun wire =>
        layout.frameWire (spliceInput.quotientWire wire)
      have oneScope (wire : Fin state.diagram.val.wireCount) :
          (layout.plugRaw.wires (oneMap wire)).scope =
            layout.frameRegion (state.diagram.val.wires wire).scope := by
        change
          (layout.plugWire
            (layout.quotientBlockWire (spliceInput.quotientWire wire))).scope = _
        rw [layout.plugWire_quotientBlockWire]
        have scopeEq := Splice.Input.coalescedScope_eq_of_boundary_nodup
          spliceInput boundaryNodup (spliceInput.quotientWire wire)
        rw [scopeEq]
        simp [oneMap, spliceInput] <;> rfl
      have oneTransport :
          (spliceFrameInterfaceTransport spliceInput).transportBoundary current =
            some (current.map oneMap) := by
        apply InterfaceTransport.transportBoundary_eq_map
        intro wire member
        unfold spliceFrameInterfaceTransport InterfaceTransport.rootFiltered
        dsimp only
        have targetRoot :
            (layout.plugRaw.wires (oneMap wire)).scope = layout.plugRaw.root := by
          rw [oneScope, currentRoot wire member]
          rfl
        change
          (if (layout.plugRaw.wires (oneMap wire)).scope = layout.plugRaw.root then
              some (oneMap wire)
            else none) = some (oneMap wire)
        rw [if_pos targetRoot]
      let next := advanceInstantiationState comprehension attachments binders
        payload state atom tail site arguments
          (Splice.Input.checkInput_sound input_eq).2
      have nextTransport :
          next.interface.transportBoundary boundary =
            some (current.map oneMap) := by
        rw [advanceInstantiationState_interface]
        calc
          (state.interface.compose
                (spliceFrameInterfaceTransport spliceInput)).transportBoundary
              boundary =
              state.interface.transportBoundary boundary >>=
                (spliceFrameInterfaceTransport spliceInput).transportBoundary :=
            InterfaceTransport.transportBoundary_compose _ _ _
          _ = some (current.map oneMap) := by
            rw [stateTransport]
            exact oneTransport
      have nextRoot : ∀ wire, wire ∈ current.map oneMap →
          (next.diagram.val.wires wire).scope = next.diagram.val.root := by
        have transported :=
          (spliceFrameInterfaceTransport spliceInput).transportBoundary_root_scoped
            currentRoot oneTransport
        simpa [next, advanceInstantiationState, spliceInput] using transported
      have resultTransport := ih (current.map oneMap) nextTransport nextRoot
      simpa [wireMap, oneMap, spliceInput, List.map_map, Function.comp_def]
        using resultTransport

/-- Specialization of `interface_transportBoundary_eq_map` to the executor's
identity-interface initial state. -/
theorem initialInterface_transportBoundary_eq_map
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
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    result.interface.transportBoundary boundary =
      some (boundary.map trace.wireMap) := by
  have initialTransport :
      (initialInstantiationState payload).interface.transportBoundary boundary =
        some boundary := by
    have mapped := InterfaceTransport.transportBoundary_eq_map
      (InterfaceTransport.identity input.val) id
      (boundary := boundary) (by intro wire member; rfl)
    simpa [initialInstantiationState] using mapped
  exact trace.interface_transportBoundary_eq_map boundary boundary
    initialTransport sourceRoot boundaryNodup

/-- The complete successful instantiation interface—copy splices, processed
atom deletion, and final vacuous promotion—transports an ordered source
boundary exactly to the boundary used by `finalSourceOpen`. -/
theorem finalInterface_transportBoundary_eq_map
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
    {raw : ConcreteDiagram}
    (hraw : vacuousElimRaw? (dropInstantiationAtomsRaw result) result.bubble =
      some raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (boundaryNodup : comprehension.val.boundary.Nodup) :
    let toDropped := result.interface.compose
      (InterfaceTransport.byWireCount result.diagram.val
        (dropInstantiationAtomsRaw result) rfl)
    (toDropped.compose (vacuousElimInterfaceTransport hraw)).transportBoundary
        boundary =
      some (boundary.map fun wire =>
        Fin.cast (vacuousElimRaw?_wireCount hraw).symm (trace.wireMap wire)) := by
  let copiedBoundary := boundary.map trace.wireMap
  have copyTransport : result.interface.transportBoundary boundary =
      some copiedBoundary :=
    trace.initialInterface_transportBoundary_eq_map boundary sourceRoot
      boundaryNodup
  have copiedRoot : ∀ wire, wire ∈ copiedBoundary →
      (result.diagram.val.wires wire).scope = result.diagram.val.root :=
    result.interface.transportBoundary_root_scoped sourceRoot copyTransport
  let dropTransport := InterfaceTransport.byWireCount result.diagram.val
    (dropInstantiationAtomsRaw result) rfl
  have dropBoundary : dropTransport.transportBoundary copiedBoundary =
      some copiedBoundary := by
    let dropMap : Fin result.diagram.val.wireCount →
        Fin (dropInstantiationAtomsRaw result).wireCount := fun wire =>
      Fin.cast rfl wire
    have mapped := InterfaceTransport.transportBoundary_eq_map dropTransport
      dropMap
      (boundary := copiedBoundary) (by
        intro wire member
        unfold dropTransport InterfaceTransport.byWireCount
          InterfaceTransport.rootFiltered
        dsimp only
        have droppedRoot :
            ((dropInstantiationAtomsRaw result).wires wire).scope =
              (dropInstantiationAtomsRaw result).root := by
          simpa [dropInstantiationAtomsRaw] using copiedRoot wire member
        change
          (if ((dropInstantiationAtomsRaw result).wires (dropMap wire)).scope =
                (dropInstantiationAtomsRaw result).root then
              some (dropMap wire)
            else none) = some (dropMap wire)
        have droppedRoot' :
            ((dropInstantiationAtomsRaw result).wires (dropMap wire)).scope =
              (dropInstantiationAtomsRaw result).root := by
          simpa [dropMap] using droppedRoot
        rw [if_pos droppedRoot'])
    have mapEq : copiedBoundary.map dropMap = copiedBoundary := by
      induction copiedBoundary with
      | nil => rfl
      | cons wire rest ih =>
          rw [List.map_cons]
          rw [show dropMap wire = wire from Fin.ext (by rfl), ih]
          rfl
    rw [mapEq] at mapped
    exact mapped
  let toDropped := result.interface.compose dropTransport
  have toDroppedBoundary : toDropped.transportBoundary boundary =
      some copiedBoundary := by
    calc
      toDropped.transportBoundary boundary =
          result.interface.transportBoundary boundary >>=
            dropTransport.transportBoundary :=
        InterfaceTransport.transportBoundary_compose _ _ _
      _ = some copiedBoundary := by
        rw [copyTransport]
        exact dropBoundary
  have droppedRoot : ∀ wire, wire ∈ copiedBoundary →
      ((dropInstantiationAtomsRaw result).wires wire).scope =
        (dropInstantiationAtomsRaw result).root :=
    toDropped.transportBoundary_root_scoped sourceRoot toDroppedBoundary
  have vacuousBoundary :=
    VacuousElimTrace.interfaceTransport_transportBoundary hraw
      finalWellFormed copiedBoundary droppedRoot
  calc
    (toDropped.compose
          (vacuousElimInterfaceTransport hraw)).transportBoundary boundary =
        toDropped.transportBoundary boundary >>=
          (vacuousElimInterfaceTransport hraw).transportBoundary :=
      InterfaceTransport.transportBoundary_compose _ _ _
    _ = some (copiedBoundary.map
          (Fin.cast (vacuousElimRaw?_wireCount hraw).symm)) := by
      rw [toDroppedBoundary]
      exact vacuousBoundary
    _ = some (boundary.map fun wire =>
          Fin.cast (vacuousElimRaw?_wireCount hraw).symm
            (trace.wireMap wire)) := by
      apply congrArg some
      change
        List.map (Fin.cast (vacuousElimRaw?_wireCount hraw).symm)
            (List.map trace.wireMap boundary) = _
      simpa [Function.comp_def] using
        (List.map_map
          (l := boundary)
          (f := trace.wireMap)
          (g := Fin.cast (vacuousElimRaw?_wireCount hraw).symm))

end InstantiationTrace

end VisualProof.Rule
