import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceRegionFixed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- The executor-owned atom ledger remains duplicate-free after one accepted
splice.  This is the exact freshness certificate required by forward terminal
extraction at the next copy site. -/
theorem ownedAtoms_nodup_advance
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (pending_eq : state.pendingAtoms = atom :: tail)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (ownedNodup : state.ownedAtoms.Nodup) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).ownedAtoms.Nodup := by
  let layout := (instantiateSpliceInput comprehension attachments binders
    payload state site arguments).plugLayout
  have sourceNodup : (state.processedAtoms ++ atom :: tail).Nodup := by
    simpa [InstantiationState.ownedAtoms, pending_eq] using ownedNodup
  have mappedNodup :
      ((state.processedAtoms ++ atom :: tail).map layout.frameNode).Nodup :=
    sourceNodup.map _ (fun first second distinct equality =>
      distinct (layout.frameNode_injective equality))
  change ((state.processedAtoms.map layout.frameNode ++
    [layout.frameNode atom]) ++ tail.map layout.frameNode).Nodup
  have list_eq :
      (state.processedAtoms.map layout.frameNode ++ [layout.frameNode atom]) ++
          tail.map layout.frameNode =
        (state.processedAtoms ++ atom :: tail).map layout.frameNode := by
    induction state.processedAtoms with
    | nil => rfl
    | cons head rest ih =>
        simp only [List.cons_append]
        exact congrArg (List.cons (layout.frameNode head)) ih
  rw [list_eq]
  exact mappedNodup

/-- Shape and owned-ledger invariants needed at every accepted copy step,
packaged in the same recursive shape as the executor trace.  Binder targets
use `BinderTargetsEveryStep`, whose first witness comes from the first checked
splice rather than from the serialized payload alone. -/
structure StepInvariantAt
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount) : Prop where
  shape : BubbleHasPayloadArity payload state
  ownedNodup : state.ownedAtoms.Nodup

def StepInvariantsEveryStep
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
      state result) : Prop :=
  match trace with
  | .done _ _ _ => True
  | .step _ state _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      StepInvariantAt payload state ∧ StepInvariantsEveryStep rest

theorem stepInvariantsEveryStep_of
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
    (invariant : StepInvariantAt payload state) :
    StepInvariantsEveryStep trace := by
  induction trace with
  | done => trivial
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      let next := advanceInstantiationState comprehension attachments binders
        payload state atom tail site arguments hadmissible
      have nextInvariant : StepInvariantAt payload next := {
        shape := invariant.shape.advance comprehension attachments binders
          payload state atom tail site arguments hadmissible
        ownedNodup := ownedAtoms_nodup_advance comprehension attachments binders
          payload state atom tail site arguments pending_eq hadmissible
          invariant.ownedNodup
      }
      exact ⟨invariant, ih nextInvariant⟩

theorem initial_stepInvariantsEveryStep
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
      (initialInstantiationState payload) result) :
    StepInvariantsEveryStep trace := by
  apply stepInvariantsEveryStep_of trace
  exact {
    shape := initial_bubbleHasPayloadArity payload
    ownedNodup := by
      simpa [InstantiationState.ownedAtoms, initialInstantiationState] using
        boundAtoms_nodup input bubble
  }

end InstantiationSemantic

end VisualProof.Rule
