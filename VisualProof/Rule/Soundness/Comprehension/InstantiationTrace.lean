import VisualProof.Rule.Comprehension.Semantics

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

/-- Proof-relevant replay of the successful `instantiateCopies` branch.  Every
constructor records the exact checked splice and the exact state transition
used by the executor. -/
inductive InstantiationTrace
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature} :
    Nat →
      InstantiationState origin attachments.length
        payload.binderSpine.proxyCount →
      InstantiationState origin attachments.length
        payload.binderSpine.proxyCount → Prop
  | done (fuel state)
      (pending_empty : state.pendingAtoms = []) :
      InstantiationTrace comprehension attachments binders payload fuel state
        state
  | step (fuel state result)
      (atom : Fin state.diagram.val.nodeCount)
      (tail : List (Fin state.diagram.val.nodeCount))
      (site candidate : Fin state.diagram.val.regionCount)
      (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
      (checkedInput : Splice.Input.CheckedInput signature)
      (pending_eq : state.pendingAtoms = atom :: tail)
      (node_eq : state.diagram.val.nodes atom = .atom site candidate)
      (candidate_eq : candidate = state.bubble)
      (arguments_eq : instantiateArguments? state atom payload.arity =
        some arguments)
      (input_eq : Splice.Input.checkInput
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments) = .ok checkedInput)
      (rest : InstantiationTrace comprehension attachments binders payload fuel
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments
          (Splice.Input.checkInput_sound input_eq).2)
        result) :
      InstantiationTrace comprehension attachments binders payload (fuel + 1)
        state result

/-- A successful executor run exposes its complete checked-splice trace. -/
theorem instantiateCopies_success_trace
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
    (fuel : Nat)
    (state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (hcopy : instantiateCopies comprehension attachments binders payload fuel
      state = .ok result) :
    InstantiationTrace comprehension attachments binders payload fuel state
      result := by
  induction fuel generalizing state result with
  | zero =>
      cases hpending : state.pendingAtoms with
      | nil =>
          simp [instantiateCopies, hpending] at hcopy
          subst result
          exact .done 0 state hpending
      | cons atom tail =>
          simp [instantiateCopies, hpending] at hcopy
  | succ fuel ih =>
      cases hpending : state.pendingAtoms with
      | nil =>
          simp [instantiateCopies, hpending] at hcopy
          subst result
          exact .done (fuel + 1) state hpending
      | cons atom tail =>
          simp only [instantiateCopies, hpending] at hcopy
          split at hcopy <;> try contradiction
          rename_i site candidate hnode
          split at hcopy <;> try contradiction
          rename_i hcandidate
          split at hcopy <;> try contradiction
          rename_i arguments harguments
          split at hcopy <;> try contradiction
          rename_i checkedInput hinput
          exact .step fuel state result atom tail site candidate arguments
            checkedInput hpending hnode hcandidate harguments hinput
            (ih _ _ hcopy)

end VisualProof.Rule
