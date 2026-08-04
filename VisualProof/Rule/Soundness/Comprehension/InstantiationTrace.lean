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
        payload.binderSpine.proxyCount → Type
  | done (fuel state)
      (pending_empty : state.pendingAtoms = []) :
      InstantiationTrace comprehension attachments binders payload fuel state
        state
  | step (fuel state result)
      (atom : Fin state.diagram.val.nodeCount)
      (tail : List (Fin state.diagram.val.nodeCount))
      (site candidate : Fin state.diagram.val.regionCount)
      (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
      (plan : InstantiationCopyPlan comprehension attachments binders payload
        state atom tail site arguments)
      (pending_eq : state.pendingAtoms = atom :: tail)
      (node_eq : state.diagram.val.nodes atom = .atom site candidate)
      (candidate_eq : candidate = state.bubble)
      (arguments_eq : instantiateArguments? state atom payload.arity =
        some arguments)
      (rest : InstantiationTrace comprehension attachments binders payload fuel
        plan.next
        result) :
      InstantiationTrace comprehension attachments binders payload (fuel + 1)
        state result

/-- A successful executor run exposes its complete checked-splice trace. -/
def instantiateCopiesSuccessTrace
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
      simp only [instantiateCopies] at hcopy
      split at hcopy
      · rename_i hpending
        cases hcopy
        exact .done 0 state (List.isEmpty_iff.mp hpending)
      · contradiction
  | succ fuel ih =>
      simp only [instantiateCopies] at hcopy
      split at hcopy
      · rename_i hpending
        cases hcopy
        exact .done (fuel + 1) state hpending
      · rename_i atom tail hpending
        split at hcopy <;> try contradiction
        rename_i site candidate hnode
        split at hcopy <;> try contradiction
        rename_i hcandidate
        split at hcopy <;> try contradiction
        rename_i arguments harguments
        split at hcopy <;> try contradiction
        rename_i plan hplan
        exact .step fuel state result atom tail site candidate arguments plan
          hpending hnode hcandidate harguments (ih plan.next result hcopy)

end VisualProof.Rule
