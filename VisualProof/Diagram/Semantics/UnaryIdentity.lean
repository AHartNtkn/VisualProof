import VisualProof.Diagram.Semantics
import VisualProof.Diagram.UnaryIdentity

namespace VisualProof.Diagram

open VisualProof.Theory

theorem ItemSeq.pinWires_denotes
    (source : List Sig) (renameWires : WireRenaming source target)
    (selected : ∀ {signature}, Var source signature → Bool)
    (model : Model) (env : Values model target) :
    denoteItemSeq model env (ItemSeq.pinWires source renameWires selected) := by
  induction source with
  | nil => trivial
  | cons signature rest induction =>
      simp only [ItemSeq.pinWires]
      split
      · exact ⟨denoteItem_unary_identity model env _,
          induction
            ⟨fun wire => renameWires (.there wire)⟩
            (fun wire => selected (.there wire))⟩
      · exact induction
          ⟨fun wire => renameWires (.there wire)⟩
          (fun wire => selected (.there wire))

end VisualProof.Diagram
