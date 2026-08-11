import VisualProof.Concrete.Elaboration.SpliceOccurrence
import VisualProof.Diagram.RenamingIsomorphism

/-! Item-sequence permutations used by splice elaboration. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace Splice

/-- Reorder the compiler's node-then-child blocks into the splice model's
frame-then-material blocks, without changing the ambient wire carrier. -/
noncomputable def nodeChildBlocksToFrameMaterialBlocks
    (frameNodes materialNodes frameChildren materialChildren :
      ItemSeq wires rels) :
    ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
      ((frameNodes.append materialNodes).append
        (frameChildren.append materialChildren))
      ((frameNodes.append frameChildren).append
        (materialNodes.append materialChildren)) := by
  have middleSwap :
      ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
        (materialNodes.append frameChildren)
        (frameChildren.append materialNodes) := by
    simpa only [FiniteEquiv.refl, ItemSeq.renameWires_id] using
      ItemSeqIso.appendCommRename materialNodes frameChildren
        (FiniteEquiv.refl (Fin wires))
  have middleWithTail := ItemSeqIso.append middleSwap
    (ItemSeqIso.refl materialChildren)
  have reorderedTail :
      ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
        (materialNodes.append (frameChildren.append materialChildren))
        (frameChildren.append (materialNodes.append materialChildren)) := by
    simpa only [ItemSeq.append_assoc] using middleWithTail
  have reordered := ItemSeqIso.append (ItemSeqIso.refl frameNodes)
    reorderedTail
  simpa only [ItemSeq.append_assoc] using reordered

end Splice

end VisualProof.Concrete
