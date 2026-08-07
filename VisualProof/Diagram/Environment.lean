import VisualProof.Diagram.Rename

namespace VisualProof.Diagram

def extendWireEnv (outerEnv : Fin outer → D) (localEnv : Fin localWires → D) :
    Fin (outer + localWires) → D :=
  Fin.addCases outerEnv localEnv

@[simp] theorem extendWireEnv_zero (outerEnv : Fin outer → D)
    (localEnv : Fin 0 → D) :
    extendWireEnv outerEnv localEnv = outerEnv := by
  funext i
  let j : Fin outer := Fin.cast (Nat.add_zero outer) i
  have hi : i = Fin.castAdd 0 j := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_left j

end VisualProof.Diagram
