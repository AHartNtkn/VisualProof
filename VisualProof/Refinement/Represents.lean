import VisualProof.Concrete.Encode
import VisualProof.Concrete.State

namespace VisualProof

open VisualProof.Diagram

def Represents
    (concrete : Concrete.OpenDiagram)
    (diagram : OpenDiagram concrete.boundary.length) : Prop :=
  ∃ translated,
    Concrete.translate concrete = .ok translated ∧
    OpenDiagram.Isomorphic translated diagram

def StateRepresents
    (state : Concrete.State arity)
    (diagram : OpenDiagram arity) : Prop :=
  Represents state.checked.val
    (diagram.castArity state.boundary_length.symm)

def Concrete.State.translate (state : Concrete.State arity) :
    Except Concrete.Error (VisualProof.Diagram.OpenDiagram arity) :=
  (Concrete.translate state.checked.val).map
    (fun diagram => diagram.castArity state.boundary_length)

theorem Concrete.State.translate_checked (state : Concrete.State arity) :
    state.translate =
      .ok (state.checked.elaborate.castArity state.boundary_length) := by
  unfold Concrete.State.translate
  rw [Concrete.translate_checked]
  rfl

theorem encode_represents (diagram : OpenDiagram arity) :
    StateRepresents (Concrete.encode diagram) diagram := by
  exact ⟨(Concrete.encode diagram).checked.elaborate,
    Concrete.translate_checked (Concrete.encode diagram).checked,
    Concrete.encode_elaborate_isomorphic diagram⟩

theorem checked_represents (concrete : Concrete.CheckedOpen) :
    Represents concrete.val concrete.elaborate := by
  exact ⟨concrete.elaborate, Concrete.translate_checked concrete,
    OpenDiagram.Isomorphic.refl concrete.elaborate⟩

theorem represents_unique
    (first : Represents concrete firstDiagram)
    (second : Represents concrete secondDiagram) :
    OpenDiagram.Isomorphic firstDiagram secondDiagram := by
  rcases first with ⟨firstTranslated, firstTranslation, firstIso⟩
  rcases second with ⟨secondTranslated, secondTranslation, secondIso⟩
  have translatedEq : firstTranslated = secondTranslated := by
    rw [firstTranslation] at secondTranslation
    exact Except.ok.inj secondTranslation
  subst secondTranslated
  exact firstIso.symm.trans secondIso

theorem representation_complete (diagram : OpenDiagram arity) :
    ∃ (concrete : Concrete.OpenDiagram)
      (arity_eq : concrete.boundary.length = arity),
      Represents concrete (diagram.castArity arity_eq.symm) := by
  exact ⟨(Concrete.encode diagram).checked.val,
    (Concrete.encode diagram).boundary_length, encode_represents diagram⟩

end VisualProof
