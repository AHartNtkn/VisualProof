import VisualProof.Concrete.Subgraph.Splice.Input.Layout.Core

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

def plugLayout (input : Input) : PlugLayout input := {}

def spliceChecked (input : Input) : Except Error Checked :=
  match checkInput input with
  | .error error => .error error
  | .ok _ =>
      match checkWellFormed input.plugLayout.plugRaw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok result

theorem spliceChecked_sound
    (hsplice : spliceChecked input = .ok result) :
    result.val = input.plugLayout.plugRaw ∧ input.Admissible := by
  unfold spliceChecked at hsplice
  split at hsplice
  · contradiction
  · rename_i checkedInput hinput
    split at hsplice
    · contradiction
    · rename_i checkedResult hresult
      cases hsplice
      exact ⟨checkWellFormed_preserves_input hresult,
        (checkInput_sound hinput).2⟩

theorem quotientWire_scope_eq_root
    (input : Input) (hadmissible : input.Admissible)
    (wire : Fin input.frame.val.wireCount)
    (hroot : (input.frame.val.wires wire).scope = input.frame.val.root) :
    (input.coalesceFrameRaw.wires (input.quotientWire wire)).scope =
      input.coalesceFrameRaw.root := by
  change input.coalescedScope (input.quotientWire wire) =
    input.frame.val.root
  apply Elaboration.encloses_sheet_eq input.frame.property.root_is_sheet
  have hencloses := input.coalescedScope_encloses_member hadmissible
    (input.quotientWire wire) wire
    ((input.mem_classWires _ _).2 rfl)
  simpa only [hroot] using hencloses

theorem PlugLayout.outputOpenRoot_wellFormed
    (input : Input) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (plugWellFormed : layout.plugRaw.WellFormed)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (layout.outputOpenRoot input sourceBoundary).WellFormed where
  diagram_well_formed := plugWellFormed
  boundary_is_root_scoped := by
    intro outputWire houtput
    change outputWire ∈
      sourceBoundary.map (layout.frameWire ∘ input.quotientWire) at houtput
    obtain ⟨wire, hwire, rfl⟩ := List.mem_map.mp houtput
    have hscope := quotientWire_scope_eq_root input hadmissible wire
      (sourceRoot wire hwire)
    simpa [PlugLayout.outputOpenRoot, PlugLayout.plugRaw,
      PlugLayout.plugWire, PlugLayout.frameWire] using
      congrArg layout.frameRegion hscope

def spliceCheckedResultOpenRaw
    (input : Input) {result : Checked}
    (hsplice : spliceChecked input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) : OpenDiagram where
  diagram := result.val
  boundary :=
    (input.plugLayout.outputOpenRoot input sourceBoundary).boundary.map
      (Fin.cast (congrArg Diagram.wireCount
        (spliceChecked_sound hsplice).1.symm))

theorem spliceCheckedResultOpenRaw_wellFormed
    (input : Input) {result : Checked}
    (hsplice : spliceChecked input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (spliceCheckedResultOpenRaw input hsplice sourceBoundary).WellFormed := by
  have hvalue := (spliceChecked_sound hsplice).1
  have hadmissible := (spliceChecked_sound hsplice).2
  rcases result with ⟨diagram, wellFormed⟩
  dsimp at hvalue ⊢
  subst diagram
  simpa [spliceCheckedResultOpenRaw] using
    input.plugLayout.outputOpenRoot_wellFormed input hadmissible wellFormed
      sourceBoundary sourceRoot

def spliceCheckedResultOpen
    (input : Input) {result : Checked}
    (hsplice : spliceChecked input = .ok result)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) : CheckedOpen :=
  ⟨spliceCheckedResultOpenRaw input hsplice sourceBoundary,
    spliceCheckedResultOpenRaw_wellFormed input hsplice sourceBoundary
      sourceRoot⟩

end VisualProof.Concrete.Splice.Input
