import VisualProof.Rule.WirePrimitive.Arguments

namespace VisualProof

namespace WirePrimitive

namespace ArgumentsFixtures

open ConcreteWirePrimitive

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def concreteError? {α : Type} :
    Except WireArgumentError α → Option WireArgumentError
  | .error error => some error
  | .ok _ => none

/-!
One applied end sits at the acted wire's own scope and the other is nested
under two cuts.  This single corpus exercises all-end coverage, scope
visibility, endpoint-local arity binders at both the frame boundary and an
intrinsic nested region, and exact signature comparison.
-/
private def nestedRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 5
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes
    | ⟨0, _⟩ => .atom 0 [.rel [.iota], .iota]
    | ⟨1, _⟩ => .atom 2 [.rel [.iota], .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.rel [.iota], .iota]
          scope := 0
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .arg 0⟩, ⟨1, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 1⟩, ⟨1, .arg 1⟩] }
    | ⟨3, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [] }
    | ⟨4, _⟩ =>
        { sig := .iota
          scope := 2
          endpoints := [] }

private theorem nestedRaw_wellFormed : nestedRaw.WellFormed [] := by
  native_decide

private def nested : CheckedDiagram [] :=
  ⟨nestedRaw, nestedRaw_wellFormed⟩

private def shifted :=
  (applyArityShift nested (idx 0) (.rel [])).toOption.get
    (by native_decide)

example :
    ((shifted.target.val.wires (idx 5)).scope,
      (shifted.target.val.wires (idx 6)).scope,
      (shifted.target.val.wires (idx 5)).endpoints.length,
      (shifted.target.val.wires (idx 6)).endpoints.length) =
      (idx 0, idx 2, 1, 1) := by
  native_decide

private def unshifted :=
  (applyArityUnshift shifted.target (idx 4) 2).toOption.get
    (by native_decide)

example :
    (unshifted.target.val.wires (idx 4)).sig =
      .rel [.rel [.iota], .iota] := by
  native_decide

example :
    concreteError? (applyArityUnshift nested (idx 0) 0) =
      some (.concreteRejected .unshiftWireNotLocal) := by
  native_decide

example :
    concreteError? (applyArgPermute nested (idx 0) [0, 0]) =
      some (.concreteRejected .invalidPermutation) := by
  native_decide

private def permuted :=
  (applyArgPermute nested (idx 0) [1, 0]).toOption.get
    (by native_decide)

example :
    (permuted.target.val.wires (idx 4)).sig =
      .rel [.iota, .rel [.iota]] := by
  native_decide

private def duplicated :=
  (applyArgDuplicate nested (idx 0) 1).toOption.get
    (by native_decide)

private def contracted :=
  (applyArgContract duplicated.target (idx 4) 1).toOption.get
    (by native_decide)

example :
    (contracted.target.val.wires (idx 4)).sig =
      .rel [.rel [.iota], .iota] := by
  native_decide

example :
    concreteError? (applyArgContract nested (idx 0) 0) =
      some (.concreteRejected .unequalAdjacentSignatures) := by
  native_decide

example :
    concreteError? (applyArgDrop nested (idx 0) 1 .forward) = none := by
  native_decide

example :
    concreteError?
      (applyArgExtend nested (idx 0) 2 .iota
        [idx 2, idx 2] .backward) = none := by
  native_decide

example :
    concreteError?
      (applyArgExtend nested (idx 0) 2 .iota
        [idx 2] .forward) =
      some (.concreteRejected .attachmentCoverage) := by
  native_decide

example :
    concreteError?
      (applyArgExtend nested (idx 0) 2 .iota
        [idx 4, idx 4] .forward) =
      some (.concreteRejected .attachmentInvisible) := by
  native_decide

example :
    concreteError?
      (applyArgExtend nested (idx 0) 2 .iota
        [idx 2, idx 3] .forward) = none := by
  native_decide

example :
    concreteError?
      (applyArgExtend nested (idx 0) 2 .iota
        [idx 2, idx 3] .backward) =
      some .extendBackwardRequiresNegative := by
  native_decide

private def emptyRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := Fin.elim0
  wires := fun _ =>
    { sig := .rel [.iota]
      scope := 0
      endpoints := [] }

private theorem emptyRaw_wellFormed : emptyRaw.WellFormed [] := by
  native_decide

private def empty : CheckedDiagram [] :=
  ⟨emptyRaw, emptyRaw_wellFormed⟩

example :
    concreteError? (applyArityShift empty (idx 0) .iota) = none := by
  native_decide

example :
    concreteError? (applyArgDrop empty (idx 0) 0 .forward) =
      some .dropRequiresNegative := by
  native_decide

example :
    concreteError? (applyArgDrop empty (idx 0) 0 .backward) = none := by
  native_decide

example :
    concreteError?
      (applyArgExtend empty (idx 0) 1 .iota [] .forward) = none := by
  native_decide

example :
    concreteError?
      (applyArgExtend empty (idx 0) 1 .iota [] .backward) =
      some .extendBackwardRequiresNegative := by
  native_decide

#check applyArityShift
#check applyArityUnshift
#check applyArgPermute
#check applyArgDuplicate
#check applyArgContract
#check applyArgDrop
#check applyArgExtend

#check arity_shift_sound
#check arity_unshift_sound
#check arg_permute_sound
#check arg_duplicate_sound
#check arg_contract_sound
#check arg_drop_sound
#check arg_extend_sound

end ArgumentsFixtures

end WirePrimitive

end VisualProof
