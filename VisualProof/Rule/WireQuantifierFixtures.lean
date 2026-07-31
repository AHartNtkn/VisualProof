import VisualProof.Rule.WireQuantifier

namespace VisualProof
namespace WireQuantifierFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def iotaSeverRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }

private theorem iotaSeverRaw_wellFormed :
    iotaSeverRaw.WellFormed [] := by
  native_decide

private def iotaSeverSource : CheckedDiagram [] :=
  ⟨iotaSeverRaw, iotaSeverRaw_wellFormed⟩

private def iotaSeverInput : WireSeverInput iotaSeverSource :=
  .iota .forward (idx 0) [⟨idx 0, .identity 0⟩]

example :
    (applyWireSever iotaSeverSource iotaSeverInput).toOption.map
      (fun applied => applied.target.val.wireCount) =
      some 2 := by
  native_decide

example
    (applied : AppliedWireSever iotaSeverSource iotaSeverInput)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv iotaSeverSource)
      (denoteChecked pre definitionEnv applied.target) := by
  exact
    iota_sever_sound .forward (idx 0) [⟨idx 0, .identity 0⟩]
      applied pre definitionEnv

private def iotaJoinRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .identity 1⟩] }

private theorem iotaJoinRaw_wellFormed :
    iotaJoinRaw.WellFormed [] := by
  native_decide

private def iotaJoinSource : CheckedDiagram [] :=
  ⟨iotaJoinRaw, iotaJoinRaw_wellFormed⟩

private def iotaJoinInput : WireJoinInput iotaJoinSource :=
  .iota .forward (idx 0) (idx 1)

example :
    (applyWireJoin iotaJoinSource iotaJoinInput).toOption.map
      (fun applied => applied.target.val.wireCount) =
      some 1 := by
  native_decide

example
    (applied : AppliedWireJoin iotaJoinSource iotaJoinInput)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv iotaJoinSource)
      (denoteChecked pre definitionEnv applied.target) := by
  exact
    iota_join_sound .forward (idx 0) (idx 1)
      applied pre definitionEnv

end WireQuantifierFixtures
end VisualProof
