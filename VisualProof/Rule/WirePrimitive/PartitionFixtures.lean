import VisualProof.Rule.WirePrimitive.Partition

namespace VisualProof

namespace WirePrimitive

namespace PartitionFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def error?
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source} :
    Except WirePartitionError (AppliedWireSever source input) →
      Option WirePartitionError
  | .error error => some error
  | .ok _ => none

private def joinError?
    {source : CheckedDiagram definitions}
    {input : WireJoinInput source} :
    Except WirePartitionError (AppliedWireJoin source input) →
      Option WirePartitionError
  | .error error => some error
  | .ok _ => none

/-! `.iota` remains one ordinary signature instance. -/

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

private def iotaSeverInput : WireSeverInput iotaSeverSource where
  orientation := .forward
  wire := idx 0
  keep := [⟨idx 0, .identity 0⟩]
  scope := idx 0

example :
    (applyWireSever iotaSeverSource iotaSeverInput).toOption.map
      (fun applied =>
        (applied.target.val.wireCount,
          applied.target.val.wiresList.getLast?.map fun wire =>
            (applied.target.val.wires wire).sig)) =
      some (2, some .iota) := by
  native_decide

example
    (applied : AppliedWireSever iotaSeverSource iotaSeverInput)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv iotaSeverSource)
      (denoteChecked pre definitionEnv applied.target) := by
  exact wire_sever_sound iotaSeverInput applied pre definitionEnv

/-!
Nested relation signature, moved-endpoint enclosure, and chosen-scope
polarity. The original wire is root-scoped; the moved endpoint and fresh wire
are scoped at the child cut.
-/

private def nestedSig : Sig := .rel [.rel [.iota]]

private def nestedScopedRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 1
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 nestedSig 2
    | ⟨1, _⟩ => .identity 1 nestedSig 2
  wires := fun _ =>
    { sig := nestedSig
      scope := 0
      endpoints :=
        [⟨0, .identity 0⟩, ⟨0, .identity 1⟩,
          ⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

private theorem nestedScopedRaw_wellFormed :
    nestedScopedRaw.WellFormed [] := by
  constructor <;> native_decide

private def nestedScopedSource : CheckedDiagram [] :=
  ⟨nestedScopedRaw, nestedScopedRaw_wellFormed⟩

private def nestedScopedSever : WireSeverInput nestedScopedSource where
  orientation := .backward
  wire := idx 0
  keep := [⟨idx 0, .identity 0⟩, ⟨idx 0, .identity 1⟩]
  scope := idx 1

private def nestedScopedApplied :
    AppliedWireSever nestedScopedSource nestedScopedSever :=
  (applyWireSever nestedScopedSource nestedScopedSever).toOption.get
    (by native_decide)

example :
    ((nestedScopedApplied.target.val.wires (idx 1)).sig,
      (nestedScopedApplied.target.val.wires (idx 1)).scope.val,
      (nestedScopedApplied.target.val.wires (idx 1)).endpoints) =
      (nestedSig, 1,
        [⟨idx 1, .identity 0⟩, ⟨idx 1, .identity 1⟩]) := by
  native_decide

example
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .backward
      (denoteChecked pre definitionEnv nestedScopedSource)
      (denoteChecked pre definitionEnv nestedScopedApplied.target) := by
  exact
    wire_sever_sound nestedScopedSever nestedScopedApplied pre definitionEnv

private def wrongNestedPolarity : WireSeverInput nestedScopedSource :=
  { nestedScopedSever with orientation := .forward }

example :
    error? (applyWireSever nestedScopedSource wrongNestedPolarity) =
      some .severRequiresPositive := by
  native_decide

private def movedEndpointOutsideScope : WireSeverInput nestedScopedSource where
  orientation := .backward
  wire := idx 0
  keep := [⟨idx 1, .identity 0⟩, ⟨idx 1, .identity 1⟩]
  scope := idx 1

example :
    error? (applyWireSever nestedScopedSource movedEndpointOutsideScope) =
      some .movedEndpointOutsideScope := by
  native_decide

/-! Nullary relation signatures merge exactly like every other signature. -/

private def nullaryJoinRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 (.rel []) 2
    | ⟨1, _⟩ => .identity 1 (.rel []) 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

private theorem nullaryJoinRaw_wellFormed :
    nullaryJoinRaw.WellFormed [] := by
  native_decide

private def nullaryJoinSource : CheckedDiagram [] :=
  ⟨nullaryJoinRaw, nullaryJoinRaw_wellFormed⟩

private def nullaryJoinInput : WireJoinInput nullaryJoinSource where
  orientation := .forward
  left := idx 0
  right := idx 1

private def nullaryJoinApplied :
    AppliedWireJoin nullaryJoinSource nullaryJoinInput :=
  (applyWireJoin nullaryJoinSource nullaryJoinInput).toOption.get
    (by native_decide)

example :
    (nullaryJoinApplied.target.val.wireCount,
      (nullaryJoinApplied.target.val.wires (idx 0)).sig,
      (nullaryJoinApplied.target.val.wires (idx 0)).scope.val) =
      (1, .rel [], 0) := by
  native_decide

example
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv nullaryJoinSource)
      (denoteChecked pre definitionEnv nullaryJoinApplied.target) := by
  exact wire_join_sound nullaryJoinInput nullaryJoinApplied pre definitionEnv

/-! Sibling scopes are incomparable and therefore cannot merge. -/

private def incomparableRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 2
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 1 (.rel []) 2
    | ⟨1, _⟩ => .identity 2 (.rel []) 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 2
          endpoints := [⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

private theorem incomparableRaw_wellFormed :
    incomparableRaw.WellFormed [] := by
  native_decide

private def incomparableSource : CheckedDiagram [] :=
  ⟨incomparableRaw, incomparableRaw_wellFormed⟩

private def incomparableJoin : WireJoinInput incomparableSource where
  orientation := .forward
  left := idx 0
  right := idx 1

example :
    joinError? (applyWireJoin incomparableSource incomparableJoin) =
      some .incomparableScopes := by
  native_decide

/-!
Merge may consume a non-head endpoint. The inner nullary-relation wire owns
an atom argument endpoint; later content primitives must refuse this same
shape because they act only on applied heads.
-/

private def nonHeadRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 0 (.rel []) 2
    | ⟨1, _⟩ => .atom 1 [.rel []]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨1, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.rel []]
          scope := 1
          endpoints := [⟨1, .head⟩] }

private theorem nonHeadRaw_wellFormed :
    nonHeadRaw.WellFormed [] := by
  native_decide

private def nonHeadSource : CheckedDiagram [] :=
  ⟨nonHeadRaw, nonHeadRaw_wellFormed⟩

private def nonHeadJoin : WireJoinInput nonHeadSource where
  orientation := .forward
  left := idx 0
  right := idx 1

example :
    (applyWireJoin nonHeadSource nonHeadJoin).toOption.map
      (fun applied =>
        (applied.target.val.wireCount,
          applied.target.val.wiresList.head?.map fun wire =>
            (applied.target.val.wires wire).endpoints.map fun endpoint =>
              (endpoint.node.val, endpoint.port))) =
      some
        (2, some
          [(0, .identity 0), (0, .identity 1), (1, .arg 0)]) := by
  native_decide

end PartitionFixtures

end WirePrimitive

end VisualProof
