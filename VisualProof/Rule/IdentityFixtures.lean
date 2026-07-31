import VisualProof.Rule.Identity

namespace VisualProof
namespace IdentityFixtures

open ConcreteDiagram
open StructuralCore
open WirePrimitive.Partition

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def nestedSig : Sig := .rel [.rel [], .iota]

/-!
The zero-outer case lives at even cut depth.  Three distinct local wires make
the collapse rule, rather than degenerate deletion, authoritative.
-/
private def allCoScopedRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 nestedSig 3
  wires
    | ⟨0, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 2⟩] }

private theorem allCoScopedRaw_wellFormed :
    allCoScopedRaw.WellFormed [] := by
  native_decide

private def allCoScoped : CheckedDiagram [] :=
  ⟨allCoScopedRaw, allCoScopedRaw_wellFormed⟩

example :
    (collapseOnePoint allCoScoped (idx 0)).map
        (fun rewrite =>
          (rewrite.target.val.nodeCount,
            rewrite.target.val.wiresList.map fun wire =>
              ((rewrite.target.val.wires wire).sig,
                (rewrite.target.val.wires wire).scope.val))) =
      some (0, [(nestedSig, 0)]) := by
  native_decide

/-!
The one-outer case lives at odd cut depth.  The outer wire is deliberately
second in concrete order: eligibility must select it as the representative,
then preserve its signature and root scope.
-/
private def oneOuterRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .identity 1 nestedSig 3
  wires
    | ⟨0, _⟩ =>
        { sig := nestedSig
          scope := 1
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := nestedSig
          scope := 1
          endpoints := [⟨0, .identity 2⟩] }

private theorem oneOuterRaw_wellFormed :
    oneOuterRaw.WellFormed [] := by
  native_decide

private def oneOuter : CheckedDiagram [] :=
  ⟨oneOuterRaw, oneOuterRaw_wellFormed⟩

private def oneOuterRewrite : IdentityRewrite oneOuter :=
  (collapseOnePoint oneOuter (idx 0)).get (by native_decide)

example :
    (oneOuterRewrite.target.val.nodeCount,
      oneOuterRewrite.target.val.wireCount,
      (oneOuterRewrite.target.val.wires (idx 0)).sig,
      (oneOuterRewrite.target.val.wires (idx 0)).scope.val,
      (oneOuterRewrite.wireImage (idx 0)).val,
      (oneOuterRewrite.wireImage (idx 1)).val,
      (oneOuterRewrite.wireImage (idx 2)).val) =
      (0, 1, nestedSig, 0, 0, 0, 0) := by
  native_decide

example :
    (normalizeOneIdentity oneOuter).isSome = true := by
  native_decide

/-!
Two outer wires are the exact refusal boundary.  The local third wire ensures
the source is nondegenerate while the two outer scopes remain comparable.
-/
private def twoOuterRaw : ConcreteDiagram 0 where
  regionCount := 3
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
  nodes := fun _ => .identity 2 nestedSig 3
  wires
    | ⟨0, _⟩ =>
        { sig := nestedSig
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := nestedSig
          scope := 1
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := nestedSig
          scope := 2
          endpoints := [⟨0, .identity 2⟩] }

private theorem twoOuterRaw_wellFormed :
    twoOuterRaw.WellFormed [] := by
  native_decide

private def twoOuter : CheckedDiagram [] :=
  ⟨twoOuterRaw, twoOuterRaw_wellFormed⟩

example :
    (collapseOnePoint twoOuter (idx 0)).isNone = true := by
  native_decide

example :
    (normalizeOneIdentity twoOuter).isNone = true := by
  native_decide

/-! Soundness is pinned at both even and odd cut parity. -/
example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv allCoScoped ↔
      denoteChecked pre definitionEnv
        (normalizeIdentities allCoScoped).target :=
  normalizeIdentities_sound allCoScoped pre definitionEnv
    |>.symm

example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv oneOuter ↔
      denoteChecked pre definitionEnv
        (normalizeIdentities oneOuter).target :=
  normalizeIdentities_sound oneOuter pre definitionEnv
    |>.symm

/-!
Derived substitution uses only the ordinary copy receipt, scoped sever, and
eager normalization.  The source identity lives in region 1 with both `a`
and `b` root-scoped, so neither it nor its copied instance can normalize
before severing.  The two atom sites pin forward severing at even depth and
backward severing at odd depth on the same checked host.
-/
private def substitutionPatternRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .identity 0 .iota 2
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 1⟩] } }
  boundary := [0, 1]

private theorem substitutionPatternRaw_wellFormed :
    substitutionPatternRaw.WellFormed [] := by
  constructor <;> native_decide

private def substitutionPattern : CheckedOpenDiagram [] :=
  ⟨substitutionPatternRaw, substitutionPatternRaw_wellFormed⟩

private def substitutionHostRaw : ConcreteDiagram 0 where
  regionCount := 4
  nodeCount := 3
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
    | ⟨3, _⟩ => .cut 2
  nodes
    | ⟨0, _⟩ => .identity 1 .iota 2
    | ⟨1, _⟩ => .atom 2 [.iota]
    | ⟨2, _⟩ => .atom 3 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 0⟩, ⟨1, .arg 0⟩, ⟨2, .arg 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 2
          endpoints := [⟨1, .head⟩] }
    | ⟨3, _⟩ =>
        { sig := .rel [.iota]
          scope := 3
          endpoints := [⟨2, .head⟩] }

private theorem substitutionHostRaw_wellFormed :
    substitutionHostRaw.WellFormed [] := by
  native_decide

private def substitutionHost : CheckedDiagram [] :=
  ⟨substitutionHostRaw, substitutionHostRaw_wellFormed⟩

private def substitutionOccurrenceInput :
    OccurrenceInput substitutionPattern substitutionHost where
  region := idx 1
  regionMap := fun _ => idx 1
  nodeMap := fun _ => idx 0
  wireMap
    | ⟨0, _⟩ => idx 0
    | ⟨1, _⟩ => idx 1

private def substitutionOccurrence :
    Occurrence substitutionPattern substitutionHost :=
  (checkOccurrence substitutionOccurrenceInput).toOption.get
    (by native_decide)

private def evenIterationInput :
    OrdinaryIterationInput substitutionOccurrence.toSelection
      substitutionOccurrence where
  destination := idx 2

private def oddIterationInput :
    OrdinaryIterationInput substitutionOccurrence.toSelection
      substitutionOccurrence where
  destination := idx 3

private def evenIteration :
    CheckedOrdinaryIteration evenIterationInput :=
  (checkOrdinaryIteration evenIterationInput).toOption.get
    (by native_decide)

private def oddIteration :
    CheckedOrdinaryIteration oddIterationInput :=
  (checkOrdinaryIteration oddIterationInput).toOption.get
    (by native_decide)

example :
    (evenIteration.target.val.nodeCount,
      oddIteration.target.val.nodeCount) = (4, 4) := by
  native_decide

/-! Plain iteration preserves the copied identity's exact `a,b` attachments. -/
example :
    (evenIteration.target.val.endpointOwner?
        ⟨idx 3, .identity 0⟩,
      evenIteration.target.val.endpointOwner?
        ⟨idx 3, .identity 1⟩,
      oddIteration.target.val.endpointOwner?
        ⟨idx 3, .identity 0⟩,
      oddIteration.target.val.endpointOwner?
        ⟨idx 3, .identity 1⟩) =
      (some (idx 0), some (idx 1), some (idx 0), some (idx 1)) := by
  native_decide

private def evenSeverInput : WireSeverInput evenIteration.target where
  orientation := .forward
  wire := idx 0
  keep := [⟨idx 0, .identity 0⟩, ⟨idx 2, .arg 0⟩]
  scope := idx 2

private def oddSeverInput : WireSeverInput oddIteration.target where
  orientation := .backward
  wire := idx 0
  keep := [⟨idx 0, .identity 0⟩, ⟨idx 1, .arg 0⟩]
  scope := idx 3

private def evenSever : AppliedWireSever evenIteration.target evenSeverInput :=
  (applyWireSever evenIteration.target evenSeverInput).toOption.get
    (by native_decide)

private def oddSever : AppliedWireSever oddIteration.target oddSeverInput :=
  (applyWireSever oddIteration.target oddSeverInput).toOption.get
    (by native_decide)

private def evenNormalized := normalizeIdentities evenSever.target
private def oddNormalized := normalizeIdentities oddSever.target

/-!
The selected atom argument lands on `b`; the other atom remains attached to
`a`.  The copied identity and the fresh sever wire are both absent afterward.
-/
example :
    (evenNormalized.target.val.nodeCount,
      evenNormalized.target.val.wireCount,
      evenNormalized.target.val.endpointOwner?
        ⟨idx 1, .arg 0⟩,
      evenNormalized.target.val.endpointOwner?
        ⟨idx 2, .arg 0⟩) =
      (3, 4, some (idx 1), some (idx 0)) := by
  native_decide

example :
    (oddNormalized.target.val.nodeCount,
      oddNormalized.target.val.wireCount,
      oddNormalized.target.val.endpointOwner?
        ⟨idx 1, .arg 0⟩,
      oddNormalized.target.val.endpointOwner?
        ⟨idx 2, .arg 0⟩) =
      (3, 4, some (idx 0), some (idx 1)) := by
  native_decide

example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    Directed .forward
      (denoteChecked pre definitionEnv evenIteration.source)
      (denoteChecked pre definitionEnv evenNormalized.target) :=
  identity_substitution_derived_sound
    evenIteration evenSeverInput evenSever pre definitionEnv

example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    Directed .backward
      (denoteChecked pre definitionEnv oddIteration.source)
      (denoteChecked pre definitionEnv oddNormalized.target) :=
  identity_substitution_derived_sound
    oddIteration oddSeverInput oddSever pre definitionEnv

end IdentityFixtures
end VisualProof
