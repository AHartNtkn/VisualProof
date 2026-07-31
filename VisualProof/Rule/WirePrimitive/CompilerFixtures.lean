import VisualProof.Rule.WirePrimitive.CompilerSoundness

namespace VisualProof

namespace WirePrimitive

namespace CompilerFixtures

/-!
This fixture module is the executable acceptance corpus for the structural
content compiler.  The concrete round-trip cases are added alongside the
compiler implementation below; these public-interface checks deliberately
make the initial target RED.
-/

#check CompiledPrimitiveStep
#check PrimitiveProgram
#check runPrimitiveProgram
#check compileRelationJoin
#check compileRelationSever
#check runPrimitiveProgram_sound
#check compiled_join_redundant
#check compiled_sever_redundant
#check CompiledRelationJoin.transportBoundary
#check CompiledRelationJoin.transportBoundary_get
#check CompiledRelationSever.transportBoundary
#check CompiledRelationSever.transportBoundary_get

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

/-! One unary ambient-atom join, used as the first executable compiler probe. -/

private def unaryAmbientRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 [.iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota]
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem unaryAmbientRaw_wellFormed :
    unaryAmbientRaw.WellFormed [] := by
  constructor <;> native_decide

private def unaryAmbient : CheckedOpenDiagram [] :=
  ⟨unaryAmbientRaw, unaryAmbientRaw_wellFormed⟩

private def unaryJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }

private theorem unaryJoinSourceRaw_wellFormed :
    unaryJoinSourceRaw.WellFormed [] := by
  native_decide

private def unaryJoinSource : CheckedDiagram [] :=
  ⟨unaryJoinSourceRaw, unaryJoinSourceRaw_wellFormed⟩

private def unaryJoinInput :
    MonolithicRelationJoinInput unaryJoinSource where
  orientation := .forward
  wire := idx 0
  content := unaryAmbient
  parameters := [idx 2]

example :
    (compileRelationJoin unaryJoinSource unaryJoinInput).isOk = true := by
  native_decide

example :
    (compileRelationJoin unaryJoinSource unaryJoinInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.wireJoin] := by
  native_decide

/-! The flipped orientation compiles the same join at positive polarity. -/

private def backwardJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }

private theorem backwardJoinSourceRaw_wellFormed :
    backwardJoinSourceRaw.WellFormed [] := by
  native_decide

private def backwardJoinSource : CheckedDiagram [] :=
  ⟨backwardJoinSourceRaw, backwardJoinSourceRaw_wellFormed⟩

private def backwardJoinInput :
    MonolithicRelationJoinInput backwardJoinSource where
  orientation := .backward
  wire := idx 0
  content := unaryAmbient
  parameters := [idx 2]

example :
    (compileRelationJoin backwardJoinSource backwardJoinInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.wireJoin] := by
  native_decide

/-! The same unary atom abstracted and reconstructed through a reversed plan. -/

private def unarySeverSourceRaw : ConcreteDiagram 0 :=
  unaryAmbientRaw.diagram

private theorem unarySeverSourceRaw_wellFormed :
    unarySeverSourceRaw.WellFormed [] :=
  unaryAmbientRaw_wellFormed.1

private def unarySeverSource : CheckedDiagram [] :=
  ⟨unarySeverSourceRaw, unarySeverSourceRaw_wellFormed⟩

private def unaryOccurrenceInput :
    OccurrenceInput unaryAmbient unarySeverSource where
  region := idx 0
  regionMap := fun _ => idx 0
  nodeMap := fun _ => idx 0
  wireMap
    | ⟨0, _⟩ => idx 0
    | ⟨1, _⟩ => idx 1

private def unaryOccurrence :
    Occurrence unaryAmbient unarySeverSource :=
  (checkOccurrence unaryOccurrenceInput).toOption.get (by native_decide)

private def unaryContentOccurrence :
    ContentOccurrence unarySeverSource unaryAmbient where
  selection := unaryOccurrence.toSelection
  occurrence := unaryOccurrence
  formals := [idx 0]

private def unarySeverInput :
    MonolithicRelationSeverInput unarySeverSource where
  orientation := .forward
  scope := idx 0
  pattern := unaryAmbient
  occurrences := [unaryContentOccurrence]

example :
    (compileRelationSever unarySeverSource unarySeverInput).isOk = true := by
  native_decide

/-! Empty content exercises uniform end deletion followed by vacuous removal. -/

private def emptyUnaryRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 0
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := Fin.elim0
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [] } }
  boundary := [0]

private theorem emptyUnaryRaw_wellFormed :
    emptyUnaryRaw.WellFormed [] := by
  constructor <;> native_decide

private def emptyUnary : CheckedOpenDiagram [] :=
  ⟨emptyUnaryRaw, emptyUnaryRaw_wellFormed⟩

private def emptyJoinInput :
    MonolithicRelationJoinInput unaryJoinSource where
  orientation := .forward
  wire := idx 0
  content := emptyUnary
  parameters := []

example :
    (compileRelationJoin unaryJoinSource emptyJoinInput).isOk = true := by
  native_decide

example :
    (compileRelationJoin unaryJoinSource emptyJoinInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.endsDelete, .vacuousElim] := by
  native_decide

private def backwardEmptyInput :
    MonolithicRelationJoinInput backwardJoinSource where
  orientation := .backward
  wire := idx 0
  content := emptyUnary
  parameters := []

example :
    (compileRelationJoin backwardJoinSource backwardEmptyInput).isOk =
      true := by
  native_decide

/-!
Repeated formals are preserved in the ordered content boundary and compiled
by duplicating the corresponding live argument before the ambient merge.
-/

private def repeatedFormalRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 [.iota, .iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩, ⟨0, .arg 1⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota, .iota]
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem repeatedFormalRaw_wellFormed :
    repeatedFormalRaw.WellFormed [] := by
  constructor <;> native_decide

private def repeatedFormal : CheckedOpenDiagram [] :=
  ⟨repeatedFormalRaw, repeatedFormalRaw_wellFormed⟩

private def repeatedJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 0
          endpoints := [] }

private theorem repeatedJoinSourceRaw_wellFormed :
    repeatedJoinSourceRaw.WellFormed [] := by
  native_decide

private def repeatedJoinSource : CheckedDiagram [] :=
  ⟨repeatedJoinSourceRaw, repeatedJoinSourceRaw_wellFormed⟩

private def repeatedFormalInput :
    MonolithicRelationJoinInput repeatedJoinSource where
  orientation := .forward
  wire := idx 0
  content := repeatedFormal
  parameters := [idx 2]

example :
    (compileRelationJoin repeatedJoinSource repeatedFormalInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.argDuplicate, .wireJoin] := by
  native_decide

/-!
An unused formal is dropped before a nullary ambient application.  This
simultaneously checks nullary relation content and ordered-formal deletion.
-/

private def droppedFormalRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 []
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [] }
        | ⟨1, _⟩ =>
            { sig := .rel []
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem droppedFormalRaw_wellFormed :
    droppedFormalRaw.WellFormed [] := by
  constructor <;> native_decide

private def droppedFormal : CheckedOpenDiagram [] :=
  ⟨droppedFormalRaw, droppedFormalRaw_wellFormed⟩

private def nullaryJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [] }

private theorem nullaryJoinSourceRaw_wellFormed :
    nullaryJoinSourceRaw.WellFormed [] := by
  native_decide

private def nullaryJoinSource : CheckedDiagram [] :=
  ⟨nullaryJoinSourceRaw, nullaryJoinSourceRaw_wellFormed⟩

private def droppedFormalInput :
    MonolithicRelationJoinInput nullaryJoinSource where
  orientation := .forward
  wire := idx 0
  content := droppedFormal
  parameters := [idx 2]

example :
    (compileRelationJoin nullaryJoinSource droppedFormalInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.argDrop, .wireJoin] := by
  native_decide

/-!
Ambient argument stubs are materialized uniformly at every live endpoint.
The head and argument parameters occupy distinct ordered boundary positions.
-/

private def uniformParameterRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 [.iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota]
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem uniformParameterRaw_wellFormed :
    uniformParameterRaw.WellFormed [] := by
  constructor <;> native_decide

private def uniformParameter : CheckedOpenDiagram [] :=
  ⟨uniformParameterRaw, uniformParameterRaw_wellFormed⟩

private def uniformParameterSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 []
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }

private theorem uniformParameterSourceRaw_wellFormed :
    uniformParameterSourceRaw.WellFormed [] := by
  native_decide

private def uniformParameterSource : CheckedDiagram [] :=
  ⟨uniformParameterSourceRaw, uniformParameterSourceRaw_wellFormed⟩

private def uniformParameterInput :
    MonolithicRelationJoinInput uniformParameterSource where
  orientation := .forward
  wire := idx 0
  content := uniformParameter
  parameters := [idx 1, idx 2]

example :
    (compileRelationJoin uniformParameterSource uniformParameterInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.argExtend, .wireJoin] := by
  native_decide

/-!
Identity ports deliberately oppose the boundary order, forcing a permutation
before the checked identity leaf is emitted.
-/

private def permutedIdentityRaw : OpenConcreteDiagram 0 where
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
              endpoints := [⟨0, .identity 1⟩] }
        | ⟨1, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .identity 0⟩] } }
  boundary := [0, 1]

private theorem permutedIdentityRaw_wellFormed :
    permutedIdentityRaw.WellFormed [] := by
  constructor <;> native_decide

private def permutedIdentity : CheckedOpenDiagram [] :=
  ⟨permutedIdentityRaw, permutedIdentityRaw_wellFormed⟩

private def binaryJoinSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota, .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 1⟩] }

private theorem binaryJoinSourceRaw_wellFormed :
    binaryJoinSourceRaw.WellFormed [] := by
  native_decide

private def binaryJoinSource : CheckedDiagram [] :=
  ⟨binaryJoinSourceRaw, binaryJoinSourceRaw_wellFormed⟩

private def permutedIdentityInput :
    MonolithicRelationJoinInput binaryJoinSource where
  orientation := .forward
  wire := idx 0
  content := permutedIdentity
  parameters := []

example :
    (compileRelationJoin binaryJoinSource permutedIdentityInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.argPermute, .identityLeaf] := by
  native_decide

/-! A relation-valued formal head is compiled through `applyFormal`. -/

private def formalApplicationRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 2
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .atom 0 [.iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota]
              scope := 0
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 1]

private theorem formalApplicationRaw_wellFormed :
    formalApplicationRaw.WellFormed [] := by
  constructor <;> native_decide

private def formalApplication : CheckedOpenDiagram [] :=
  ⟨formalApplicationRaw, formalApplicationRaw_wellFormed⟩

private def higherOrderSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota, .rel [.iota]]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .rel [.iota]]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .arg 1⟩] }

private theorem higherOrderSourceRaw_wellFormed :
    higherOrderSourceRaw.WellFormed [] := by
  native_decide

private def higherOrderSource : CheckedDiagram [] :=
  ⟨higherOrderSourceRaw, higherOrderSourceRaw_wellFormed⟩

private def formalApplicationInput :
    MonolithicRelationJoinInput higherOrderSource where
  orientation := .forward
  wire := idx 0
  content := formalApplication
  parameters := []

example :
    (compileRelationJoin higherOrderSource formalApplicationInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.argPermute, .applyFormal] := by
  native_decide

/-!
Worked `∃y.(P(x,y) ∧ ¬Q(y))`: one root binder, a parallel root
decomposition, one nested cut, and two ambient relation parameters.
-/

private def workedContentRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 2
      nodeCount := 2
      wireCount := 4
      root := 0
      regions
        | ⟨0, _⟩ => .sheet
        | ⟨1, _⟩ => .cut 0
      nodes
        | ⟨0, _⟩ => .atom 0 [.iota, .iota]
        | ⟨1, _⟩ => .atom 1 [.iota]
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 0⟩] }
        | ⟨1, _⟩ =>
            { sig := .rel [.iota, .iota]
              scope := 0
              endpoints := [⟨0, .head⟩] }
        | ⟨2, _⟩ =>
            { sig := .rel [.iota]
              scope := 0
              endpoints := [⟨1, .head⟩] }
        | ⟨3, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [⟨0, .arg 1⟩, ⟨1, .arg 0⟩] } }
  boundary := [0, 1, 2]

private theorem workedContentRaw_wellFormed :
    workedContentRaw.WellFormed [] := by
  constructor <;> native_decide

private def workedContent : CheckedOpenDiagram [] :=
  ⟨workedContentRaw, workedContentRaw_wellFormed⟩

private def workedSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 0
          endpoints := [] }
    | ⟨3, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }

private theorem workedSourceRaw_wellFormed :
    workedSourceRaw.WellFormed [] := by
  native_decide

private def workedSource : CheckedDiagram [] :=
  ⟨workedSourceRaw, workedSourceRaw_wellFormed⟩

private def workedJoinInput :
    MonolithicRelationJoinInput workedSource where
  orientation := .forward
  wire := idx 0
  content := workedContent
  parameters := [idx 2, idx 3]

example :
    (compileRelationJoin workedSource workedJoinInput).isOk = true := by
  native_decide

example :
    (compileRelationJoin workedSource workedJoinInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some
        [.arityShift, .parallelSplit, .wireJoin, .cutWrap, .argDrop,
          .wireJoin] := by
  native_decide

/-!
Folded references remain folded through compilation.  The definition
signature is part of the checked diagram index, while the compiler emits only
the ordinary `refLeaf` primitive.
-/

private def foldedRefContentRaw : OpenConcreteDiagram 1 where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun _ => .ref 0 0 [.iota]
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] } }
  boundary := [0]

private theorem foldedRefContentRaw_wellFormed :
    foldedRefContentRaw.WellFormed [[.iota]] := by
  constructor <;> native_decide

private def foldedRefContent : CheckedOpenDiagram [[.iota]] :=
  ⟨foldedRefContentRaw, foldedRefContentRaw_wellFormed⟩

private def foldedRefSourceRaw : ConcreteDiagram 1 where
  regionCount := 2
  nodeCount := 1
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }

private theorem foldedRefSourceRaw_wellFormed :
    foldedRefSourceRaw.WellFormed [[.iota]] := by
  native_decide

private def foldedRefSource : CheckedDiagram [[.iota]] :=
  ⟨foldedRefSourceRaw, foldedRefSourceRaw_wellFormed⟩

private def foldedRefInput :
    MonolithicRelationJoinInput foldedRefSource where
  orientation := .forward
  wire := idx 0
  content := foldedRefContent
  parameters := []

example :
    (compileRelationJoin foldedRefSource foldedRefInput).toOption.map
        (fun compiled => compiled.program.tags) =
      some [.refLeaf] := by
  native_decide

/-!
Two severed sites share one uniform ambient head but carry distinct formal
attachments.  Reversing the join plan therefore covers both the uniform
parameter and per-site argument vectors.
-/

private def twoSiteSourceRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .arg 0⟩] }

private theorem twoSiteSourceRaw_wellFormed :
    twoSiteSourceRaw.WellFormed [] := by
  native_decide

private def twoSiteSource : CheckedDiagram [] :=
  ⟨twoSiteSourceRaw, twoSiteSourceRaw_wellFormed⟩

private def firstSiteInput : OccurrenceInput unaryAmbient twoSiteSource where
  region := idx 0
  regionMap := fun _ => idx 0
  nodeMap := fun _ => idx 0
  wireMap
    | ⟨0, _⟩ => idx 1
    | ⟨1, _⟩ => idx 0

private def firstSite : Occurrence unaryAmbient twoSiteSource :=
  (checkOccurrence firstSiteInput).toOption.get (by native_decide)

private def secondSiteInput : OccurrenceInput unaryAmbient twoSiteSource where
  region := idx 0
  regionMap := fun _ => idx 0
  nodeMap := fun _ => idx 1
  wireMap
    | ⟨0, _⟩ => idx 2
    | ⟨1, _⟩ => idx 0

private def secondSite : Occurrence unaryAmbient twoSiteSource :=
  (checkOccurrence secondSiteInput).toOption.get (by native_decide)

private def firstContentSite :
    ContentOccurrence twoSiteSource unaryAmbient where
  selection := firstSite.toSelection
  occurrence := firstSite
  formals := [idx 1]

private def secondContentSite :
    ContentOccurrence twoSiteSource unaryAmbient where
  selection := secondSite.toSelection
  occurrence := secondSite
  formals := [idx 2]

private def twoSiteSeverInput :
    MonolithicRelationSeverInput twoSiteSource where
  orientation := .forward
  scope := idx 0
  pattern := unaryAmbient
  occurrences := [firstContentSite, secondContentSite]

example :
    (compileRelationSever twoSiteSource twoSiteSeverInput).isOk = true := by
  native_decide

end CompilerFixtures

end WirePrimitive

end VisualProof
