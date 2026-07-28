import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof.ConcreteExamples

open VisualProof

def nullaryRelationAtom : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 []
  wires := fun _ =>
    { sig := .rel []
      scope := 0
      endpoints := [⟨0, .head⟩] }

def higherOrderArgumentAtom : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.rel []]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.rel []]
          scope := 0
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }

def threePortIdentity : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 3
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 2⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }

def permutedThreePortIdentity : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 3
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 2⟩] }

/--
Two three-port identity nodes share three distinct wires. The companion fixture
below changes every identity storage index and reverses every wire's endpoint
list, while preserving the same unordered incidence.
-/
def identityOrderOriginal : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 3
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 2⟩, ⟨1, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩, ⟨1, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩, ⟨1, .identity 2⟩] }

def identityOrderPermuted : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 3
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 2⟩, ⟨0, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 0⟩, ⟨0, .identity 1⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 1⟩, ⟨0, .identity 2⟩] }

def repeatedBoundaryAlias : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 1
      nodeCount := 0
      wireCount := 1
      root := 0
      regions := fun _ => .sheet
      nodes := fun node => Fin.elim0 node
      wires := fun _ =>
        { sig := .iota
          scope := 0
          endpoints := [] } }
  boundary := [0, 0]

def mixedSignatureIdentity : ConcreteDiagram 0 where
  regionCount := 1
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
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }

def scopeViolation : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 1
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 0 []
  wires := fun _ =>
    { sig := .rel []
      scope := 1
      endpoints := [⟨0, .head⟩] }

def checkError {definitions : List (List Sig)} :
    Except WFError (CheckedDiagram definitions) → Option WFError
  | .error error => some error
  | .ok _ => none

example :
    checkError (checkWellFormed [] mixedSignatureIdentity) =
      some (.identitySignatureMismatch 0 1) := by
  native_decide

example :
    checkError (checkWellFormed [] scopeViolation) =
      some (.wireScopeDoesNotEnclose 0 0 .head) := by
  native_decide

def checkAccepted {definitions : List (List Sig)} :
    Except WFError (CheckedDiagram definitions) → Bool
  | .error _ => false
  | .ok _ => true

example : checkAccepted (checkWellFormed [] nullaryRelationAtom) = true := by
  native_decide

example : checkAccepted (checkWellFormed [] higherOrderArgumentAtom) = true := by
  native_decide

example : checkAccepted (checkWellFormed [] threePortIdentity) = true := by
  native_decide

theorem nullaryRelationAtom_wellFormed :
    nullaryRelationAtom.WellFormed [] := by
  native_decide

theorem higherOrderArgumentAtom_wellFormed :
    higherOrderArgumentAtom.WellFormed [] := by
  native_decide

theorem threePortIdentity_wellFormed :
    threePortIdentity.WellFormed [] := by
  native_decide

theorem permutedThreePortIdentity_wellFormed :
    permutedThreePortIdentity.WellFormed [] := by
  native_decide

theorem identityOrderOriginal_wellFormed :
    identityOrderOriginal.WellFormed [] := by
  native_decide

theorem identityOrderPermuted_wellFormed :
    identityOrderPermuted.WellFormed [] := by
  native_decide

def nullaryRelationAtom_checked : CheckedDiagram [] :=
  ⟨nullaryRelationAtom, nullaryRelationAtom_wellFormed⟩

def higherOrderArgumentAtom_checked : CheckedDiagram [] :=
  ⟨higherOrderArgumentAtom, higherOrderArgumentAtom_wellFormed⟩

def threePortIdentity_checked : CheckedDiagram [] :=
  ⟨threePortIdentity, threePortIdentity_wellFormed⟩

def permutedThreePortIdentity_checked : CheckedDiagram [] :=
  ⟨permutedThreePortIdentity, permutedThreePortIdentity_wellFormed⟩

def identityOrderOriginal_checked : CheckedDiagram [] :=
  ⟨identityOrderOriginal, identityOrderOriginal_wellFormed⟩

def identityOrderPermuted_checked : CheckedDiagram [] :=
  ⟨identityOrderPermuted, identityOrderPermuted_wellFormed⟩

theorem repeatedBoundaryAlias_wellFormed :
    repeatedBoundaryAlias.WellFormed [] := by
  constructor <;> native_decide

def repeatedBoundaryAlias_checked : CheckedOpenDiagram [] :=
  ⟨repeatedBoundaryAlias, repeatedBoundaryAlias_wellFormed⟩

private def boundaryClasses (openDiagram : OpenConcreteDiagram definitionCount) :
    List openDiagram.diagram.WireId :=
  ConcreteElaboration.openBoundaryWires openDiagram

private def boundarySignatures
    (openDiagram : OpenConcreteDiagram definitionCount) : List Sig :=
  openDiagram.boundary.map fun wire =>
    (openDiagram.diagram.wires wire).sig

private def boundaryClassSignatures
    (openDiagram : OpenConcreteDiagram definitionCount) : List Sig :=
  ConcreteElaboration.openBoundaryClassSigs openDiagram

private def resolveBoundaryWireIn?
    (diagram : ConcreteDiagram definitionCount) :
    (classes : List diagram.WireId) → (wire : diagram.WireId) →
      Option (Var (classes.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig)
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveBoundaryWireIn? diagram tail wire).map .there

private def compileBoundary?
    (openDiagram : OpenConcreteDiagram definitionCount) :
    (boundary : List openDiagram.diagram.WireId) →
      Option (Vars (boundaryClassSignatures openDiagram)
        (boundary.map fun wire => (openDiagram.diagram.wires wire).sig))
  | [] => some .nil
  | wire :: tail => do
      let head ← resolveBoundaryWireIn? openDiagram.diagram
        (boundaryClasses openDiagram) wire
      let rest ← compileBoundary? openDiagram tail
      pure (.cons head rest)

/--
The repeated-boundary fixture is obtained from the checked raw open graph:
its ordered boundary is resolved against deduplicated concrete wire classes,
and its root is compiled with those classes already visible, excluding the
open wire from the root-local binder block. No intrinsic boundary or body is
substituted by hand.
-/
def repeatedBoundaryAlias_elaborated : OpenDiagram [] [.iota, .iota] where
  classes := boundaryClassSignatures repeatedBoundaryAlias
  boundary := (compileBoundary? repeatedBoundaryAlias
    repeatedBoundaryAlias.boundary).get (by native_decide)
  boundary_surjective := by
    intro sig fiber
    cases fiber with
    | here =>
        change (⟨.iota, .here⟩ : PackedVar [.iota]) ∈
          [⟨.iota, .here⟩, ⟨.iota, .here⟩]
        simp
    | there impossible => exact nomatch impossible
  body := (ConcreteElaboration.compileOpenRoot? []
    repeatedBoundaryAlias).get (by native_decide)

example : repeatedBoundaryAlias.boundary.length = 2 := by
  native_decide

example : repeatedBoundaryAlias.boundary[0]? = repeatedBoundaryAlias.boundary[1]? := by
  native_decide

example :
    repeatedBoundaryAlias_elaborated.boundaryAliases 0 1 := by
  exact ⟨.iota, .here, rfl, rfl⟩

example :
    ConcreteElaboration.openRootLocalWires repeatedBoundaryAlias = [] := by
  native_decide

example :
    ConcreteElaboration.compileOpenRoot? [] repeatedBoundaryAlias =
      some blank := by
  rfl

theorem repeatedBoundaryAlias_denotation
    (pre : PreModel) (definitionEnv : DefinitionEnv pre [])
    (left right : pre.Domain .iota) :
    denoteOpen pre definitionEnv repeatedBoundaryAlias_elaborated
      (left, (right, PUnit.unit)) ↔ left = right := by
  constructor
  · rintro ⟨env, boundaryValues, _⟩
    exact (congrArg Prod.fst boundaryValues).symm.trans
      (congrArg (fun values => values.2.1) boundaryValues)
  · intro equality
    subst right
    let env : Env pre [.iota] :=
      fun _ wireVar =>
        match wireVar with
        | .here => left
        | .there impossible => nomatch impossible
    refine ⟨env, rfl, ?_⟩
    rw [show repeatedBoundaryAlias_elaborated.body =
      blank by rfl]
    trivial

def nullaryRelationAtom_expected : Region [] [] :=
  .mk (.cons
    (.bind (.rel [])
      (.mk (.cons (.atom .here .nil) .nil)))
    .nil)

def higherOrderArgumentAtom_expected : Region [] [] :=
  .mk (.cons
    (.bind (.rel [])
      (.mk (.cons
        (.bind (.rel [.rel []])
          (.mk (.cons
            (.atom .here (.cons (.there .here) .nil))
            .nil)))
        .nil)))
    .nil)

def threePortIdentity_expected : Region [] [] :=
  .mk (.cons
    (.bind .iota
      (.mk (.cons
        (.bind .iota
          (.mk (.cons
            (.bind .iota
              (.mk (.cons
                (.identity .iota
                  [.there .here, .there (.there .here), .here]
                  (by decide))
                .nil)))
            .nil)))
        .nil)))
    .nil)

example :
    elaborate nullaryRelationAtom_checked =
      nullaryRelationAtom_expected := by
  rfl

example :
    elaborate higherOrderArgumentAtom_checked =
      higherOrderArgumentAtom_expected := by
  rfl

example :
    elaborate threePortIdentity_checked =
      threePortIdentity_expected := by
  rfl

theorem nullaryRelationAtom_denotation
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv nullaryRelationAtom_checked ↔
      ∃ relation : pre.Domain (.rel []),
        pre.apply relation PUnit.unit := by
  rw [elaborate_denotes_checked]
  change denoteRegion pre definitionEnv Env.empty
    (elaborate nullaryRelationAtom_checked) ↔ _
  rw [show elaborate nullaryRelationAtom_checked =
      nullaryRelationAtom_expected by rfl]
  simp [nullaryRelationAtom_expected, denoteRegion, denoteItemSeq,
    denoteItem, Vars.denote]

theorem higherOrderArgumentAtom_denotation
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv higherOrderArgumentAtom_checked ↔
      ∃ argument : pre.Domain (.rel []),
      ∃ relation : pre.Domain (.rel [.rel []]),
        pre.apply relation (argument, PUnit.unit) := by
  rw [elaborate_denotes_checked]
  change denoteRegion pre definitionEnv Env.empty
    (elaborate higherOrderArgumentAtom_checked) ↔ _
  rw [show elaborate higherOrderArgumentAtom_checked =
      higherOrderArgumentAtom_expected by rfl]
  simp [higherOrderArgumentAtom_expected, denoteRegion, denoteItemSeq,
    denoteItem, Vars.denote]

theorem threePortIdentity_denotation
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv threePortIdentity_checked ↔
      ∃ third second first : pre.Domain .iota,
        AllEqual [second, third, first] := by
  rw [elaborate_denotes_checked]
  change denoteRegion pre definitionEnv Env.empty
    (elaborate threePortIdentity_checked) ↔ _
  rw [show elaborate threePortIdentity_checked =
      threePortIdentity_expected by rfl]
  simp [threePortIdentity_expected, denoteRegion, denoteItemSeq,
    denoteItem]

def originalOrderEndpoint (node : Fin 2) (index : Nat) :
    CEndpoint identityOrderOriginal.nodeCount :=
  ⟨⟨node.val, by change node.val < 2; exact node.isLt⟩,
    .identity index⟩

def permutedOrderEndpoint (node : Fin 2) (index : Nat) :
    CEndpoint identityOrderPermuted.nodeCount :=
  ⟨⟨node.val, by change node.val < 2; exact node.isLt⟩,
    .identity index⟩

def identityIncidenceIso :
    ConcreteIso (definitions := [])
      identityOrderOriginal identityOrderPermuted where
  regions := Data.Finite.FiniteEquiv.refl _
  nodes := Data.Finite.FiniteEquiv.refl _
  wires := Data.Finite.FiniteEquiv.refl _
  root := rfl
  region_table := by
    intro region
    rfl
  node_table := by
    intro node
    rfl
  wire_signature := by
    rintro ⟨(_ | _ | _ | n), bound⟩
    · rfl
    · rfl
    · rfl
    · simp [identityOrderOriginal] at bound
      omega
  wire_scope := by
    rintro ⟨(_ | _ | _ | n), bound⟩
    · rfl
    · rfl
    · rfl
    · simp [identityOrderOriginal] at bound
      omega
  endpoint_forward := by
    rintro ⟨(_ | _ | _ | n), bound⟩ endpoint member
    · change endpoint ∈
        [originalOrderEndpoint 0 2, originalOrderEndpoint 1 0] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨permutedOrderEndpoint 0 0, ?_, ?_⟩
        · change permutedOrderEndpoint 0 0 ∈
            [permutedOrderEndpoint 1 2, permutedOrderEndpoint 0 0]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨permutedOrderEndpoint 1 2, ?_, ?_⟩
        · change permutedOrderEndpoint 1 2 ∈
            [permutedOrderEndpoint 1 2, permutedOrderEndpoint 0 0]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · change endpoint ∈
        [originalOrderEndpoint 0 0, originalOrderEndpoint 1 1] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨permutedOrderEndpoint 0 1, ?_, ?_⟩
        · change permutedOrderEndpoint 0 1 ∈
            [permutedOrderEndpoint 1 0, permutedOrderEndpoint 0 1]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨permutedOrderEndpoint 1 0, ?_, ?_⟩
        · change permutedOrderEndpoint 1 0 ∈
            [permutedOrderEndpoint 1 0, permutedOrderEndpoint 0 1]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · change endpoint ∈
        [originalOrderEndpoint 0 1, originalOrderEndpoint 1 2] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨permutedOrderEndpoint 0 2, ?_, ?_⟩
        · change permutedOrderEndpoint 0 2 ∈
            [permutedOrderEndpoint 1 1, permutedOrderEndpoint 0 2]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨permutedOrderEndpoint 1 1, ?_, ?_⟩
        · change permutedOrderEndpoint 1 1 ∈
            [permutedOrderEndpoint 1 1, permutedOrderEndpoint 0 2]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · simp [identityOrderOriginal] at bound
      omega
  endpoint_backward := by
    rintro ⟨(_ | _ | _ | n), bound⟩ endpoint member
    · change endpoint ∈
        [permutedOrderEndpoint 1 2, permutedOrderEndpoint 0 0] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨originalOrderEndpoint 1 0, ?_, ?_⟩
        · change originalOrderEndpoint 1 0 ∈
            [originalOrderEndpoint 0 2, originalOrderEndpoint 1 0]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨originalOrderEndpoint 0 2, ?_, ?_⟩
        · change originalOrderEndpoint 0 2 ∈
            [originalOrderEndpoint 0 2, originalOrderEndpoint 1 0]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · change endpoint ∈
        [permutedOrderEndpoint 1 0, permutedOrderEndpoint 0 1] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨originalOrderEndpoint 1 1, ?_, ?_⟩
        · change originalOrderEndpoint 1 1 ∈
            [originalOrderEndpoint 0 0, originalOrderEndpoint 1 1]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨originalOrderEndpoint 0 0, ?_, ?_⟩
        · change originalOrderEndpoint 0 0 ∈
            [originalOrderEndpoint 0 0, originalOrderEndpoint 1 1]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · change endpoint ∈
        [permutedOrderEndpoint 1 1, permutedOrderEndpoint 0 2] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with member | member <;> subst endpoint
      · refine ⟨originalOrderEndpoint 1 2, ?_, ?_⟩
        · change originalOrderEndpoint 1 2 ∈
            [originalOrderEndpoint 0 1, originalOrderEndpoint 1 2]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
      · refine ⟨originalOrderEndpoint 0 1, ?_, ?_⟩
        · change originalOrderEndpoint 0 1 ∈
            [originalOrderEndpoint 0 1, originalOrderEndpoint 1 2]
          simp
        simp [identityOrderOriginal, identityOrderPermuted,
          PortCorresponds, originalOrderEndpoint, permutedOrderEndpoint]
    · simp [identityOrderOriginal] at bound
      omega

theorem identityIncidencePermutation_denotation
    (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv identityOrderOriginal_checked =
      denoteChecked pre definitionEnv identityOrderPermuted_checked := by
  apply propext
  exact iso_denotation identityIncidenceIso pre definitionEnv

end VisualProof.ConcreteExamples
