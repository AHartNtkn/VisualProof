import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Rule.IdentityRetargetSemantics

namespace VisualProof

namespace IdentityFixtures

open ConcreteExamples
open ConcreteDiagram

def repeatedIncidence : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints :=
        [⟨0, .identity 1⟩, ⟨0, .identity 0⟩] }

theorem repeatedIncidence_wellFormed :
    repeatedIncidence.WellFormed [] := by
  native_decide

def repeatedIncidence_checked : CheckedDiagram [] :=
  ⟨repeatedIncidence, repeatedIncidence_wellFormed⟩

private theorem repeatedRegion_unique
    (region : repeatedIncidence_checked.val.RegionId) :
    region = ⟨0, by native_decide⟩ := by
  apply Fin.ext
  change region.val = 0
  have bound := region.isLt
  change region.val < 1 at bound
  omega

private theorem repeatedNode_unique
    (node : repeatedIncidence_checked.val.NodeId) :
    node = ⟨0, by native_decide⟩ := by
  apply Fin.ext
  change node.val = 0
  have bound := node.isLt
  change node.val < 1 at bound
  omega

private theorem repeatedWire_unique
    (wire : repeatedIncidence_checked.val.WireId) :
    wire = ⟨0, by native_decide⟩ := by
  apply Fin.ext
  change wire.val = 0
  have bound := wire.isLt
  change wire.val < 1 at bound
  omega

def negativeCoScoped : ConcreteDiagram 0 where
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
          scope := 1
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .identity 0⟩] }

theorem negativeCoScoped_wellFormed :
    negativeCoScoped.WellFormed [] := by
  native_decide

def negativeCoScoped_checked : CheckedDiagram [] :=
  ⟨negativeCoScoped, negativeCoScoped_wellFormed⟩

def sameRegionFusion : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .identity 1 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨1, .identity 1⟩, ⟨0, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨1, .identity 0⟩] }

theorem sameRegionFusion_wellFormed :
    sameRegionFusion.WellFormed [] := by
  native_decide

def sameRegionFusion_checked : CheckedDiagram [] :=
  ⟨sameRegionFusion, sameRegionFusion_wellFormed⟩

def arityOneFusion : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 2
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 .iota 2
  wires := fun _ =>
    { sig := .iota
      scope := 0
      endpoints :=
        [⟨0, .identity 0⟩, ⟨0, .identity 1⟩,
          ⟨1, .identity 0⟩, ⟨1, .identity 1⟩] }

theorem arityOneFusion_wellFormed :
    arityOneFusion.WellFormed [] := by
  native_decide

def arityOneFusion_checked : CheckedDiagram [] :=
  ⟨arityOneFusion, arityOneFusion_wellFormed⟩

def relationCoScoped : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .identity 0 (.rel []) 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }

theorem relationCoScoped_wellFormed :
    relationCoScoped.WellFormed [] := by
  native_decide

def relationCoScoped_checked : CheckedDiagram [] :=
  ⟨relationCoScoped, relationCoScoped_wellFormed⟩

/-- The normalizer must delete a repeated one-wire identity as reflexive truth. -/
example :
    (normalizeIdentities repeatedIncidence_checked).target.val.nodeCount = 0 := by
  native_decide

/-- Co-scoped collapse is eager in a positive sheet. -/
example :
    (normalizeIdentities threePortIdentity_checked).target.val.wireCount = 1 := by
  native_decide

/-- The same one-point collapse is eager below one cut. -/
example :
    (normalizeIdentities negativeCoScoped_checked).target.val.wireCount = 1 := by
  native_decide

/-- Same-region identities fuse by unordered distinct-wire union. -/
example :
    let normalized := normalizeIdentities sameRegionFusion_checked
    normalized.target.val.nodeCount = 1 ∧
      normalized.target.val.wireCount = 3 := by
  native_decide

/-- Direct Rule 3 refuses a union that would violate identity arity. -/
example :
    (fuseSameRegion arityOneFusion_checked
      ⟨0, by native_decide⟩ ⟨1, by native_decide⟩).isSome = false := by
  native_decide

/-- Relation-sorted identities are ordinary grammatical identities. -/
example :
    (normalizeIdentities relationCoScoped_checked).target.val.wireCount = 1 := by
  native_decide

/-- Identity storage indices and endpoint order are semantically irrelevant. -/
example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv identityOrderOriginal_checked =
      denoteChecked pre definitionEnv identityOrderPermuted_checked :=
  identityIncidencePermutation_denotation pre definitionEnv

def retargetHost : ConcreteDiagram 0 where
  regionCount := 4
  nodeCount := 3
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
    | ⟨3, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .identity 1 .iota 2
    | ⟨1, _⟩ => .identity 2 .iota 2
    | ⟨2, _⟩ => .identity 3 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 1⟩,
              ⟨1, .identity 0⟩, ⟨1, .identity 1⟩,
              ⟨2, .identity 0⟩, ⟨2, .identity 1⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }

theorem retargetHost_wellFormed :
    retargetHost.WellFormed [] := by
  native_decide

def retargetHost_checked : CheckedDiagram [] :=
  ⟨retargetHost, retargetHost_wellFormed⟩

def retargetBoundary : List retargetHost_checked.val.WireId :=
  [⟨0, by native_decide⟩]

def deiterationBoundary : List retargetHost_checked.val.WireId :=
  [⟨1, by native_decide⟩]

def retargetInput : IdentityRetargetInput retargetHost_checked where
  boundary := 0
  identity := ⟨0, by native_decide⟩
  sourceWire := ⟨0, by native_decide⟩
  targetWire := ⟨1, by native_decide⟩

def nestedSite : retargetHost_checked.val.RegionId :=
  ⟨2, by native_decide⟩

def siblingSite : retargetHost_checked.val.RegionId :=
  ⟨3, by native_decide⟩

/-- Iteration validates the stable source-to-target evidence at its source. -/
example :
    (checkIdentityRetarget retargetHost_checked nestedSite .iteration
      retargetBoundary retargetInput).isSome = true := by
  native_decide

/-- Deiteration reuses the same oriented evidence at its target. -/
example :
    (checkIdentityRetarget retargetHost_checked nestedSite .deiteration
      deiterationBoundary retargetInput).isSome = true := by
  native_decide

/-- Deiteration refuses an attachment still carrying the outer source. -/
example :
    (checkIdentityRetarget retargetHost_checked nestedSite .deiteration
      retargetBoundary retargetInput).isSome = false := by
  native_decide

/-- The same identity does not dominate sibling region 3. -/
example :
    (checkIdentityRetarget retargetHost_checked siblingSite .iteration
      retargetBoundary retargetInput).isSome = false := by
  native_decide

/-- A batch cannot name one boundary position twice. -/
example :
    (checkIdentityRetargets retargetHost_checked nestedSite .iteration
      retargetBoundary [retargetInput, retargetInput]).isSome = false := by
  native_decide

def nestedSelection : CheckedSelection retargetHost_checked where
  root := nestedSite
  regions := [nestedSite]
  nodes := [⟨1, by native_decide⟩]
  wires := [⟨0, by native_decide⟩]
  regions_nodup := by native_decide
  nodes_nodup := by native_decide
  wires_nodup := by native_decide
  root_mem := by native_decide
  host_root_retained := by native_decide
  root_parent_external := by native_decide
  below_root := by native_decide
  descendants_closed := by native_decide
  nodes_exact := by native_decide
  wires_exact := by native_decide

def nestedCrossingZero : CheckedSelection.BoundaryCrossing nestedSelection :=
  ⟨(⟨0, by native_decide⟩,
      ⟨⟨1, by native_decide⟩, .identity 0⟩), by native_decide⟩

def nestedCrossingOne : CheckedSelection.BoundaryCrossing nestedSelection :=
  ⟨(⟨0, by native_decide⟩,
      ⟨⟨1, by native_decide⟩, .identity 1⟩), by native_decide⟩

def nestedOccurrence :
    Occurrence repeatedIncidence_checked retargetHost_checked where
  selection := nestedSelection
  regionMap := fun _ => nestedSite
  nodeMap := fun _ => ⟨1, by native_decide⟩
  wireMap := fun _ => ⟨0, by native_decide⟩
  regionInverse := fun _ _ => ⟨0, by native_decide⟩
  nodeInverse := fun _ _ => ⟨0, by native_decide⟩
  wireInverse := fun _ _ => ⟨0, by native_decide⟩
  region_injective := by
    intro left right _
    exact (repeatedRegion_unique left).trans
      (repeatedRegion_unique right).symm
  node_injective := by
    intro left right _
    exact (repeatedNode_unique left).trans
      (repeatedNode_unique right).symm
  wire_injective := by
    intro left right _
    exact (repeatedWire_unique left).trans
      (repeatedWire_unique right).symm
  root := by native_decide
  region_mem := by native_decide
  region_exact := by native_decide
  parentage := by native_decide
  node_corresponds := by
    intro node
    rw [repeatedNode_unique node]
    rfl
  node_mem := by native_decide
  node_exact := by native_decide
  wire_signature := by native_decide
  wire_mem := by native_decide
  wire_exact := by native_decide
  region_left_inverse := by native_decide
  node_left_inverse := by native_decide
  wire_left_inverse := by native_decide
  region_right_inverse := by native_decide
  node_right_inverse := by native_decide
  wire_right_inverse := by native_decide
  boundary := [nestedCrossingZero, nestedCrossingOne]
  boundary_nodup := by native_decide
  boundary_complete := by
    rintro ⟨⟨wire, endpoint⟩, crossing⟩
    have wireEquality : wire = (⟨0, by native_decide⟩ :
        retargetHost_checked.val.WireId) := by
      simpa [nestedSelection] using crossing.1
    subst wire
    have nodeEquality :
        endpoint.node = (⟨1, by native_decide⟩ :
          retargetHost_checked.val.NodeId) := by
      simpa [nestedSelection] using crossing.2.2.1
    have incident := crossing.2.1
    rcases endpoint with ⟨node, port⟩
    change node = (⟨1, by native_decide⟩ :
      retargetHost_checked.val.NodeId) at nodeEquality
    subst node
    change
      (⟨⟨1, by native_decide⟩, port⟩ :
          CEndpoint retargetHost_checked.val.nodeCount) ∈
        [⟨⟨0, by native_decide⟩, .identity 1⟩,
          ⟨⟨1, by native_decide⟩, .identity 0⟩,
          ⟨⟨1, by native_decide⟩, .identity 1⟩,
          ⟨⟨2, by native_decide⟩, .identity 0⟩,
          ⟨⟨2, by native_decide⟩, .identity 1⟩] at incident
    simp only [List.mem_cons, List.not_mem_nil, or_false] at incident
    rcases incident with incident | incident | incident | incident | incident
    · simp at incident
    · have : port = .identity 0 :=
        congrArg CEndpoint.port incident
      subst port
      simp [nestedCrossingZero]
    · have : port = .identity 1 :=
        congrArg CEndpoint.port incident
      subst port
      simp [nestedCrossingOne]
    · simp at incident
    · simp at incident
  scope_preserved_internal := by native_decide
  positional_incidence := by
    intro node port notIdentity
    rw [repeatedNode_unique node] at notIdentity
    simp [repeatedIncidence_checked, repeatedIncidence] at notIdentity
  identity_incidence := by
    intro node region sig arity equation
    have nodeEquality := repeatedNode_unique node
    subst node
    injection equation with regionEquality sigEquality arityEquality
    subst region
    subst sig
    subst arity
    native_decide

def siblingSelection : CheckedSelection retargetHost_checked where
  root := siblingSite
  regions := [siblingSite]
  nodes := [⟨2, by native_decide⟩]
  wires := [⟨0, by native_decide⟩]
  regions_nodup := by native_decide
  nodes_nodup := by native_decide
  wires_nodup := by native_decide
  root_mem := by native_decide
  host_root_retained := by native_decide
  root_parent_external := by native_decide
  below_root := by native_decide
  descendants_closed := by native_decide
  nodes_exact := by native_decide
  wires_exact := by native_decide

def siblingCrossingZero : CheckedSelection.BoundaryCrossing siblingSelection :=
  ⟨(⟨0, by native_decide⟩,
      ⟨⟨2, by native_decide⟩, .identity 0⟩), by native_decide⟩

def siblingCrossingOne : CheckedSelection.BoundaryCrossing siblingSelection :=
  ⟨(⟨0, by native_decide⟩,
      ⟨⟨2, by native_decide⟩, .identity 1⟩), by native_decide⟩

def siblingOccurrence :
    Occurrence repeatedIncidence_checked retargetHost_checked where
  selection := siblingSelection
  regionMap := fun _ => siblingSite
  nodeMap := fun _ => ⟨2, by native_decide⟩
  wireMap := fun _ => ⟨0, by native_decide⟩
  regionInverse := fun _ _ => ⟨0, by native_decide⟩
  nodeInverse := fun _ _ => ⟨0, by native_decide⟩
  wireInverse := fun _ _ => ⟨0, by native_decide⟩
  region_injective := by
    intro left right _
    exact (repeatedRegion_unique left).trans
      (repeatedRegion_unique right).symm
  node_injective := by
    intro left right _
    exact (repeatedNode_unique left).trans
      (repeatedNode_unique right).symm
  wire_injective := by
    intro left right _
    exact (repeatedWire_unique left).trans
      (repeatedWire_unique right).symm
  root := by native_decide
  region_mem := by native_decide
  region_exact := by native_decide
  parentage := by native_decide
  node_corresponds := by
    intro node
    rw [repeatedNode_unique node]
    rfl
  node_mem := by native_decide
  node_exact := by native_decide
  wire_signature := by native_decide
  wire_mem := by native_decide
  wire_exact := by native_decide
  region_left_inverse := by native_decide
  node_left_inverse := by native_decide
  wire_left_inverse := by native_decide
  region_right_inverse := by native_decide
  node_right_inverse := by native_decide
  wire_right_inverse := by native_decide
  boundary := [siblingCrossingZero, siblingCrossingOne]
  boundary_nodup := by native_decide
  boundary_complete := by
    rintro ⟨⟨wire, endpoint⟩, crossing⟩
    have wireEquality : wire = (⟨0, by native_decide⟩ :
        retargetHost_checked.val.WireId) := by
      simpa [siblingSelection] using crossing.1
    subst wire
    have nodeEquality :
        endpoint.node = (⟨2, by native_decide⟩ :
          retargetHost_checked.val.NodeId) := by
      simpa [siblingSelection] using crossing.2.2.1
    have incident := crossing.2.1
    rcases endpoint with ⟨node, port⟩
    change node = (⟨2, by native_decide⟩ :
      retargetHost_checked.val.NodeId) at nodeEquality
    subst node
    change
      (⟨⟨2, by native_decide⟩, port⟩ :
          CEndpoint retargetHost_checked.val.nodeCount) ∈
        [⟨⟨0, by native_decide⟩, .identity 1⟩,
          ⟨⟨1, by native_decide⟩, .identity 0⟩,
          ⟨⟨1, by native_decide⟩, .identity 1⟩,
          ⟨⟨2, by native_decide⟩, .identity 0⟩,
          ⟨⟨2, by native_decide⟩, .identity 1⟩] at incident
    simp only [List.mem_cons, List.not_mem_nil, or_false] at incident
    rcases incident with incident | incident | incident | incident | incident
    · simp at incident
    · simp at incident
    · simp at incident
    · have : port = .identity 0 :=
        congrArg CEndpoint.port incident
      subst port
      simp [siblingCrossingZero]
    · have : port = .identity 1 :=
        congrArg CEndpoint.port incident
      subst port
      simp [siblingCrossingOne]
  scope_preserved_internal := by native_decide
  positional_incidence := by
    intro node port notIdentity
    rw [repeatedNode_unique node] at notIdentity
    simp [repeatedIncidence_checked, repeatedIncidence] at notIdentity
  identity_incidence := by
    intro node region sig arity equation
    have nodeEquality := repeatedNode_unique node
    subst node
    injection equation with regionEquality sigEquality arityEquality
    subst region
    subst sig
    subst arity
    native_decide

theorem nestedExtractedWellFormed :
    nestedOccurrence.extractedOpen.WellFormed [] := by
  constructor <;> native_decide

def nestedExtractedChecked : CheckedOpenDiagram [] :=
  checkedExtraction nestedOccurrence nestedExtractedWellFormed

def nestedBoundaryVars :
    Vars
      (ConcreteElaboration.openBoundaryClassSigs
        nestedOccurrence.extractedOpen)
      (checkedBoundarySigs nestedExtractedChecked) :=
  .cons .here (.cons .here .nil)

theorem nestedBoundaryVars_compiles :
    compileExtractedBoundary? nestedExtractedChecked =
      some nestedBoundaryVars := by
  rfl

theorem nestedBoundaryVars_surjective :
    ∀ sig
      (fiber : Var
        (ConcreteElaboration.openBoundaryClassSigs
          nestedOccurrence.extractedOpen) sig),
      nestedBoundaryVars.Contains fiber := by
  intro sig fiber
  cases fiber with
  | here =>
      change
        (⟨.iota, Var.here⟩ : PackedVar [.iota]) ∈
          (Vars.cons Var.here (Vars.cons Var.here Vars.nil)).entries
      simp [Vars.entries]
  | there fiber =>
      nomatch fiber

def nestedExtractedBody :
    Region []
      (ConcreteElaboration.openBoundaryClassSigs
        nestedOccurrence.extractedOpen) :=
  .mk (.cons
    (.identity .iota [.here, .here] (by decide))
    .nil)

theorem nestedExtractedBody_compiles :
    ConcreteElaboration.compileOpenRoot? []
        nestedOccurrence.extractedOpen =
      some nestedExtractedBody := by
  rfl

def nestedExtraction : ExtractionCompilation nestedOccurrence where
  wellFormed := nestedExtractedWellFormed
  boundary := nestedBoundaryVars
  boundary_compiles := nestedBoundaryVars_compiles
  boundary_surjective := nestedBoundaryVars_surjective
  body := nestedExtractedBody
  body_compiles := nestedExtractedBody_compiles

theorem nestedRemovalWellFormed :
    (Removal.diagram nestedOccurrence).WellFormed [] := by
  native_decide

def nestedRemoved : RemovalResult nestedOccurrence :=
  ⟨nestedRemovalWellFormed⟩

def nestedSourceTarget :
    Fin nestedExtraction.checked.val.boundary.length →
      nestedRemoved.complement.val.WireId :=
  fun _ =>
    Removal.wireIndex nestedOccurrence
      ⟨0, by native_decide⟩ (by native_decide)

def nestedSourceAttachment :
    ConcreteSpliceAttachment nestedRemoved nestedExtraction.checked where
  target := nestedSourceTarget
  signature := by native_decide
  scope := by native_decide
  identityRequests :=
    computedIdentityRequests nestedRemoved nestedExtraction.checked
      nestedSourceTarget
  identityRequests_nodup := Data.Finite.eraseDups_nodup _
  identityRequests_exact := rfl

def nestedRetargetInput :
    IdentityRetargetInput nestedRemoved.complement where
  boundary := 0
  identity :=
    Removal.nodeIndex nestedOccurrence
      ⟨0, by native_decide⟩ (by native_decide)
  sourceWire :=
    Removal.wireIndex nestedOccurrence
      ⟨0, by native_decide⟩ (by native_decide)
  targetWire :=
    Removal.wireIndex nestedOccurrence
      ⟨1, by native_decide⟩ (by native_decide)

theorem nestedRetargetedSplice_isSome :
    (checkIdentityRetargetedSplice nestedRemoved nestedExtraction.checked
      .iteration nestedSourceAttachment [nestedRetargetInput]).isSome =
      true := by
  native_decide

def nestedRetargetedSplice :
    CheckedIdentityRetargetedSplice nestedRemoved nestedExtraction.checked
      .iteration :=
  (checkIdentityRetargetedSplice nestedRemoved nestedExtraction.checked
    .iteration nestedSourceAttachment [nestedRetargetInput]).get
      nestedRetargetedSplice_isSome

theorem nestedRetargetedSplice_accepted :
    checkIdentityRetargetedSplice nestedRemoved nestedExtraction.checked
        .iteration nestedSourceAttachment [nestedRetargetInput] =
      some nestedRetargetedSplice :=
  Option.some_get nestedRetargetedSplice_isSome |>.symm

private theorem nestedSourceSplice_returns_ok :
    (match splice nestedRetargetedSplice.source with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem nestedSourceSplice_succeeds :
    ∃ result, splice nestedRetargetedSplice.source = .ok result := by
  cases accepted : splice nestedRetargetedSplice.source with
  | error error =>
      have success := nestedSourceSplice_returns_ok
      simp [accepted] at success
  | ok result =>
      exact ⟨result, rfl⟩

noncomputable def nestedSourceResult :
    ConcreteSpliceResult nestedRetargetedSplice.source :=
  Classical.choose nestedSourceSplice_succeeds

theorem nestedSourceAccepted :
    splice nestedRetargetedSplice.source = .ok nestedSourceResult :=
  Classical.choose_spec nestedSourceSplice_succeeds

private theorem nestedTargetSplice_returns_ok :
    (match splice nestedRetargetedSplice.target with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem nestedTargetSplice_succeeds :
    ∃ result, splice nestedRetargetedSplice.target = .ok result := by
  cases accepted : splice nestedRetargetedSplice.target with
  | error error =>
      have success := nestedTargetSplice_returns_ok
      simp [accepted] at success
  | ok result =>
      exact ⟨result, rfl⟩

noncomputable def nestedTargetResult :
    ConcreteSpliceResult nestedRetargetedSplice.target :=
  Classical.choose nestedTargetSplice_succeeds

theorem nestedTargetAccepted :
    splice nestedRetargetedSplice.target = .ok nestedTargetResult :=
  Classical.choose_spec nestedTargetSplice_succeeds

theorem siblingRemovalWellFormed :
    (Removal.diagram siblingOccurrence).WellFormed [] := by
  native_decide

def siblingRemoved : RemovalResult siblingOccurrence :=
  ⟨siblingRemovalWellFormed⟩

def siblingSourceTarget :
    Fin nestedExtraction.checked.val.boundary.length →
      siblingRemoved.complement.val.WireId :=
  fun _ =>
    Removal.wireIndex siblingOccurrence
      ⟨0, by native_decide⟩ (by native_decide)

def siblingSourceAttachment :
    ConcreteSpliceAttachment siblingRemoved nestedExtraction.checked where
  target := siblingSourceTarget
  signature := by native_decide
  scope := by native_decide
  identityRequests :=
    computedIdentityRequests siblingRemoved nestedExtraction.checked
      siblingSourceTarget
  identityRequests_nodup := Data.Finite.eraseDups_nodup _
  identityRequests_exact := rfl

def siblingRetargetInput :
    IdentityRetargetInput siblingRemoved.complement where
  boundary := 0
  identity :=
    Removal.nodeIndex siblingOccurrence
      ⟨0, by native_decide⟩ (by native_decide)
  sourceWire :=
    Removal.wireIndex siblingOccurrence
      ⟨0, by native_decide⟩ (by native_decide)
  targetWire :=
    Removal.wireIndex siblingOccurrence
      ⟨1, by native_decide⟩ (by native_decide)

/--
The full splice retarget checker rejects the same identity at an actual
sibling removal site because dominance is absent.
-/
example :
    (checkIdentityRetargetedSplice siblingRemoved nestedExtraction.checked
      .iteration siblingSourceAttachment [siblingRetargetInput]).isSome =
      false := by
  native_decide

/--
The accepted nested occurrence exercises the public premise-free semantic
endpoint on two independently accepted normalized splice results.
-/
example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv nestedTargetResult.checked ↔
      denoteChecked pre definitionEnv nestedSourceResult.checked :=
  identity_retarget_sound nestedExtraction nestedRetargetedSplice
    nestedSourceResult nestedSourceAccepted
    nestedTargetResult nestedTargetAccepted pre definitionEnv

/--
The public substitution theorem compares only independently accepted,
normalized splice results; no semantic equality is supplied by its caller.
-/
example
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {site : RemovalResult occurrence}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice site extracted.checked direction)
    (sourceResult : ConcreteSpliceResult checked.source)
    (sourceAccepted : splice checked.source = .ok sourceResult)
    (targetResult : ConcreteSpliceResult checked.target)
    (targetAccepted : splice checked.target = .ok targetResult)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv targetResult.checked ↔
      denoteChecked pre definitionEnv sourceResult.checked :=
  identity_retarget_sound extracted checked
    sourceResult sourceAccepted targetResult targetAccepted pre definitionEnv

end IdentityFixtures

end VisualProof
