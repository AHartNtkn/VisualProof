import VisualProof.Concrete.Step

namespace VisualProof.Concrete.StructuralValidation

open VisualProof.Diagram

def succeeds : Except ε α → Bool
  | .error _ => false
  | .ok _ => true

def operationRegionCount (result : Except ε (OperationReceipt input)) :
    Nat :=
  match result with
  | .error _ => 0
  | .ok receipt => receipt.result.val.regionCount

def receiptBoundaryValues (result : Except Error (Receipt source)) :
    List Nat :=
  match result with
  | .error _ => []
  | .ok receipt => receipt.target.checked.val.boundary.map Fin.val

def nestedRaw : Concrete.Diagram where
  regionCount := 3
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.bubble 0 0) (fun _ => .cut 1))
  nodes := fun _ => .atom 2 1
  wires := Fin.elim0

theorem nestedRaw_accepted :
    (checkWellFormed nestedRaw).toOption.isSome := by
  native_decide

def nested : Checked :=
  (checkWellFormed nestedRaw).toOption.get nestedRaw_accepted

def nestedRoot : Fin nested.val.regionCount := ⟨0, by native_decide⟩
def nestedBubble : Fin nested.val.regionCount := ⟨1, by native_decide⟩
def nestedCut : Fin nested.val.regionCount := ⟨2, by native_decide⟩
def nestedAtom : Fin nested.val.nodeCount := ⟨0, by native_decide⟩

def rootSelectionRequest : SelectionRequest nested.val where
  anchor := nestedRoot
  childRoots := [nestedBubble]
  directNodes := []
  explicitWires := []

theorem rootSelectionRequest_accepted :
    (checkSelection rootSelectionRequest).toOption.isSome := by
  native_decide

def rootSelection : CheckedSelection nested.val :=
  (checkSelection rootSelectionRequest).toOption.get
    rootSelectionRequest_accepted

def nestedSelectionRequest : SelectionRequest nested.val where
  anchor := nestedCut
  childRoots := []
  directNodes := [nestedAtom]
  explicitWires := []

theorem nestedSelectionRequest_accepted :
    (checkSelection nestedSelectionRequest).toOption.isSome := by
  native_decide

def nestedSelection : CheckedSelection nested.val :=
  (checkSelection nestedSelectionRequest).toOption.get
    nestedSelectionRequest_accepted

def selectionReplacementCounts : Nat × Nat :=
  (operationRegionCount (replaceSelectionRaw nested rootSelection
      (emptySelectionReplacement nested rootSelection)),
    operationRegionCount (replaceSelectionRaw nested nestedSelection
      (emptySelectionReplacement nested nestedSelection)))

theorem root_and_nested_selection_replacement :
    selectionReplacementCounts = (1, 3) := by
  native_decide

def nestedBinderSpine :=
  nested.val.extractedBinderSpine nestedSelection

theorem extracted_nonempty_binder_spine :
    nestedBinderSpine.proxyCount = 1 := by
  native_decide

theorem empty_binder_spine : emptyReplacementSpine.proxyCount = 0 := rfl

def binderSpliceCounts : Nat × Nat :=
  (operationRegionCount (spliceRaw {
      frame := nested
      pattern := emptyReplacementOpen
      site := nestedCut
      attachment := Fin.elim0
      binderSpine := emptyReplacementSpine
      binderTarget := Fin.elim0
    }),
    operationRegionCount
      (spliceRaw (iterationSpliceInput nested nestedSelection nestedCut)))

theorem empty_and_nonempty_binder_splice :
    binderSpliceCounts = (3, 3) := by
  native_decide

def nonterminalPatternRaw : Concrete.Diagram where
  regionCount := 3
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.bubble 0 0) (fun _ => .cut 0))
  nodes := Fin.elim0
  wires := Fin.elim0

theorem nonterminalPatternRaw_accepted :
    (checkWellFormed nonterminalPatternRaw).toOption.isSome := by
  native_decide

def nonterminalPatternChecked : Checked :=
  (checkWellFormed nonterminalPatternRaw).toOption.get
    nonterminalPatternRaw_accepted

def nonterminalPattern : CheckedOpen where
  val := { diagram := nonterminalPatternChecked.val, boundary := [] }
  property := {
    diagram_well_formed := nonterminalPatternChecked.property
    boundary_is_root_scoped := by simp
  }

def nonterminalPatternProxy : Fin nonterminalPattern.val.diagram.regionCount :=
  ⟨1, by native_decide⟩

def nonterminalPatternSpine : BinderSpine nonterminalPattern.val.diagram where
  proxyCount := 1
  proxy := fun _ => nonterminalPatternProxy
  arity := fun _ => 0
  bodyContainer := nonterminalPatternProxy
  proxy_injective := fun _ _ _ => Subsingleton.elim _ _
  proxy_ne_root := by
    intro index equality
    have values := congrArg Fin.val equality
    have proxyValue : nonterminalPatternProxy.val = 1 := rfl
    have rootValue : nonterminalPattern.val.diagram.root.val = 0 := by
      native_decide
    omega
  body_eq_root_of_empty := by
    intro impossible
    omega
  body_eq_terminal_of_nonempty := by intros; rfl
  proxy_region := by
    intro index
    native_decide +revert

def nonterminalSpliceInput : Splice.Input where
  frame := nested
  pattern := nonterminalPattern
  site := nestedCut
  attachment := Fin.elim0
  binderSpine := nonterminalPatternSpine
  binderTarget := fun _ => nestedBubble

def nonterminalSpineRejected : Bool :=
  match spliceRaw nonterminalSpliceInput with
  | .error .nonterminalBinderSpine => true
  | _ => false

theorem nonterminal_binder_spine_is_rejected : nonterminalSpineRejected := by
  native_decide

def aliasFrameRaw : Concrete.Diagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := Fin.elim0
  wires := fun _ => { scope := 0, endpoints := [] }

theorem aliasFrameRaw_accepted :
    (checkWellFormed aliasFrameRaw).toOption.isSome := by
  native_decide

def aliasFrame : Checked :=
  (checkWellFormed aliasFrameRaw).toOption.get aliasFrameRaw_accepted

def aliasPatternRaw : Concrete.Diagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := Fin.elim0
  wires := fun _ => { scope := 0, endpoints := [] }

theorem aliasPatternRaw_accepted :
    (checkWellFormed aliasPatternRaw).toOption.isSome := by
  native_decide

def aliasPatternChecked : Checked :=
  (checkWellFormed aliasPatternRaw).toOption.get aliasPatternRaw_accepted

def aliasPatternWire : Fin aliasPatternChecked.val.wireCount :=
  ⟨0, by native_decide⟩

def aliasPatternOpen : Concrete.OpenDiagram where
  diagram := aliasPatternChecked.val
  boundary := [aliasPatternWire, aliasPatternWire]

def aliasPattern : CheckedOpen where
  val := aliasPatternOpen
  property := {
    diagram_well_formed := aliasPatternChecked.property
    boundary_is_root_scoped := by
      intro wire _
      apply Fin.ext
      native_decide +revert
  }

def aliasPatternSpine : BinderSpine aliasPattern.val.diagram where
  proxyCount := 0
  proxy := Fin.elim0
  arity := Fin.elim0
  bodyContainer := aliasPattern.val.diagram.root
  proxy_injective := fun index => Fin.elim0 index
  proxy_ne_root := fun index => Fin.elim0 index
  body_eq_root_of_empty := fun _ => rfl
  body_eq_terminal_of_nonempty := by simp
  proxy_region := fun index => Fin.elim0 index

def aliasSpliceInput : Splice.Input where
  frame := aliasFrame
  pattern := aliasPattern
  site := ⟨0, by native_decide⟩
  attachment := fun position =>
    if position.val = 0 then
      ⟨0, by native_decide⟩
    else
      ⟨1, by native_decide⟩
  binderSpine := aliasPatternSpine
  binderTarget := Fin.elim0

def aliasFrameOpen : Concrete.OpenDiagram where
  diagram := aliasFrame.val
  boundary := [⟨0, by native_decide⟩, ⟨1, by native_decide⟩]

def aliasState : State 2 where
  checked := {
    val := aliasFrameOpen
    property := {
      diagram_well_formed := aliasFrame.property
      boundary_is_root_scoped := by
        intro wire _
        apply Fin.ext
        native_decide +revert
    }
  }
  boundary_length := rfl

def aliasedBoundaryValues : List Nat :=
  match spliceRaw aliasSpliceInput with
  | .error _ => []
  | .ok operation =>
      match operation.toReceipt aliasState with
      | none => []
      | some receipt =>
          receipt.target.checked.val.boundary.map Fin.val

theorem splice_preserves_aliased_boundary_positions :
    aliasedBoundaryValues = [0, 0] := by
  native_decide

def splitFrameRaw : Concrete.Diagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := Fin.elim0
  wires := fun _ => { scope := 0, endpoints := [] }

theorem splitFrameRaw_accepted :
    (checkWellFormed splitFrameRaw).toOption.isSome := by
  native_decide

def splitFrame : Checked :=
  (checkWellFormed splitFrameRaw).toOption.get splitFrameRaw_accepted

def splitWire : Fin splitFrame.val.wireCount :=
  ⟨0, by native_decide⟩

def splitState : State 2 where
  checked := {
    val := { diagram := splitFrame.val, boundary := [splitWire, splitWire] }
    property := {
      diagram_well_formed := splitFrame.property
      boundary_is_root_scoped := by
        intro wire _
        apply Fin.ext
        native_decide +revert
    }
  }
  boundary_length := rfl

def splitStateWire : Fin splitState.checked.val.diagram.wireCount :=
  ⟨0, by native_decide⟩

def alternatingSplitBoundary : WireSeverBoundary splitState splitStateWire where
  side := fun position => decide (position.val = 1)
  other := by
    intro position different
    apply (different ?_).elim
    apply Fin.ext
    native_decide +revert

def splitBoundaryValues : List Nat :=
  receiptBoundaryValues
    (splitWireRaw splitState splitStateWire [] alternatingSplitBoundary)

theorem split_open_boundary_by_position :
    splitBoundaryValues = [0, 1] := by
  native_decide

def singleCutRaw : Concrete.Diagram where
  regionCount := 2
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet (fun _ => .cut 0)
  nodes := Fin.elim0
  wires := Fin.elim0

theorem singleCutRaw_accepted :
    (checkWellFormed singleCutRaw).toOption.isSome := by
  native_decide

def singleCut : Checked :=
  (checkWellFormed singleCutRaw).toOption.get singleCutRaw_accepted

def boundBubbleRaw : Concrete.Diagram where
  regionCount := 2
  nodeCount := 1
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet (fun _ => .bubble 0 0)
  nodes := fun _ => .atom 1 1
  wires := Fin.elim0

theorem boundBubbleRaw_accepted :
    (checkWellFormed boundBubbleRaw).toOption.isSome := by
  native_decide

def boundBubble : Checked :=
  (checkWellFormed boundBubbleRaw).toOption.get boundBubbleRaw_accepted

def singleCutRegion : Fin singleCut.val.regionCount :=
  ⟨1, by native_decide⟩

def boundBubbleRegion : Fin boundBubble.val.regionCount :=
  ⟨1, by native_decide⟩

def wrapperRecognitionFailures : Bool × Bool :=
  ((recognizeDoubleCut singleCut singleCutRegion).isNone,
    (recognizeVacuous boundBubble boundBubbleRegion).isNone)

theorem malformed_wrappers_are_rejected :
    wrapperRecognitionFailures = (true, true) := by
  native_decide

def emptyChecked : Checked :=
  ⟨emptyReplacementDiagram, emptyReplacementDiagram_wellFormed⟩

def emptyRoot : Fin emptyChecked.val.regionCount :=
  ⟨0, by native_decide⟩

def emptyRootSelectionRequest : SelectionRequest emptyChecked.val where
  anchor := emptyRoot
  childRoots := []
  directNodes := []
  explicitWires := []

theorem emptyRootSelectionRequest_accepted :
    (checkSelection emptyRootSelectionRequest).toOption.isSome := by
  native_decide

def emptyRootSelection : CheckedSelection emptyChecked.val :=
  (checkSelection emptyRootSelectionRequest).toOption.get
    emptyRootSelectionRequest_accepted

def emptyRootSelectionFor (input : Checked) : CheckedSelection input.val :=
  ⟨{
    anchor := input.val.root
    childRoots := []
    directNodes := []
    explicitWires := []
  }, {
    childRoots_nodup := by simp
    childRoots_direct := by simp
    directNodes_nodup := by simp
    directNodes_at_anchor := by simp
    explicitWires_nodup := by simp
    explicitWires_at_anchor := by simp
    explicitWireEndpoints_selected := by simp
  }⟩

def isEmptyRootDiagram (diagram : Concrete.Diagram) : Bool :=
  if present : 0 < diagram.regionCount then
    let root : Fin diagram.regionCount := ⟨0, present⟩
    diagram.regionCount == 1 &&
      diagram.nodeCount == 0 &&
      diagram.wireCount == 0 &&
      decide (diagram.root = root) &&
      decide (diagram.regions root = .sheet)
  else
    false

def isCanonicalDoubleCut (diagram : Concrete.Diagram) : Bool :=
  if innerPresent : 2 < diagram.regionCount then
    let root : Fin diagram.regionCount := ⟨0, by omega⟩
    let outer : Fin diagram.regionCount := ⟨1, by omega⟩
    let inner : Fin diagram.regionCount := ⟨2, innerPresent⟩
    diagram.regionCount == 3 &&
      diagram.nodeCount == 0 &&
      diagram.wireCount == 0 &&
      decide (diagram.root = root) &&
      decide (diagram.regions root = .sheet) &&
      decide (diagram.regions outer = .cut root) &&
      decide (diagram.regions inner = .cut outer)
  else
    false

def isCanonicalVacuous (diagram : Concrete.Diagram) : Bool :=
  if bubblePresent : 1 < diagram.regionCount then
    let root : Fin diagram.regionCount := ⟨0, by omega⟩
    let bubble : Fin diagram.regionCount := ⟨1, bubblePresent⟩
    diagram.regionCount == 2 &&
      diagram.nodeCount == 0 &&
      diagram.wireCount == 0 &&
      decide (diagram.root = root) &&
      decide (diagram.regions root = .sheet) &&
      decide (diagram.regions bubble = .bubble root 0)
  else
    false

def doubleCutRoundTrip : Bool :=
  match applyDoubleCutIntro emptyChecked emptyRootSelection with
  | .error _ => false
  | .ok introduced =>
      if outerExists : 1 < introduced.result.val.regionCount then
        (recognizeDoubleCut introduced.result ⟨1, outerExists⟩).isSome &&
          match applyDoubleCutElim introduced.result ⟨1, outerExists⟩ with
          | .error _ => false
          | .ok eliminated =>
              isEmptyRootDiagram eliminated.result.val &&
                match eliminated.toReceipt (State.closed introduced.result) with
                | none => false
                | some receipt => receipt.target.checked.val.boundary.isEmpty
      else false

theorem double_cut_intro_elim_round_trip : doubleCutRoundTrip := by
  native_decide

def vacuousRoundTrip : Bool :=
  match applyVacuousIntro emptyChecked emptyRootSelection 0 with
  | .error _ => false
  | .ok introduced =>
      if bubbleExists : 1 < introduced.result.val.regionCount then
        (recognizeVacuous introduced.result ⟨1, bubbleExists⟩).isSome &&
          match applyVacuousElim introduced.result ⟨1, bubbleExists⟩ with
          | .error _ => false
          | .ok eliminated =>
              isEmptyRootDiagram eliminated.result.val &&
                match eliminated.toReceipt (State.closed introduced.result) with
                | none => false
                | some receipt => receipt.target.checked.val.boundary.isEmpty
      else false

theorem vacuous_intro_elim_round_trip : vacuousRoundTrip := by
  native_decide

def canonicalDoubleCutRaw : Concrete.Diagram where
  regionCount := 3
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.cut 0) (fun _ => .cut 1))
  nodes := Fin.elim0
  wires := Fin.elim0

theorem canonicalDoubleCutRaw_accepted :
    (checkWellFormed canonicalDoubleCutRaw).toOption.isSome := by
  native_decide

def canonicalDoubleCut : Checked :=
  (checkWellFormed canonicalDoubleCutRaw).toOption.get
    canonicalDoubleCutRaw_accepted

def canonicalDoubleCutOuter : Fin canonicalDoubleCut.val.regionCount :=
  ⟨1, by native_decide⟩

def doubleCutReverseRoundTrip : Bool :=
  match applyDoubleCutElim canonicalDoubleCut canonicalDoubleCutOuter with
  | .error _ => false
  | .ok eliminated =>
      isEmptyRootDiagram eliminated.result.val &&
        match applyDoubleCutIntro eliminated.result
            (emptyRootSelectionFor eliminated.result) with
        | .error _ => false
        | .ok introduced =>
            isCanonicalDoubleCut introduced.result.val

theorem double_cut_elim_intro_round_trip : doubleCutReverseRoundTrip := by
  native_decide

def canonicalVacuousRaw : Concrete.Diagram where
  regionCount := 2
  nodeCount := 0
  wireCount := 0
  root := 0
  regions := Fin.cases .sheet (fun _ => .bubble 0 0)
  nodes := Fin.elim0
  wires := Fin.elim0

theorem canonicalVacuousRaw_accepted :
    (checkWellFormed canonicalVacuousRaw).toOption.isSome := by
  native_decide

def canonicalVacuous : Checked :=
  (checkWellFormed canonicalVacuousRaw).toOption.get
    canonicalVacuousRaw_accepted

def canonicalVacuousBubble : Fin canonicalVacuous.val.regionCount :=
  ⟨1, by native_decide⟩

def vacuousReverseRoundTrip : Bool :=
  match applyVacuousElim canonicalVacuous canonicalVacuousBubble with
  | .error _ => false
  | .ok eliminated =>
      isEmptyRootDiagram eliminated.result.val &&
        match applyVacuousIntro eliminated.result
            (emptyRootSelectionFor eliminated.result) 0 with
        | .error _ => false
        | .ok introduced => isCanonicalVacuous introduced.result.val

theorem vacuous_elim_intro_round_trip : vacuousReverseRoundTrip := by
  native_decide

end VisualProof.Concrete.StructuralValidation
