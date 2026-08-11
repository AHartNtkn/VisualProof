import VisualProof.Concrete.Step

namespace VisualProof.Concrete.StructuralValidation

open VisualProof.Diagram

def succeeds : Except ε α → Bool
  | .error _ => false
  | .ok _ => true

def receiptBoundaryValues (result : Except Error (Receipt source)) :
    List Nat :=
  match result with
  | .error _ => []
  | .ok receipt => receipt.target.checked.val.boundary.map Fin.val

def nestedRaw : Concrete.Diagram where
  regionCount := 3
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.bubble 0 1) (fun _ => .cut 1))
  nodes := fun _ => .atom 2 1
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .arg 0 }]
  }

theorem nestedRaw_accepted :
    (checkWellFormed nestedRaw).toOption.isSome := by
  native_decide

def nested : Checked :=
  (checkWellFormed nestedRaw).toOption.get nestedRaw_accepted

def nestedRoot : Fin nested.val.regionCount := ⟨0, by native_decide⟩
def nestedBubble : Fin nested.val.regionCount := ⟨1, by native_decide⟩
def nestedCut : Fin nested.val.regionCount := ⟨2, by native_decide⟩
def nestedAtom : Fin nested.val.nodeCount := ⟨0, by native_decide⟩
def nestedWire : Fin nested.val.wireCount := ⟨0, by native_decide⟩

def nestedState : State 1 where
  checked := {
    val := { diagram := nested.val, boundary := [nestedWire] }
    property := {
      diagram_well_formed := nested.property
      boundary_is_root_scoped := by
        intro wire _
        apply Fin.ext
        native_decide +revert
    }
  }
  boundary_length := rfl

def rootSelectionRequest : SelectionRequest nested.val where
  anchor := nestedRoot
  childRoots := [nestedBubble]
  directNodes := []
  explicitWires := [nestedWire]

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

def isAtomAt {regionCount : Nat} (node : CNode regionCount)
    (region binder : Fin regionCount) : Bool :=
  match node with
  | .atom actualRegion actualBinder =>
      decide (actualRegion = region) && decide (actualBinder = binder)
  | .identity .. => false

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

def isNestedBody (diagram : Concrete.Diagram) : Bool :=
  if cutPresent : 2 < diagram.regionCount then
    if nodePresent : 0 < diagram.nodeCount then
      if wirePresent : 0 < diagram.wireCount then
        let root : Fin diagram.regionCount := ⟨0, by omega⟩
        let bubble : Fin diagram.regionCount := ⟨1, by omega⟩
        let cut : Fin diagram.regionCount := ⟨2, cutPresent⟩
        let node : Fin diagram.nodeCount := ⟨0, nodePresent⟩
        let wire : Fin diagram.wireCount := ⟨0, wirePresent⟩
        diagram.regionCount == 3 &&
          diagram.nodeCount == 1 &&
          diagram.wireCount == 1 &&
          decide (diagram.root = root) &&
          decide (diagram.regions root = .sheet) &&
          decide (diagram.regions bubble = .bubble root 1) &&
          decide (diagram.regions cut = .cut bubble) &&
          isAtomAt (diagram.nodes node) cut bubble &&
          decide ((diagram.wires wire).scope = root) &&
          decide ((diagram.wires wire).endpoints =
            [{ node := node, port := .arg 0 }])
      else false
    else false
  else false

def isNestedBodyRemoved (diagram : Concrete.Diagram) : Bool :=
  if cutPresent : 2 < diagram.regionCount then
    if wirePresent : 0 < diagram.wireCount then
      let root : Fin diagram.regionCount := ⟨0, by omega⟩
      let bubble : Fin diagram.regionCount := ⟨1, by omega⟩
      let cut : Fin diagram.regionCount := ⟨2, cutPresent⟩
      let wire : Fin diagram.wireCount := ⟨0, wirePresent⟩
      diagram.regionCount == 3 &&
        diagram.nodeCount == 0 &&
        diagram.wireCount == 1 &&
        decide (diagram.root = root) &&
        decide (diagram.regions root = .sheet) &&
        decide (diagram.regions bubble = .bubble root 1) &&
        decide (diagram.regions cut = .cut bubble) &&
        decide ((diagram.wires wire).scope = root) &&
        (diagram.wires wire).endpoints.isEmpty
    else false
  else false

def isNestedBodyIterated (diagram : Concrete.Diagram) : Bool :=
  if cutPresent : 2 < diagram.regionCount then
    if secondNodePresent : 1 < diagram.nodeCount then
      if wirePresent : 0 < diagram.wireCount then
        let root : Fin diagram.regionCount := ⟨0, by omega⟩
        let bubble : Fin diagram.regionCount := ⟨1, by omega⟩
        let cut : Fin diagram.regionCount := ⟨2, cutPresent⟩
        let firstNode : Fin diagram.nodeCount := ⟨0, by omega⟩
        let secondNode : Fin diagram.nodeCount := ⟨1, secondNodePresent⟩
        let wire : Fin diagram.wireCount := ⟨0, wirePresent⟩
        diagram.regionCount == 3 &&
          diagram.nodeCount == 2 &&
          diagram.wireCount == 1 &&
          decide (diagram.root = root) &&
          decide (diagram.regions root = .sheet) &&
          decide (diagram.regions bubble = .bubble root 1) &&
          decide (diagram.regions cut = .cut bubble) &&
          isAtomAt (diagram.nodes firstNode) cut bubble &&
          isAtomAt (diagram.nodes secondNode) cut bubble &&
          decide ((diagram.wires wire).scope = root) &&
          decide ((diagram.wires wire).endpoints =
            [{ node := firstNode, port := .arg 0 },
             { node := secondNode, port := .arg 0 }])
      else false
    else false
  else false

def selectionReplacementObservation : Bool :=
  match replaceSelectionRaw nested rootSelection
      (emptySelectionReplacement nested rootSelection) with
  | .error _ => false
  | .ok rootResult =>
      isEmptyRootDiagram rootResult.result.val &&
        match replaceSelectionRaw nested nestedSelection
            (emptySelectionReplacement nested nestedSelection) with
        | .error _ => false
        | .ok nestedResult => isNestedBodyRemoved nestedResult.result.val

theorem root_and_nested_selection_replacement :
    selectionReplacementObservation := by
  native_decide

def nestedBinderSpine :=
  nested.val.extractedBinderSpine nestedSelection

theorem extracted_nonempty_binder_spine :
    nestedBinderSpine.proxyCount = 1 := by
  native_decide

theorem empty_binder_spine : emptyReplacementSpine.proxyCount = 0 := rfl

def binderSpliceObservation : Bool :=
  match spliceRaw {
      frame := nested
      pattern := emptyReplacementOpen
      site := nestedCut
      attachment := Fin.elim0
      binderSpine := emptyReplacementSpine
      binderTarget := Fin.elim0
    } with
  | .error _ => false
  | .ok emptySplice =>
      isNestedBody emptySplice.result.val &&
        match spliceRaw
            (iterationSpliceInput nested nestedSelection nestedCut) with
        | .error _ => false
        | .ok nonemptySplice => isNestedBodyIterated nonemptySplice.result.val

theorem empty_and_nonempty_binder_splice :
    binderSpliceObservation := by
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

def hasNestedOpenBoundary (state : State 1) : Bool :=
  decide (state.checked.val.boundary.map Fin.val = [0])

def isNestedDoubleCut (diagram : Concrete.Diagram) : Bool :=
  if innerPresent : 4 < diagram.regionCount then
    if nodePresent : 0 < diagram.nodeCount then
      if wirePresent : 0 < diagram.wireCount then
        let root : Fin diagram.regionCount := ⟨0, by omega⟩
        let binder : Fin diagram.regionCount := ⟨1, by omega⟩
        let site : Fin diagram.regionCount := ⟨2, by omega⟩
        let outer : Fin diagram.regionCount := ⟨3, by omega⟩
        let inner : Fin diagram.regionCount := ⟨4, innerPresent⟩
        let node : Fin diagram.nodeCount := ⟨0, nodePresent⟩
        let wire : Fin diagram.wireCount := ⟨0, wirePresent⟩
        diagram.regionCount == 5 &&
          diagram.nodeCount == 1 &&
          diagram.wireCount == 1 &&
          decide (diagram.root = root) &&
          decide (diagram.regions root = .sheet) &&
          decide (diagram.regions binder = .bubble root 1) &&
          decide (diagram.regions site = .cut binder) &&
          decide (diagram.regions outer = .cut site) &&
          decide (diagram.regions inner = .cut outer) &&
          isAtomAt (diagram.nodes node) inner binder &&
          decide ((diagram.wires wire).scope = root) &&
          decide ((diagram.wires wire).endpoints =
            [{ node := node, port := .arg 0 }])
      else false
    else false
  else false

def isNestedVacuous (diagram : Concrete.Diagram) : Bool :=
  if bubblePresent : 3 < diagram.regionCount then
    if nodePresent : 0 < diagram.nodeCount then
      if wirePresent : 0 < diagram.wireCount then
        let root : Fin diagram.regionCount := ⟨0, by omega⟩
        let binder : Fin diagram.regionCount := ⟨1, by omega⟩
        let site : Fin diagram.regionCount := ⟨2, by omega⟩
        let bubble : Fin diagram.regionCount := ⟨3, bubblePresent⟩
        let node : Fin diagram.nodeCount := ⟨0, nodePresent⟩
        let wire : Fin diagram.wireCount := ⟨0, wirePresent⟩
        diagram.regionCount == 4 &&
          diagram.nodeCount == 1 &&
          diagram.wireCount == 1 &&
          decide (diagram.root = root) &&
          decide (diagram.regions root = .sheet) &&
          decide (diagram.regions binder = .bubble root 1) &&
          decide (diagram.regions site = .cut binder) &&
          decide (diagram.regions bubble = .bubble site 2) &&
          isAtomAt (diagram.nodes node) bubble binder &&
          decide ((diagram.wires wire).scope = root) &&
          decide ((diagram.wires wire).endpoints =
            [{ node := node, port := .arg 0 }])
      else false
    else false
  else false

def nestedDoubleCutRaw : Concrete.Diagram where
  regionCount := 5
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.bubble 0 1)
      (Fin.cases (.cut 1)
        (Fin.cases (.cut 2) (fun _ => .cut 3))))
  nodes := fun _ => .atom 4 1
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .arg 0 }]
  }

theorem nestedDoubleCutRaw_accepted :
    (checkWellFormed nestedDoubleCutRaw).toOption.isSome := by
  native_decide

def nestedDoubleCut : Checked :=
  (checkWellFormed nestedDoubleCutRaw).toOption.get
    nestedDoubleCutRaw_accepted

def nestedDoubleCutWire : Fin nestedDoubleCut.val.wireCount :=
  ⟨0, by native_decide⟩

def nestedDoubleCutState : State 1 where
  checked := {
    val := {
      diagram := nestedDoubleCut.val
      boundary := [nestedDoubleCutWire]
    }
    property := {
      diagram_well_formed := nestedDoubleCut.property
      boundary_is_root_scoped := by
        intro wire _
        apply Fin.ext
        native_decide +revert
    }
  }
  boundary_length := rfl

def nestedVacuousRaw : Concrete.Diagram where
  regionCount := 4
  nodeCount := 1
  wireCount := 1
  root := 0
  regions := Fin.cases .sheet
    (Fin.cases (.bubble 0 1)
      (Fin.cases (.cut 1) (fun _ => .bubble 2 2)))
  nodes := fun _ => .atom 3 1
  wires := fun _ => {
    scope := 0
    endpoints := [{ node := 0, port := .arg 0 }]
  }

theorem nestedVacuousRaw_accepted :
    (checkWellFormed nestedVacuousRaw).toOption.isSome := by
  native_decide

def nestedVacuous : Checked :=
  (checkWellFormed nestedVacuousRaw).toOption.get
    nestedVacuousRaw_accepted

def nestedVacuousWire : Fin nestedVacuous.val.wireCount :=
  ⟨0, by native_decide⟩

def nestedVacuousState : State 1 where
  checked := {
    val := {
      diagram := nestedVacuous.val
      boundary := [nestedVacuousWire]
    }
    property := {
      diagram_well_formed := nestedVacuous.property
      boundary_is_root_scoped := by
        intro wire _
        apply Fin.ext
        native_decide +revert
    }
  }
  boundary_length := rfl

def nestedBodySelection? (input : Checked) :
    Option (CheckedSelection input.val) :=
  if cutPresent : 2 < input.val.regionCount then
    if nodePresent : 0 < input.val.nodeCount then
      let request : SelectionRequest input.val := {
        anchor := ⟨2, cutPresent⟩
        childRoots := []
        directNodes := [⟨0, nodePresent⟩]
        explicitWires := []
      }
      (checkSelection request).toOption
    else none
  else none

def doubleCutRoundTrip : Bool :=
  match applyDoubleCutIntro nested nestedSelection with
  | .error _ => false
  | .ok introduced =>
      match introduced.toReceipt nestedState with
      | none => false
      | some wrapped =>
          isNestedDoubleCut wrapped.target.diagram.val &&
            hasNestedOpenBoundary wrapped.target &&
            if outerExists : 3 < wrapped.target.diagram.val.regionCount then
              let outer : Fin wrapped.target.diagram.val.regionCount :=
                ⟨3, outerExists⟩
              (recognizeDoubleCut wrapped.target.diagram outer).isSome &&
                match applyDoubleCutElim wrapped.target.diagram outer with
                | .error _ => false
                | .ok eliminated =>
                    match eliminated.toReceipt wrapped.target with
                    | none => false
                    | some restored =>
                        isNestedBody restored.target.diagram.val &&
                          hasNestedOpenBoundary restored.target
            else false

theorem double_cut_intro_elim_round_trip : doubleCutRoundTrip := by
  native_decide

def vacuousRoundTrip : Bool :=
  match applyVacuousIntro nested nestedSelection 2 with
  | .error _ => false
  | .ok introduced =>
      match introduced.toReceipt nestedState with
      | none => false
      | some wrapped =>
          isNestedVacuous wrapped.target.diagram.val &&
            hasNestedOpenBoundary wrapped.target &&
            if bubbleExists : 3 < wrapped.target.diagram.val.regionCount then
              let bubble : Fin wrapped.target.diagram.val.regionCount :=
                ⟨3, bubbleExists⟩
              (recognizeVacuous wrapped.target.diagram bubble).isSome &&
                match applyVacuousElim wrapped.target.diagram bubble with
                | .error _ => false
                | .ok eliminated =>
                    match eliminated.toReceipt wrapped.target with
                    | none => false
                    | some restored =>
                        isNestedBody restored.target.diagram.val &&
                          hasNestedOpenBoundary restored.target
            else false

theorem vacuous_intro_elim_round_trip : vacuousRoundTrip := by
  native_decide

def doubleCutReverseRoundTrip : Bool :=
  if outerExists : 3 < nestedDoubleCut.val.regionCount then
    let outer : Fin nestedDoubleCut.val.regionCount := ⟨3, outerExists⟩
    isNestedDoubleCut nestedDoubleCut.val &&
      hasNestedOpenBoundary nestedDoubleCutState &&
      (recognizeDoubleCut nestedDoubleCut outer).isSome &&
      match applyDoubleCutElim nestedDoubleCut outer with
      | .error _ => false
      | .ok eliminated =>
          match eliminated.toReceipt nestedDoubleCutState with
          | none => false
          | some body =>
              isNestedBody body.target.diagram.val &&
                hasNestedOpenBoundary body.target &&
                match nestedBodySelection? body.target.diagram with
                | none => false
                | some selection =>
                    match applyDoubleCutIntro body.target.diagram selection with
                    | .error _ => false
                    | .ok introduced =>
                        match introduced.toReceipt body.target with
                        | none => false
                        | some restored =>
                            isNestedDoubleCut restored.target.diagram.val &&
                              hasNestedOpenBoundary restored.target
  else false

theorem double_cut_elim_intro_round_trip : doubleCutReverseRoundTrip := by
  native_decide

def vacuousReverseRoundTrip : Bool :=
  if bubbleExists : 3 < nestedVacuous.val.regionCount then
    let bubble : Fin nestedVacuous.val.regionCount := ⟨3, bubbleExists⟩
    isNestedVacuous nestedVacuous.val &&
      hasNestedOpenBoundary nestedVacuousState &&
      (recognizeVacuous nestedVacuous bubble).isSome &&
      match applyVacuousElim nestedVacuous bubble with
      | .error _ => false
      | .ok eliminated =>
          match eliminated.toReceipt nestedVacuousState with
          | none => false
          | some body =>
              isNestedBody body.target.diagram.val &&
                hasNestedOpenBoundary body.target &&
                match nestedBodySelection? body.target.diagram with
                | none => false
                | some selection =>
                    match applyVacuousIntro body.target.diagram selection 2 with
                    | .error _ => false
                    | .ok introduced =>
                        match introduced.toReceipt body.target with
                        | none => false
                        | some restored =>
                            isNestedVacuous restored.target.diagram.val &&
                              hasNestedOpenBoundary restored.target
  else false

theorem vacuous_elim_intro_round_trip : vacuousReverseRoundTrip := by
  native_decide

end VisualProof.Concrete.StructuralValidation
