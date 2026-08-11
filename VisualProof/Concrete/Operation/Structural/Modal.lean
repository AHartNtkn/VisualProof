import VisualProof.Concrete.Operation.Structural.Wire

namespace VisualProof.Concrete

open VisualProof.Diagram
open VisualProof.Data.Finite

namespace DoubleCutWrapper

/-- Add the canonical pair of nested cut regions around a replacement
fragment's binder-spine body while preserving its wire and node carriers. -/
def diagram (pattern : OpenDiagram)
    (spine : BinderSpine pattern.diagram) : Concrete.Diagram :=
  let outer : Fin (pattern.diagram.regionCount + 2) :=
    Fin.natAdd pattern.diagram.regionCount ⟨0, by decide⟩
  let inner : Fin (pattern.diagram.regionCount + 2) :=
    Fin.natAdd pattern.diagram.regionCount ⟨1, by decide⟩
  { regionCount := pattern.diagram.regionCount + 2
    nodeCount := pattern.diagram.nodeCount
    wireCount := pattern.diagram.wireCount
    root := Fin.castAdd 2 pattern.diagram.root
    regions := Fin.addCases
      (fun region =>
        if ∃ index, region = spine.proxy index then
          liftCRegion 2 (pattern.diagram.regions region)
        else if (pattern.diagram.regions region).parent? =
            some spine.bodyContainer then
          reparentLiftedRegion 2 inner (pattern.diagram.regions region)
        else
          liftCRegion 2 (pattern.diagram.regions region))
      (Fin.cases (.cut (Fin.castAdd 2 spine.bodyContainer))
        (fun _ => .cut outer))
    nodes := fun node =>
      if (pattern.diagram.nodes node).region = spine.bodyContainer then
        reparentLiftedNode 2 inner (pattern.diagram.nodes node)
      else
        liftCNode 2 (pattern.diagram.nodes node)
    wires := fun wire =>
      let original := pattern.diagram.wires wire
      if wire ∈ pattern.boundary then
        liftCWireRegions 2 original
      else if original.scope = spine.bodyContainer then
        { scope := inner, endpoints := original.endpoints }
      else
        liftCWireRegions 2 original }

/-- The canonical double-cut wrapper preserves the replacement boundary. -/
def openDiagram (pattern : OpenDiagram)
    (spine : BinderSpine pattern.diagram) : OpenDiagram where
  diagram := diagram pattern spine
  boundary := pattern.boundary

private theorem doubleCutWrapperBoundaryRootScoped
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram) :
    ∀ wire, wire ∈ (openDiagram pattern.val spine).boundary →
      ((openDiagram pattern.val spine).diagram.wires wire).scope =
        (openDiagram pattern.val spine).diagram.root := by
  intro wire hwire
  change wire ∈ pattern.val.boundary at hwire
  have hroot := pattern.property.boundary_is_root_scoped wire hwire
  change (if wire ∈ pattern.val.boundary then
      liftCWireRegions 2 (pattern.val.diagram.wires wire)
    else if (pattern.val.diagram.wires wire).scope = spine.bodyContainer then
      { scope := Fin.natAdd pattern.val.diagram.regionCount ⟨1, by decide⟩
        endpoints := (pattern.val.diagram.wires wire).endpoints }
    else liftCWireRegions 2 (pattern.val.diagram.wires wire)).scope =
      Fin.castAdd 2 pattern.val.diagram.root
  rw [if_pos hwire]
  exact congrArg (Fin.castAdd 2) hroot

/-- Lift the source-derived binder spine through the canonical wrapper. -/
def spine
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram) :
    BinderSpine (diagram pattern spine) where
  proxyCount := spine.proxyCount
  proxy := fun index => Fin.castAdd 2 (spine.proxy index)
  arity := spine.arity
  bodyContainer := Fin.castAdd 2 spine.bodyContainer
  proxy_injective := by
    intro left right equality
    apply spine.proxy_injective
    apply Fin.ext
    exact congrArg
      (fun value : Fin (pattern.diagram.regionCount + 2) => value.val) equality
  proxy_ne_root := by
    intro index equality
    apply spine.proxy_ne_root index
    apply Fin.ext
    exact congrArg
      (fun value : Fin (pattern.diagram.regionCount + 2) => value.val) equality
  body_eq_root_of_empty := by
    intro empty
    exact congrArg (Fin.castAdd 2) (spine.body_eq_root_of_empty empty)
  body_eq_terminal_of_nonempty := by
    intro nonempty
    exact congrArg (Fin.castAdd 2)
      (spine.body_eq_terminal_of_nonempty nonempty)
  proxy_region := by
    intro index
    have isProxy : ∃ candidate, spine.proxy index = spine.proxy candidate :=
      ⟨index, rfl⟩
    rw [show (diagram pattern spine).regions
        (Fin.castAdd 2 (spine.proxy index)) =
          liftCRegion 2 (pattern.diagram.regions (spine.proxy index)) by
      simp [diagram, isProxy]]
    rw [spine.proxy_region index]
    split <;> rfl

end DoubleCutWrapper

def doubleCutWrappedReplacement (input : Checked)
    (selection : CheckedSelection input.val) :
    Except Error (SelectionReplacement input selection) :=
  let base := extractedSelectionReplacementFor input selection selection
  let rawOpen := DoubleCutWrapper.openDiagram
    base.pattern.val base.binderSpine
  match hcheck : checkWellFormed rawOpen.diagram with
  | .error error => .error (.resultNotWellFormed error)
  | .ok checked =>
      let pattern : CheckedOpen := ⟨rawOpen, {
        diagram_well_formed := by
          rw [← checkWellFormed_preserves_input hcheck]
          exact checked.property
        boundary_is_root_scoped :=
          DoubleCutWrapper.doubleCutWrapperBoundaryRootScoped
            base.pattern base.binderSpine
      }⟩
      .ok {
        pattern
        attachment := base.attachment
        attachment_consistent := base.attachment_consistent
        binderSpine := DoubleCutWrapper.spine
          base.pattern.val base.binderSpine
        binderTarget := base.binderTarget
      }


private def vacuousWrapperDiagram (pattern : OpenDiagram)
    (spine : BinderSpine pattern.diagram) (arity : Nat) : Concrete.Diagram :=
  let bubble : Fin (pattern.diagram.regionCount + 1) :=
    Fin.last pattern.diagram.regionCount
  { regionCount := pattern.diagram.regionCount + 1
    nodeCount := pattern.diagram.nodeCount
    wireCount := pattern.diagram.wireCount
    root := pattern.diagram.root.castSucc
    regions := Fin.lastCases
      (.bubble spine.bodyContainer.castSucc arity)
      (fun region =>
        if ∃ index, region = spine.proxy index then
          liftCRegion 1 (pattern.diagram.regions region)
        else if (pattern.diagram.regions region).parent? =
            some spine.bodyContainer then
          reparentLiftedRegion 1 bubble (pattern.diagram.regions region)
        else
          liftCRegion 1 (pattern.diagram.regions region))
    nodes := fun node =>
      if (pattern.diagram.nodes node).region = spine.bodyContainer then
        reparentLiftedNode 1 bubble (pattern.diagram.nodes node)
      else
        liftCNode 1 (pattern.diagram.nodes node)
    wires := fun wire =>
      let original := pattern.diagram.wires wire
      if wire ∈ pattern.boundary then
        liftCWireRegions 1 original
      else if original.scope = spine.bodyContainer then
        { scope := bubble, endpoints := original.endpoints }
      else
        liftCWireRegions 1 original }

private def vacuousWrapperOpen (pattern : OpenDiagram)
    (spine : BinderSpine pattern.diagram) (arity : Nat) : OpenDiagram where
  diagram := vacuousWrapperDiagram pattern spine arity
  boundary := pattern.boundary

private theorem vacuousWrapperBoundaryRootScoped
    (pattern : CheckedOpen) (spine : BinderSpine pattern.val.diagram)
    (arity : Nat) :
    ∀ wire, wire ∈ (vacuousWrapperOpen pattern.val spine arity).boundary →
      ((vacuousWrapperOpen pattern.val spine arity).diagram.wires wire).scope =
        (vacuousWrapperOpen pattern.val spine arity).diagram.root := by
  intro wire hwire
  change wire ∈ pattern.val.boundary at hwire
  have hroot := pattern.property.boundary_is_root_scoped wire hwire
  change (if wire ∈ pattern.val.boundary then
      liftCWireRegions 1 (pattern.val.diagram.wires wire)
    else if (pattern.val.diagram.wires wire).scope = spine.bodyContainer then
      { scope := Fin.last pattern.val.diagram.regionCount
        endpoints := (pattern.val.diagram.wires wire).endpoints }
    else liftCWireRegions 1 (pattern.val.diagram.wires wire)).scope =
      pattern.val.diagram.root.castSucc
  rw [if_pos hwire]
  exact congrArg Fin.castSucc hroot

private def vacuousWrapperSpine
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (arity : Nat) : BinderSpine (vacuousWrapperDiagram pattern spine arity) where
  proxyCount := spine.proxyCount
  proxy := fun index => (spine.proxy index).castSucc
  arity := spine.arity
  bodyContainer := spine.bodyContainer.castSucc
  proxy_injective := by
    intro left right equality
    apply spine.proxy_injective
    apply Fin.ext
    exact congrArg
      (fun value : Fin (pattern.diagram.regionCount + 1) => value.val) equality
  proxy_ne_root := by
    intro index equality
    apply spine.proxy_ne_root index
    apply Fin.ext
    exact congrArg
      (fun value : Fin (pattern.diagram.regionCount + 1) => value.val) equality
  body_eq_root_of_empty := by
    intro empty
    exact congrArg Fin.castSucc (spine.body_eq_root_of_empty empty)
  body_eq_terminal_of_nonempty := by
    intro nonempty
    exact congrArg Fin.castSucc
      (spine.body_eq_terminal_of_nonempty nonempty)
  proxy_region := by
    intro index
    have isProxy : ∃ candidate, spine.proxy index = spine.proxy candidate :=
      ⟨index, rfl⟩
    rw [show (vacuousWrapperDiagram pattern spine arity).regions
        (spine.proxy index).castSucc =
          liftCRegion 1 (pattern.diagram.regions (spine.proxy index)) by
      simp [vacuousWrapperDiagram, isProxy]]
    rw [spine.proxy_region index]
    split <;> rfl

def vacuousWrappedReplacement (input : Checked)
    (selection : CheckedSelection input.val) (arity : Nat) :
    Except Error (SelectionReplacement input selection) :=
  let base := extractedSelectionReplacementFor input selection selection
  let rawOpen := vacuousWrapperOpen base.pattern.val base.binderSpine arity
  match hcheck : checkWellFormed rawOpen.diagram with
  | .error error => .error (.resultNotWellFormed error)
  | .ok checked =>
      let pattern : CheckedOpen := ⟨rawOpen, {
        diagram_well_formed := by
          rw [← checkWellFormed_preserves_input hcheck]
          exact checked.property
        boundary_is_root_scoped :=
          vacuousWrapperBoundaryRootScoped base.pattern base.binderSpine arity
      }⟩
      .ok {
        pattern
        attachment := base.attachment
        attachment_consistent := base.attachment_consistent
        binderSpine := vacuousWrapperSpine base.pattern.val
          base.binderSpine arity
        binderTarget := base.binderTarget
      }


private def directContentsRequest (input : Concrete.Diagram)
    (container : Fin input.regionCount) : SelectionRequest input where
  anchor := container
  childRoots := filterFin fun region =>
    decide ((input.regions region).parent? = some container)
  directNodes := filterFin fun node =>
    decide ((input.nodes node).region = container)
  explicitWires := filterFin fun wire =>
    decide ((input.wires wire).scope = container)

private def singleChildRequest (input : Concrete.Diagram)
    (parent child : Fin input.regionCount) : SelectionRequest input where
  anchor := parent
  childRoots := [child]
  directNodes := []
  explicitWires := []

structure DoubleCutRecognition (input : Checked)
    (outer : Fin input.val.regionCount) where
  wrapper : CheckedSelection input.val
  body : CheckedSelection input.val

def recognizeDoubleCut (input : Checked)
    (outer : Fin input.val.regionCount) :
    Option (DoubleCutRecognition input outer) :=
  match input.val.regions outer with
  | .sheet | .bubble .. => none
  | .cut target =>
      let children := filterFin fun region =>
        decide ((input.val.regions region).parent? = some outer)
      match children with
      | [inner] =>
          match input.val.regions inner with
          | .cut parent =>
              if parent = outer &&
                  (filterFin fun node =>
                    decide ((input.val.nodes node).region = outer)).isEmpty &&
                  (filterFin fun wire =>
                    decide ((input.val.wires wire).scope = outer)).isEmpty then
                match checkSelection
                    (singleChildRequest input.val target outer) with
                | .error _ => none
                | .ok wrapper =>
                    match checkSelection
                        (directContentsRequest input.val inner) with
                    | .error _ => none
                    | .ok body => some { wrapper, body }
              else none
          | _ => none
      | _ => none

structure VacuousRecognition (input : Checked)
    (bubble : Fin input.val.regionCount) where
  wrapper : CheckedSelection input.val
  body : CheckedSelection input.val

def recognizeVacuous (input : Checked)
    (bubble : Fin input.val.regionCount) :
    Option (VacuousRecognition input bubble) :=
  match input.val.regions bubble with
  | .sheet | .cut .. => none
  | .bubble parent _ =>
      if (filterFin fun node =>
          match input.val.nodes node with
          | .atom _ binder => decide (binder = bubble)
          | _ => false).isEmpty then
        match checkSelection (singleChildRequest input.val parent bubble) with
        | .error _ => none
        | .ok wrapper =>
            match checkSelection (directContentsRequest input.val bubble) with
            | .error _ => none
            | .ok body => some { wrapper, body }
      else none


def applyDoubleCutIntro (input : Checked)
    (selection : CheckedSelection input.val) :
    Except Error (OperationReceipt input) :=
  match doubleCutWrappedReplacement input selection with
  | .error error => .error error
  | .ok replacement => replaceSelectionRaw input selection replacement

theorem applyDoubleCutIntro_composition
    (success : applyDoubleCutIntro input selection = .ok result) :
    ∃ replacement,
      doubleCutWrappedReplacement input selection = .ok replacement ∧
      replaceSelectionRaw input selection replacement = .ok result := by
  unfold applyDoubleCutIntro at success
  split at success <;> try contradiction
  exact ⟨_, ‹_›, success⟩

def applyDoubleCutElim (input : Checked)
    (outer : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  match recognizeDoubleCut input outer with
  | none => .error .operationRejected
  | some recognition =>
      replaceSelectionRaw input recognition.wrapper
        (extractedSelectionReplacementFor input recognition.body
          recognition.wrapper)

theorem applyDoubleCutElim_composition
    (success : applyDoubleCutElim input outer = .ok result) :
    ∃ recognition,
      recognizeDoubleCut input outer = some recognition ∧
      replaceSelectionRaw input recognition.wrapper
        (extractedSelectionReplacementFor input recognition.body
          recognition.wrapper) = .ok result := by
  unfold applyDoubleCutElim at success
  split at success <;> try contradiction
  exact ⟨_, ‹_›, success⟩

def applyVacuousIntro (input : Checked)
    (selection : CheckedSelection input.val) (arity : Nat) :
    Except Error (OperationReceipt input) :=
  match vacuousWrappedReplacement input selection arity with
  | .error error => .error error
  | .ok replacement => replaceSelectionRaw input selection replacement

theorem applyVacuousIntro_composition
    (success : applyVacuousIntro input selection arity = .ok result) :
    ∃ replacement,
      vacuousWrappedReplacement input selection arity = .ok replacement ∧
      replaceSelectionRaw input selection replacement = .ok result := by
  unfold applyVacuousIntro at success
  split at success <;> try contradiction
  exact ⟨_, ‹_›, success⟩

def applyVacuousElim (input : Checked)
    (bubble : Fin input.val.regionCount) :
    Except Error (OperationReceipt input) :=
  match recognizeVacuous input bubble with
  | none => .error .nonVacuousBinder
  | some recognition =>
      replaceSelectionRaw input recognition.wrapper
        (extractedSelectionReplacementFor input recognition.body
          recognition.wrapper)

theorem applyVacuousElim_composition
    (success : applyVacuousElim input bubble = .ok result) :
    ∃ recognition,
      recognizeVacuous input bubble = some recognition ∧
      replaceSelectionRaw input recognition.wrapper
        (extractedSelectionReplacementFor input recognition.body
          recognition.wrapper) = .ok result := by
  unfold applyVacuousElim at success
  split at success <;> try contradiction
  exact ⟨_, ‹_›, success⟩

end VisualProof.Concrete
