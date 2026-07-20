import VisualProof.Rule.Soundness.AttachmentAliasSemanticConcreteSimulation

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

@[simp] theorem collapseWire_rawBoundaryWire
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    collapseWire pattern attachment
        (rawBoundaryWire pattern attachment position) =
      pattern.boundary.get position := by
  unfold rawBoundaryWire
  cases found : aliasIndex? pattern attachment position with
  | none => simp
  | some aliasIndex =>
      rw [collapseWire_alias]
      rw [aliasIndex?_sound pattern attachment found]
      exact congrArg Prod.fst (pairOrigin_key pattern attachment position)

theorem collapseWire_mem_boundary_of_mem_rawBoundary
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin (pattern.diagram.wireCount + aliasCount pattern attachment))
    (member : wire ∈ (raw pattern attachment bodyContainer).boundary) :
    collapseWire pattern attachment wire ∈ pattern.boundary := by
  change wire ∈ List.ofFn (rawBoundaryWire pattern attachment) at member
  rw [List.mem_ofFn] at member
  obtain ⟨position, positionEq⟩ := member
  rw [← positionEq, collapseWire_rawBoundaryWire]
  exact List.get_mem pattern.boundary position

/-- The exposed target classes collapse onto source exposed classes, while
every source class has its canonical lifted-old representative. -/
noncomputable def exposedCollapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram) :
    ContextCollapse pattern attachment spine
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      pattern.val.exposedWires := by
  let target := raw pattern.val attachment spine.bodyContainer
  let indexMap : Fin target.exposedWires.length →
      Fin pattern.val.exposedWires.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete (by
      rw [OpenConcreteDiagram.mem_exposedWires]
      have targetMember : target.exposedWires.get index ∈ target.boundary :=
        (OpenConcreteDiagram.mem_exposedWires target _).mp
          (List.get_mem target.exposedWires index)
      exact collapseWire_mem_boundary_of_mem_rawBoundary pattern.val attachment
        spine.bodyContainer _ targetMember))
  let oldIndex : Fin pattern.val.exposedWires.length →
      Fin target.exposedWires.length := fun index =>
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete (by
      rw [OpenConcreteDiagram.mem_exposedWires]
      apply liftOldWire_mem_raw_boundary pattern.val attachment
        spine.bodyContainer
      exact (OpenConcreteDiagram.mem_exposedWires pattern.val _).mp
        (List.get_mem pattern.val.exposedWires index)))
  exact {
    indexMap := indexMap
    get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
          (by
            rw [OpenConcreteDiagram.mem_exposedWires]
            have targetMember : target.exposedWires.get index ∈ target.boundary :=
              (OpenConcreteDiagram.mem_exposedWires target _).mp
                (List.get_mem target.exposedWires index)
            exact collapseWire_mem_boundary_of_mem_rawBoundary pattern.val
              attachment spine.bodyContainer _ targetMember)))
    oldIndex := oldIndex
    old_get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
          (by
            rw [OpenConcreteDiagram.mem_exposedWires]
            apply liftOldWire_mem_raw_boundary pattern.val attachment
              spine.bodyContainer
            exact (OpenConcreteDiagram.mem_exposedWires pattern.val _).mp
              (List.get_mem pattern.val.exposedWires index))))
  }

noncomputable def rootCollapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature) :
    ContextCollapse pattern attachment spine
      (raw pattern.val attachment spine.bodyContainer).rootWires
      pattern.val.rootWires :=
  ContextCollapse.ofExact pattern attachment spine contract
    pattern.val.diagram.root
    (raw pattern.val attachment spine.bodyContainer).rootWires
    pattern.val.rootWires
    (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      ⟨raw pattern.val attachment spine.bodyContainer, {
        diagram_well_formed := targetWellFormed
        boundary_is_root_scoped := by
          exact (AttachmentAliasMaterialization.terminalBody pattern attachment
            spine contract).boundary_is_root_scoped
      }⟩)
    (ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      pattern)

def combinedOuterIndex (ambient locals : List α)
    (index : Fin ambient.length) : Fin (ambient ++ locals).length :=
  Fin.cast (by simp) (Fin.castAdd locals.length index)

def combinedLocalIndex (ambient locals : List α)
    (index : Fin locals.length) : Fin (ambient ++ locals).length :=
  Fin.cast (by simp) (Fin.natAdd ambient.length index)

@[simp] theorem combinedOuterIndex_get (ambient locals : List α)
    (index : Fin ambient.length) :
    (ambient ++ locals).get (combinedOuterIndex ambient locals index) =
      ambient.get index := by
  simp [combinedOuterIndex, List.get_eq_getElem, List.getElem_append_left]

@[simp] theorem combinedLocalIndex_get (ambient locals : List α)
    (index : Fin locals.length) :
    (ambient ++ locals).get (combinedLocalIndex ambient locals index) =
      locals.get index := by
  simp [combinedLocalIndex, List.get_eq_getElem, List.getElem_append_right]

@[simp] theorem rootEnvironment_combinedOuterIndex
    (ambient locals : ConcreteElaboration.WireContext diagram)
    (outer : Fin ambient.length → D) (localEnv : Fin locals.length → D)
    (index : Fin ambient.length) :
    ConcreteElaboration.rootEnvironment ambient locals outer localEnv
        (combinedOuterIndex ambient locals index) = outer index := by
  simp [ConcreteElaboration.rootEnvironment, combinedOuterIndex, extendWireEnv,
    Fin.addCases_left]

@[simp] theorem rootEnvironment_combinedLocalIndex
    (ambient locals : ConcreteElaboration.WireContext diagram)
    (outer : Fin ambient.length → D) (localEnv : Fin locals.length → D)
    (index : Fin locals.length) :
    ConcreteElaboration.rootEnvironment ambient locals outer localEnv
        (combinedLocalIndex ambient locals index) = localEnv index := by
  simp [ConcreteElaboration.rootEnvironment, combinedLocalIndex, extendWireEnv,
    Fin.addCases_right]

theorem rootCollapse_indexMap_outer
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (index : Fin
      (raw pattern.val attachment spine.bodyContainer).exposedWires.length) :
    (rootCollapse pattern attachment spine contract targetWellFormed).indexMap
        (combinedOuterIndex
          (raw pattern.val attachment spine.bodyContainer).exposedWires
          (raw pattern.val attachment spine.bodyContainer).hiddenWires index) =
      combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires
        ((exposedCollapse pattern attachment spine).indexMap index) := by
  apply Fin.ext
  have combinedGet := (rootCollapse pattern attachment spine contract
    targetWellFormed).get
      (combinedOuterIndex
        (raw pattern.val attachment spine.bodyContainer).exposedWires
        (raw pattern.val attachment spine.bodyContainer).hiddenWires index)
  have exposedGet := (exposedCollapse pattern attachment spine).get index
  have targetOuterGet :
      ((raw pattern.val attachment spine.bodyContainer).exposedWires ++
        (raw pattern.val attachment spine.bodyContainer).hiddenWires).get
          (combinedOuterIndex
            (raw pattern.val attachment spine.bodyContainer).exposedWires
            (raw pattern.val attachment spine.bodyContainer).hiddenWires index) =
        (raw pattern.val attachment spine.bodyContainer).exposedWires.get index :=
    combinedOuterIndex_get _ _ index
  have sourceOuterGet :
      (pattern.val.exposedWires ++ pattern.val.hiddenWires).get
          (combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires
            ((exposedCollapse pattern attachment spine).indexMap index)) =
        pattern.val.exposedWires.get
          ((exposedCollapse pattern attachment spine).indexMap index) :=
    combinedOuterIndex_get _ _ _
  simp only [OpenConcreteDiagram.rootWires] at combinedGet
  exact (List.getElem_inj pattern.val.rootWires_nodup).mp (by
    change (pattern.val.exposedWires ++ pattern.val.hiddenWires).get _ = _
    exact combinedGet.trans
      ((congrArg (collapseWire pattern.val attachment) targetOuterGet).trans
        (exposedGet.symm.trans sourceOuterGet.symm)))

theorem rootCollapse_oldIndex_outer
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (index : Fin pattern.val.exposedWires.length) :
    (rootCollapse pattern attachment spine contract targetWellFormed).oldIndex
        (combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires
          index) =
      combinedOuterIndex
        (raw pattern.val attachment spine.bodyContainer).exposedWires
        (raw pattern.val attachment spine.bodyContainer).hiddenWires
        ((exposedCollapse pattern attachment spine).oldIndex index) := by
  apply Fin.ext
  have combinedGet := (rootCollapse pattern attachment spine contract
    targetWellFormed).old_get
      (combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires index)
  have exposedGet := (exposedCollapse pattern attachment spine).old_get index
  have sourceOuterGet :
      (pattern.val.exposedWires ++ pattern.val.hiddenWires).get
          (combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires
            index) = pattern.val.exposedWires.get index :=
    combinedOuterIndex_get _ _ _
  have targetOuterGet :
      ((raw pattern.val attachment spine.bodyContainer).exposedWires ++
        (raw pattern.val attachment spine.bodyContainer).hiddenWires).get
          (combinedOuterIndex
            (raw pattern.val attachment spine.bodyContainer).exposedWires
            (raw pattern.val attachment spine.bodyContainer).hiddenWires
            ((exposedCollapse pattern attachment spine).oldIndex index)) =
        (raw pattern.val attachment spine.bodyContainer).exposedWires.get
          ((exposedCollapse pattern attachment spine).oldIndex index) :=
    combinedOuterIndex_get _ _ _
  simp only [OpenConcreteDiagram.rootWires] at combinedGet
  rw [sourceOuterGet] at combinedGet
  exact (List.getElem_inj
    (raw pattern.val attachment spine.bodyContainer).rootWires_nodup).mp (by
      change ((raw pattern.val attachment spine.bodyContainer).exposedWires ++
        (raw pattern.val attachment spine.bodyContainer).hiddenWires).get _ = _
      exact combinedGet.trans (exposedGet.symm.trans targetOuterGet.symm))

noncomputable def forwardTargetLocal
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (sourceOuter : Fin pattern.val.exposedWires.length → D)
    (sourceLocal : Fin pattern.val.hiddenWires.length → D) :
    Fin (raw pattern.val attachment spine.bodyContainer).hiddenWires.length → D :=
  fun index =>
    ConcreteElaboration.rootEnvironment pattern.val.exposedWires
      pattern.val.hiddenWires sourceOuter sourceLocal
      ((rootCollapse pattern attachment spine contract targetWellFormed).indexMap
        (combinedLocalIndex
          (raw pattern.val attachment spine.bodyContainer).exposedWires
          (raw pattern.val attachment spine.bodyContainer).hiddenWires index))

noncomputable def backwardSourceLocal
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (targetOuter : Fin
      (raw pattern.val attachment spine.bodyContainer).exposedWires.length → D)
    (targetLocal : Fin
      (raw pattern.val attachment spine.bodyContainer).hiddenWires.length → D) :
    Fin pattern.val.hiddenWires.length → D :=
  fun index =>
    ConcreteElaboration.rootEnvironment
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires
      targetOuter targetLocal
      ((rootCollapse pattern attachment spine contract targetWellFormed).oldIndex
        (combinedLocalIndex pattern.val.exposedWires pattern.val.hiddenWires
          index))

theorem forwardRootEnvironment_agrees
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (sourceOuter : Fin pattern.val.exposedWires.length → D)
    (targetOuter : Fin
      (raw pattern.val attachment spine.bodyContainer).exposedWires.length → D)
    (outerAgrees : sourceOuter ∘
        (exposedCollapse pattern attachment spine).indexMap = targetOuter)
    (sourceLocal : Fin pattern.val.hiddenWires.length → D) :
    ConcreteElaboration.rootEnvironment pattern.val.exposedWires
        pattern.val.hiddenWires sourceOuter sourceLocal ∘
        (rootCollapse pattern attachment spine contract targetWellFormed).indexMap =
      ConcreteElaboration.rootEnvironment
        (raw pattern.val attachment spine.bodyContainer).exposedWires
        (raw pattern.val attachment spine.bodyContainer).hiddenWires
        targetOuter
        (forwardTargetLocal pattern attachment spine contract targetWellFormed
          sourceOuter sourceLocal) := by
  funext index
  let split : Fin
      ((raw pattern.val attachment spine.bodyContainer).exposedWires.length +
        (raw pattern.val attachment spine.bodyContainer).hiddenWires.length) :=
    Fin.cast (show
      ((raw pattern.val attachment spine.bodyContainer).exposedWires ++
        (raw pattern.val attachment spine.bodyContainer).hiddenWires).length =
      _ from List.length_append) index
  have recover : Fin.cast (show
      _ = ((raw pattern.val attachment spine.bodyContainer).exposedWires ++
        (raw pattern.val attachment spine.bodyContainer).hiddenWires).length
      from List.length_append.symm) split =
      index := by apply Fin.ext; rfl
  rw [← recover]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) split
  · rw [show Fin.cast _ (Fin.castAdd _ outerIndex) =
        combinedOuterIndex
          (raw pattern.val attachment spine.bodyContainer).exposedWires
          (raw pattern.val attachment spine.bodyContainer).hiddenWires
          outerIndex by apply Fin.ext; rfl]
    simp only [Function.comp_apply]
    rw [rootCollapse_indexMap_outer, rootEnvironment_combinedOuterIndex,
      rootEnvironment_combinedOuterIndex]
    exact congrFun outerAgrees outerIndex
  · rw [show Fin.cast _ (Fin.natAdd _ localIndex) =
        combinedLocalIndex
          (raw pattern.val attachment spine.bodyContainer).exposedWires
          (raw pattern.val attachment spine.bodyContainer).hiddenWires
          localIndex by apply Fin.ext; rfl]
    simp only [Function.comp_apply]
    rw [rootEnvironment_combinedLocalIndex]
    rfl

theorem backwardRootEnvironment_agrees
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (sourceOuter : Fin pattern.val.exposedWires.length → D)
    (targetOuter : Fin
      (raw pattern.val attachment spine.bodyContainer).exposedWires.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘
      (exposedCollapse pattern attachment spine).oldIndex)
    (targetLocal : Fin
      (raw pattern.val attachment spine.bodyContainer).hiddenWires.length → D) :
    ConcreteElaboration.rootEnvironment pattern.val.exposedWires
        pattern.val.hiddenWires sourceOuter
        (backwardSourceLocal pattern attachment spine contract targetWellFormed
          targetOuter targetLocal) =
      ConcreteElaboration.rootEnvironment
        (raw pattern.val attachment spine.bodyContainer).exposedWires
        (raw pattern.val attachment spine.bodyContainer).hiddenWires
        targetOuter targetLocal ∘
        (rootCollapse pattern attachment spine contract targetWellFormed).oldIndex := by
  funext index
  let split : Fin
      (pattern.val.exposedWires.length + pattern.val.hiddenWires.length) :=
    Fin.cast (show
      (pattern.val.exposedWires ++ pattern.val.hiddenWires).length = _
      from List.length_append)
      index
  have recover : Fin.cast (show
      _ = (pattern.val.exposedWires ++ pattern.val.hiddenWires).length
      from List.length_append.symm)
      split =
      index := by apply Fin.ext; rfl
  rw [← recover]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) split
  · rw [show Fin.cast _ (Fin.castAdd _ outerIndex) =
        combinedOuterIndex pattern.val.exposedWires pattern.val.hiddenWires
          outerIndex by apply Fin.ext; rfl]
    simp only [Function.comp_apply]
    rw [rootCollapse_oldIndex_outer, rootEnvironment_combinedOuterIndex,
      rootEnvironment_combinedOuterIndex]
    exact congrFun outerAgrees outerIndex
  · rw [show Fin.cast _ (Fin.natAdd _ localIndex) =
        combinedLocalIndex pattern.val.exposedWires pattern.val.hiddenWires
          localIndex by apply Fin.ext; rfl]
    simp only [Function.comp_apply]
    rw [rootEnvironment_combinedLocalIndex]
    rfl

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
