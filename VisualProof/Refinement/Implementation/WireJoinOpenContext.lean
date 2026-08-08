import VisualProof.Refinement.Implementation.WireJoinPairedContext

namespace VisualProof.Refinement.Implementation.WireJoinOpenContext

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireJoin
open VisualProof.Refinement.Implementation.WireJoinPairedContext

noncomputable def nestedOuterEquiv
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    FiniteEquiv (Fin source.val.exposedWires.length)
      (Fin (targetOpenRaw source.val outer inner distinct).exposedWires.length) := {
  toFun := exposedMap source.val outer inner distinct
  invFun := fun targetIndex => Classical.choose
    (exposedMap_surjective source.val outer inner distinct targetIndex)
  left_inv := by
    intro sourceIndex
    apply exposedMap_injective_of_root_ne source outer inner distinct nested
    exact Classical.choose_spec
      (exposedMap_surjective source.val outer inner distinct
        (exposedMap source.val outer inner distinct sourceIndex))
  right_inv := by
    intro targetIndex
    exact Classical.choose_spec
      (exposedMap_surjective source.val outer inner distinct targetIndex)
}

noncomputable def nestedRootEquiv
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    FiniteEquiv (Fin source.val.rootWires.length)
      (Fin (targetOpenRaw source.val outer inner distinct).rootWires.length) := by
  let witness := rootWitness source outer inner distinct ordered
    targetWellFormed
  apply contextEquiv witness source.val.rootWires_nodup
  intro member
  have rootScope := (Concrete.OpenDiagram.rootWires_exact source.val
    source.property).mem_iff inner |>.1 member
  exact nested (Concrete.Elaboration.encloses_sheet_eq
    source.property.diagram_well_formed.root_is_sheet rootScope).symm

theorem nestedRootEquiv_exposed
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (index : Fin source.val.exposedWires.length) :
    nestedRootEquiv source outer inner distinct ordered targetWellFormed nested
        (leftIndex source.val.exposedWires source.val.hiddenWires index) =
      leftIndex
        (targetOpenRaw source.val outer inner distinct).exposedWires
        (targetOpenRaw source.val outer inner distinct).hiddenWires
        (nestedOuterEquiv source outer inner distinct nested index) := by
  apply Fin.ext
  simpa [nestedRootEquiv, nestedOuterEquiv, contextEquiv,
    Concrete.OpenDiagram.rootWires] using congrArg Fin.val
      (rootWitness_index_exposed source outer inner distinct ordered
        targetWellFormed index)

theorem nestedRootEquiv_hidden_ge
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (index : Fin source.val.hiddenWires.length) :
    (targetOpenRaw source.val outer inner distinct).exposedWires.length ≤
      (nestedRootEquiv source outer inner distinct ordered targetWellFormed
        nested (rightIndex source.val.exposedWires source.val.hiddenWires
          index)).val := by
  let rootEquiv := nestedRootEquiv source outer inner distinct ordered
    targetWellFormed nested
  let outerEquiv := nestedOuterEquiv source outer inner distinct nested
  apply Classical.byContradiction
  intro notGe
  have mappedLt :
      (rootEquiv (rightIndex source.val.exposedWires
        source.val.hiddenWires index)).val <
        (targetOpenRaw source.val outer inner distinct).exposedWires.length :=
    Nat.lt_of_not_ge notGe
  let targetIndex : Fin
      (targetOpenRaw source.val outer inner distinct).exposedWires.length :=
    ⟨_, mappedLt⟩
  let sourceIndex := outerEquiv.symm targetIndex
  have sourceIndexEq : outerEquiv sourceIndex = targetIndex :=
    outerEquiv.right_inv targetIndex
  have exposedEq := nestedRootEquiv_exposed source outer inner distinct
    ordered targetWellFormed nested sourceIndex
  have mappedEq :
      rootEquiv (leftIndex source.val.exposedWires source.val.hiddenWires
          sourceIndex) =
        rootEquiv (rightIndex source.val.exposedWires source.val.hiddenWires
          index) := by
    rw [exposedEq, sourceIndexEq]
    apply Fin.ext
    rfl
  have sourceEq := rootEquiv.injective mappedEq
  have values := congrArg Fin.val sourceEq
  simp [leftIndex, rightIndex] at values
  omega

noncomputable def nestedHiddenMap
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Fin source.val.hiddenWires.length →
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length :=
  fun index =>
    let mapped := nestedRootEquiv source outer inner distinct ordered
      targetWellFormed nested
        (rightIndex source.val.exposedWires source.val.hiddenWires index)
    ⟨mapped.val -
        (targetOpenRaw source.val outer inner distinct).exposedWires.length,
      by
        have mappedBound := mapped.isLt
        have rootLength :
            (targetOpenRaw source.val outer inner distinct).rootWires.length =
              (targetOpenRaw source.val outer inner distinct).exposedWires.length +
                (targetOpenRaw source.val outer inner distinct).hiddenWires.length := by
          simp [Concrete.OpenDiagram.rootWires]
        have mappedBound' : mapped.val <
            (targetOpenRaw source.val outer inner distinct).exposedWires.length +
              (targetOpenRaw source.val outer inner distinct).hiddenWires.length := by
          calc
            mapped.val <
                (targetOpenRaw source.val outer inner distinct).rootWires.length :=
              mappedBound
            _ = _ := rootLength
        have mappedGe := nestedRootEquiv_hidden_ge source outer inner distinct
          ordered targetWellFormed nested index
        omega⟩

theorem nestedRootEquiv_hidden
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (index : Fin source.val.hiddenWires.length) :
    nestedRootEquiv source outer inner distinct ordered targetWellFormed nested
        (rightIndex source.val.exposedWires source.val.hiddenWires index) =
      rightIndex
        (targetOpenRaw source.val outer inner distinct).exposedWires
        (targetOpenRaw source.val outer inner distinct).hiddenWires
        (nestedHiddenMap source outer inner distinct ordered targetWellFormed
          nested index) := by
  apply Fin.ext
  have ge := nestedRootEquiv_hidden_ge source outer inner distinct ordered
    targetWellFormed nested index
  change
    (nestedRootEquiv source outer inner distinct ordered targetWellFormed
      nested (rightIndex source.val.exposedWires source.val.hiddenWires
        index)).val =
      (targetOpenRaw source.val outer inner distinct).exposedWires.length +
        ((nestedRootEquiv source outer inner distinct ordered
          targetWellFormed nested
            (rightIndex source.val.exposedWires source.val.hiddenWires
              index)).val -
          (targetOpenRaw source.val outer inner distinct).exposedWires.length)
  exact (Nat.add_sub_of_le ge).symm

theorem nestedHiddenMap_injective
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Function.Injective
      (nestedHiddenMap source outer inner distinct ordered targetWellFormed
        nested) := by
  intro left right equality
  let rootEquiv := nestedRootEquiv source outer inner distinct ordered
    targetWellFormed nested
  have mapped :
      rootEquiv (rightIndex source.val.exposedWires source.val.hiddenWires
          left) =
        rootEquiv (rightIndex source.val.exposedWires source.val.hiddenWires
          right) := by
    rw [nestedRootEquiv_hidden, nestedRootEquiv_hidden, equality]
  have sourceEq := rootEquiv.injective mapped
  apply Fin.ext
  have values := congrArg Fin.val sourceEq
  simp [rightIndex] at values
  omega

theorem nestedHiddenMap_surjective
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Function.Surjective
      (nestedHiddenMap source outer inner distinct ordered targetWellFormed
        nested) := by
  intro targetIndex
  let rootEquiv := nestedRootEquiv source outer inner distinct ordered
    targetWellFormed nested
  let targetRootIndex := rightIndex
    (targetOpenRaw source.val outer inner distinct).exposedWires
    (targetOpenRaw source.val outer inner distinct).hiddenWires targetIndex
  let sourceRootIndex := rootEquiv.symm targetRootIndex
  have sourceGe : source.val.exposedWires.length ≤ sourceRootIndex.val := by
    apply Classical.byContradiction
    intro notGe
    have sourceLt : sourceRootIndex.val < source.val.exposedWires.length :=
      Nat.lt_of_not_ge notGe
    let sourceIndex : Fin source.val.exposedWires.length :=
      ⟨sourceRootIndex.val, sourceLt⟩
    have sourcePosition :
        leftIndex source.val.exposedWires source.val.hiddenWires sourceIndex =
          sourceRootIndex := by
      apply Fin.ext
      rfl
    have mapped := nestedRootEquiv_exposed source outer inner distinct ordered
      targetWellFormed nested sourceIndex
    rw [sourcePosition] at mapped
    have recovers : rootEquiv sourceRootIndex = targetRootIndex :=
      rootEquiv.right_inv targetRootIndex
    rw [recovers] at mapped
    have values := congrArg Fin.val mapped
    simp [leftIndex, rightIndex, targetRootIndex] at values
    omega
  have sourceBound : sourceRootIndex.val - source.val.exposedWires.length <
      source.val.hiddenWires.length := by
    have bound := sourceRootIndex.isLt
    have rootLength : source.val.rootWires.length =
        source.val.exposedWires.length + source.val.hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    have bound' : sourceRootIndex.val <
        source.val.exposedWires.length + source.val.hiddenWires.length := by
      calc
        sourceRootIndex.val < source.val.rootWires.length := bound
        _ = _ := rootLength
    omega
  let sourceIndex : Fin source.val.hiddenWires.length :=
    ⟨sourceRootIndex.val - source.val.exposedWires.length, sourceBound⟩
  have sourcePosition :
      rightIndex source.val.exposedWires source.val.hiddenWires sourceIndex =
        sourceRootIndex := by
    apply Fin.ext
    simp [rightIndex, sourceIndex]
    omega
  refine ⟨sourceIndex, ?_⟩
  have mapped := nestedRootEquiv_hidden source outer inner distinct ordered
    targetWellFormed nested sourceIndex
  rw [sourcePosition] at mapped
  have recovers : rootEquiv sourceRootIndex = targetRootIndex :=
    rootEquiv.right_inv targetRootIndex
  rw [recovers] at mapped
  apply Fin.ext
  have values := congrArg Fin.val mapped
  simp [rightIndex, targetRootIndex] at values
  omega

noncomputable def nestedLocalEquiv
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    FiniteEquiv (Fin source.val.hiddenWires.length)
      (Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length) := {
  toFun := nestedHiddenMap source outer inner distinct ordered targetWellFormed
    nested
  invFun := fun targetIndex => Classical.choose
    (nestedHiddenMap_surjective source outer inner distinct ordered
      targetWellFormed nested targetIndex)
  left_inv := by
    intro sourceIndex
    apply nestedHiddenMap_injective source outer inner distinct ordered
      targetWellFormed nested
    exact Classical.choose_spec (nestedHiddenMap_surjective source outer inner
      distinct ordered targetWellFormed nested
        (nestedHiddenMap source outer inner distinct ordered targetWellFormed
          nested sourceIndex))
  right_inv := by
    intro targetIndex
    exact Classical.choose_spec (nestedHiddenMap_surjective source outer inner
      distinct ordered targetWellFormed nested targetIndex)
}

noncomputable def openRootRawFrame
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    {child : Fin source.val.diagram.regionCount}
    {rest : List Nat}
    (childParent : (source.val.diagram.regions child).parent? =
      some source.val.diagram.root)
    (position : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram source.val.diagram.root).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences source.val.diagram
        source.val.diagram.root) (.child child) = some position)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      (source.val.diagram.wires inner).scope rest)
    {sourceBody : Region source.val.exposedWires.length []}
    {targetBody : Region
      (targetOpenRaw source.val outer inner distinct).exposedWires.length []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetState : Concrete.Splice.OpenRootCompilerState
      (targetOpen source outer inner distinct ordered targetWellFormed)
      targetBody)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndex : Fin targetState.items.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    ItemSeqIso.Frame
      (nestedRootEquiv source outer inner distinct ordered targetWellFormed
        nested) sourceIndex targetIndex := by
  let input := source.val.diagram
  let inputWellFormed := source.property.diagram_well_formed
  let region := input.root
  let target := targetOpen source outer inner distinct ordered
    targetWellFormed
  let sourceExtended := source.val.rootWires
  let targetExtended := (targetOpenRaw source.val outer inner distinct).rootWires
  let witness := rootWitness source outer inner distinct ordered
    targetWellFormed
  let extendedWitness := witness
  let extendedEquiv := nestedRootEquiv source outer inner distinct ordered
    targetWellFormed nested
  have extendedApply : ∀ index, extendedEquiv index =
      extendedWitness.indexMap index := by
    intro index
    rfl
  have sourceExact : Concrete.Elaboration.WireContext.Exact sourceExtended
      region := by
    simpa [sourceExtended, region, input] using
      Concrete.Elaboration.openRootWires_exact source.property
  have targetExact : Concrete.Elaboration.WireContext.Exact targetExtended
      region := by
    simpa [target, targetExtended, region, input, targetOpen, targetOpenRaw]
      using Concrete.Elaboration.openRootWires_exact target.property
  have bindersEq :
      (Concrete.Elaboration.BinderContext.empty :
        Concrete.Elaboration.BinderContext (Target input outer inner) []) =
      Concrete.Elaboration.BinderContext.empty := rfl
  have fuelEq : input.regionCount = input.regionCount := rfl
  have regionNe : region ≠ (input.wires inner).scope := by
    simpa [region, input] using nested
  let occurrences := Concrete.Elaboration.localOccurrences input region
  have targetComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (Concrete.Elaboration.compileRegion?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) input.regionCount)
        targetExtended Concrete.Elaboration.BinderContext.empty occurrences =
          some targetState.items := by
    simpa [target, targetOpen, targetOpenRaw, targetExtended, occurrences, input]
      using targetState.itemsComputation
  have sourceComputation :
      Concrete.Elaboration.compileOccurrencesWith? input
        (Concrete.Elaboration.compileRegion? input input.regionCount)
        sourceExtended Concrete.Elaboration.BinderContext.empty occurrences =
          some sourceState.items := by
    simpa [sourceExtended, occurrences, input] using sourceState.itemsComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input input.regionCount)
    sourceExtended Concrete.Elaboration.BinderContext.empty sourceComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) input.regionCount)
    targetExtended Concrete.Elaboration.BinderContext.empty targetComputation
  let positions : FiniteEquiv (Fin sourceState.items.length)
      (Fin targetState.items.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      (FiniteEquiv.finCast targetLength.symm)
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    simp [positions, sourceIndexVal, targetIndexVal, FiniteEquiv.finCast]
  refine {
    positions := positions
    mapped := mapped
    siblings := ?_
  }
  intro index indexNe
  let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
  have occurrenceNe : occurrenceIndex ≠ position := by
    intro equality
    apply indexNe
    apply Fin.ext
    have values := congrArg Fin.val equality
    simpa [occurrenceIndex, sourceIndexVal] using values
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input input.regionCount)
    sourceExtended Concrete.Elaboration.BinderContext.empty sourceComputation occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) input.regionCount)
    targetExtended Concrete.Elaboration.BinderContext.empty targetComputation occurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm occurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [sourcePosition] at sourceGet
  rw [targetPosition] at targetGet
  let occurrence := occurrences.get occurrenceIndex
  have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
  change Concrete.Elaboration.compileOccurrenceWith? input
      (Concrete.Elaboration.compileRegion? input input.regionCount)
      sourceExtended Concrete.Elaboration.BinderContext.empty occurrence =
        some (sourceState.items.get index) at sourceGet
  change Concrete.Elaboration.compileOccurrenceWith?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (Concrete.Elaboration.compileRegion?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) input.regionCount)
      targetExtended Concrete.Elaboration.BinderContext.empty occurrence =
        some (targetState.items.get (positions index)) at targetGet
  have regionEnclosesSite : input.Encloses region
      (input.wires inner).scope :=
    Concrete.Elaboration.checked_encloses_trans inputWellFormed
      (by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        change (match (input.regions child).parent? with
          | none => none
          | some directParent => input.climb 0 directParent) = some region
        rw [childParent]
        rfl)
      (Concrete.Splice.Input.RegionRoute.encloses tail inputWellFormed)
  have siteNotEnclosesRegion :
      ¬ input.Encloses (input.wires inner).scope region := by
    intro reverse
    exact regionNe (Concrete.Elaboration.checked_encloses_antisymm
      inputWellFormed regionEnclosesSite reverse)
  have siblingGeometry : ∀ sibling, occurrence = .child sibling →
      sibling ≠ child ∧
      ¬ input.Encloses (input.wires inner).scope sibling ∧
      ¬ input.Encloses sibling (input.wires inner).scope := by
    intro sibling siblingEq
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child input region
        sibling).1 (by
          rw [← siblingEq]
          exact occurrenceMem)
    have siblingNe : sibling ≠ child := by
      intro equality
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup input region)
        occurrenceIndex
      have same : some occurrenceIndex = some position := by
        rw [← found, ← positionEq]
        congr 1
      exact occurrenceNe (Option.some.inj same)
    have notAbove : ¬ input.Encloses sibling
        (input.wires inner).scope :=
      Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
        inputWellFormed tail childParent siblingParent siblingNe
    have notBelow : ¬ input.Encloses
        (input.wires inner).scope sibling := by
      intro siteSibling
      have childSite := Concrete.Splice.Input.RegionRoute.encloses tail
        inputWellFormed
      have childSibling := Concrete.Elaboration.checked_encloses_trans
        inputWellFormed childSite siteSibling
      rcases Concrete.Elaboration.encloses_direct_child siblingParent
          childSibling with equality | cycle
      · exact siblingNe equality.symm
      · exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          inputWellFormed childParent cycle
    exact ⟨siblingNe, notBelow, notAbove⟩
  cases occurrenceEq : occurrence with
  | node node =>
      rw [occurrenceEq] at sourceGet targetGet
      simp only [Concrete.Elaboration.compileOccurrenceWith?]
        at sourceGet targetGet
      have nodeRegion : (input.nodes node).region = region :=
        (Concrete.Elaboration.mem_localOccurrences_node input region node).1
          (by rw [← occurrenceEq]; exact occurrenceMem)
      have nodeMap := compileNode_map_away input inputWellFormed outer inner
        distinct ordered targetWellFormed region siteNotEnclosesRegion
        sourceExtended targetExtended extendedWitness sourceExact
        targetExact Concrete.Elaboration.BinderContext.empty node nodeRegion
      rw [sourceGet] at nodeMap
      have nodeMapTarget : Concrete.Elaboration.compileNode?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetExtended
          Concrete.Elaboration.BinderContext.empty node =
            some ((sourceState.items.get index).renameWires
              extendedWitness.indexMap) := by
        rw [bindersEq]
        simpa only [Option.map_some] using nodeMap
      have nodeMap' : some (targetState.items.get (positions index)) =
          some ((sourceState.items.get index).renameWires
            extendedWitness.indexMap) := by
        exact targetGet.symm.trans nodeMapTarget
      have itemEqWitness : targetState.items.get (positions index) =
          (sourceState.items.get index).renameWires
            extendedWitness.indexMap := Option.some.inj nodeMap'
      have renameEq :
          (sourceState.items.get index).renameWires
              extendedWitness.indexMap =
            (sourceState.items.get index).renameWires extendedEquiv := by
        apply congrArg (fun map =>
          (sourceState.items.get index).renameWires map)
        funext wireIndex
        exact (extendedApply wireIndex).symm
      have itemEq : targetState.items.get (positions index) =
          (sourceState.items.get index).renameWires extendedEquiv := by
        exact itemEqWitness.trans renameEq
      exact itemEq.symm ▸ ItemIso.renameWiresEquiv _ extendedEquiv
  | child sibling =>
      rw [occurrenceEq] at sourceGet targetGet
      obtain ⟨siblingNe, notBelow, notAbove⟩ :=
        siblingGeometry sibling occurrenceEq
      have siblingParent :=
        (Concrete.Elaboration.mem_localOccurrences_child input region
          sibling).1 (by rw [← occurrenceEq]; exact occurrenceMem)
      have targetSiblingParent :
          ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).regions sibling).parent? =
            some region := by
        simpa using siblingParent
      have sourceChildExact := sourceExact.extend_child
        inputWellFormed siblingParent
      have targetChildExact := targetExact.extend_child
        targetWellFormed targetSiblingParent
      have siblingNotSite : sibling ≠ (input.wires inner).scope := by
        intro equality
        subst sibling
        exact notBelow (Concrete.Diagram.Encloses.refl input _)
      cases siblingKind : input.regions sibling with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind]
            at sourceGet
      | cut parent =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
            VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
          cases sourceResultEq : Concrete.Elaboration.compileRegion? input
              input.regionCount sibling sourceExtended Concrete.Elaboration.BinderContext.empty with
          | none => simp [sourceResultEq] at sourceGet
          | some sourceBody =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  input.regionCount sibling targetExtended
                  Concrete.Elaboration.BinderContext.empty with
              | none =>
                  simp [targetResultEq] at targetGet
              | some targetBody =>
                  rw [sourceResultEq] at sourceGet
                  rw [targetResultEq] at targetGet
                  have sourceItemEq : sourceState.items.get index =
                      .cut sourceBody := Option.some.inj sourceGet |>.symm
                  have targetItemEq : targetState.items.get (positions index) =
                      .cut targetBody := Option.some.inj targetGet |>.symm
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      input.regionCount sibling targetExtended
                      Concrete.Elaboration.BinderContext.empty = some targetBody := by
                    simpa [fuelEq, bindersEq] using targetResultEq
                  have recursive := compileRegion_away input inputWellFormed
                    outer inner distinct ordered targetWellFormed input.regionCount
                    sibling siblingNotSite notBelow notAbove sourceExtended
                    targetExtended extendedWitness sourceChildExact
                    targetChildExact Concrete.Elaboration.BinderContext.empty sourceResultEq
                    targetResultEq'
                  have recursive' : RegionIso extendedEquiv [] sourceBody
                      targetBody := by
                    have renamed := RegionIso.renameWiresEquiv sourceBody
                      extendedEquiv
                    have aligned : sourceBody.renameWires extendedEquiv =
                        sourceBody.renameWires extendedWitness.indexMap := by
                      apply congrArg (fun map => Region.renameWires map sourceBody)
                      funext wireIndex
                      exact extendedApply wireIndex
                    exact renamed.trans (aligned ▸ recursive)
                  exact sourceItemEq.symm ▸ targetItemEq.symm ▸
                    ItemIso.cut recursive'
      | bubble parent arity =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
            VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
          let pushed := Concrete.Elaboration.BinderContext.empty.push sibling arity
          cases sourceResultEq : Concrete.Elaboration.compileRegion? input
              input.regionCount sibling sourceExtended pushed with
          | none => simp [pushed, sourceResultEq] at sourceGet
          | some sourceBody =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  input.regionCount sibling targetExtended
                  (Concrete.Elaboration.BinderContext.empty.push sibling arity) with
              | none =>
                  change (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                    input.regionCount sibling targetExtended
                    (Concrete.Elaboration.BinderContext.empty.push sibling
                      arity)).bind
                        (fun body => some (.bubble arity body)) =
                          some (targetState.items.get (positions index)) at targetGet
                  rw [targetResultEq] at targetGet
                  contradiction
              | some targetBody =>
                  change (Concrete.Elaboration.compileRegion? input
                    input.regionCount sibling sourceExtended pushed).bind _ =
                      some (sourceState.items.get index) at sourceGet
                  rw [sourceResultEq] at sourceGet
                  change (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                    input.regionCount sibling targetExtended
                    (Concrete.Elaboration.BinderContext.empty.push sibling
                      arity)).bind
                        (fun body => some (.bubble arity body)) =
                        some (targetState.items.get (positions index)) at targetGet
                  rw [targetResultEq] at targetGet
                  have sourceItemEq : sourceState.items.get index =
                      .bubble arity sourceBody :=
                    Option.some.inj sourceGet |>.symm
                  have targetItemEq : targetState.items.get (positions index) =
                      .bubble arity targetBody :=
                    Option.some.inj targetGet |>.symm
                  have pushedEq : Concrete.Elaboration.BinderContext.empty.push sibling arity =
                      pushed := by rfl
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      input.regionCount sibling targetExtended pushed =
                        some targetBody := by
                    simpa [fuelEq, pushedEq] using targetResultEq
                  have recursive := compileRegion_away input inputWellFormed
                    outer inner distinct ordered targetWellFormed input.regionCount
                    sibling siblingNotSite notBelow notAbove sourceExtended
                    targetExtended extendedWitness sourceChildExact
                    targetChildExact pushed sourceResultEq targetResultEq'
                  have recursive' : RegionIso extendedEquiv (arity :: [])
                      sourceBody targetBody := by
                    have renamed := RegionIso.renameWiresEquiv sourceBody
                      extendedEquiv
                    have aligned : sourceBody.renameWires extendedEquiv =
                        sourceBody.renameWires extendedWitness.indexMap := by
                      apply congrArg (fun map => Region.renameWires map sourceBody)
                      funext wireIndex
                      exact extendedApply wireIndex
                    exact renamed.trans (aligned ▸ recursive)
                  exact sourceItemEq.symm ▸ targetItemEq.symm ▸
                    ItemIso.bubble recursive'



theorem nestedRootEquiv_factor
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    let sourceCast : FiniteEquiv (Fin source.val.rootWires.length)
        (Fin (source.val.exposedWires.length + source.val.hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    let targetCast : FiniteEquiv
        (Fin (targetOpenRaw source.val outer inner distinct).rootWires.length)
        (Fin ((targetOpenRaw source.val outer inner distinct).exposedWires.length +
          (targetOpenRaw source.val outer inner distinct).hiddenWires.length)) :=
      FiniteEquiv.finCast (by simp [Concrete.OpenDiagram.rootWires])
    (sourceCast.symm.trans
      (nestedRootEquiv source outer inner distinct ordered targetWellFormed
        nested)).trans targetCast =
      extendWireEquiv
        (nestedOuterEquiv source outer inner distinct nested)
        (nestedLocalEquiv source outer inner distinct ordered targetWellFormed
          nested) := by
  dsimp only
  apply FiniteEquiv.ext
  intro index
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) index
  · apply Fin.ext
    have mapped := nestedRootEquiv_exposed source outer inner distinct ordered
      targetWellFormed nested exposed
    simpa [FiniteEquiv.finCast, extendWireEquiv, leftIndex,
      Concrete.OpenDiagram.rootWires] using congrArg Fin.val mapped
  · apply Fin.ext
    have mapped := nestedRootEquiv_hidden source outer inner distinct ordered
      targetWellFormed nested hidden
    simpa [FiniteEquiv.finCast, extendWireEquiv, rightIndex,
      nestedLocalEquiv, Concrete.OpenDiagram.rootWires] using
        congrArg Fin.val mapped

noncomputable def openRootFrameAssembly
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    {sourceLocal targetLocal : Nat}
    {sourceSeq : ItemSeq (source.val.exposedWires.length + sourceLocal) []}
    {targetSeq : ItemSeq
      ((targetOpenRaw source.val outer inner distinct).exposedWires.length +
        targetLocal) []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source
      (.mk sourceLocal sourceSeq))
    (targetState : Concrete.Splice.OpenRootCompilerState
      (targetOpen source outer inner distinct ordered targetWellFormed)
      (.mk targetLocal targetSeq))
    (sourceLocalCanonical : sourceLocal = source.val.hiddenWires.length)
    (targetLocalCanonical : targetLocal =
      (targetOpenRaw source.val outer inner distinct).hiddenWires.length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    {sourceIndex : Fin sourceState.items.length}
    {targetIndex : Fin targetState.items.length}
    (rawFrame : ItemSeqIso.Frame
      (nestedRootEquiv source outer inner distinct ordered targetWellFormed
        nested) sourceIndex targetIndex) :
    ItemSeqIso.Frame.Indexed sourceSeq targetSeq
      (extendWireEquiv
        (nestedOuterEquiv source outer inner distinct nested)
        ((FiniteEquiv.finCast sourceLocalCanonical).trans
          ((nestedLocalEquiv source outer inner distinct ordered
            targetWellFormed nested).trans
            (FiniteEquiv.finCast targetLocalCanonical.symm))))
      sourceIndex.val targetIndex.val := by
  subst sourceLocal
  subst targetLocal
  let sourceEq : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let targetEq :
      (targetOpenRaw source.val outer inner distinct).rootWires.length =
        (targetOpenRaw source.val outer inner distinct).exposedWires.length +
          (targetOpenRaw source.val outer inner distinct).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let firstWire := FiniteEquiv.finCast sourceEq.symm
  let middleWire := nestedRootEquiv source outer inner distinct ordered
    targetWellFormed nested
  let lastWire := FiniteEquiv.finCast targetEq
  let finalWire := extendWireEquiv
    (nestedOuterEquiv source outer inner distinct nested)
    (nestedLocalEquiv source outer inner distinct ordered targetWellFormed
      nested)
  have sourcePull : sourceSeq.renameWires firstWire = sourceState.items := by
    have canonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    conv =>
      lhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    calc
      _ = sourceState.items.renameWires
          (firstWire.toFun ∘ Fin.cast sourceEq) :=
        ItemSeq.renameWires_comp sourceState.items (Fin.cast sourceEq)
          firstWire
      _ = sourceState.items := by
        have identity : firstWire.toFun ∘ Fin.cast sourceEq = id := by
          funext index
          apply Fin.ext
          rfl
        rw [identity]
        exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires lastWire = targetSeq := by
    have canonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    conv =>
      rhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    rfl
  have wireFactor : (firstWire.trans middleWire).trans lastWire =
      finalWire := by
    simpa [firstWire, middleWire, lastWire, finalWire] using
      nestedRootEquiv_factor source outer inner distinct ordered
        targetWellFormed nested
  simpa only [finalWire] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire finalWire
      sourcePull targetPush wireFactor rawFrame

structure OpenCompilerTraceAlignment
    {sourceOuter targetOuter : Nat}
    {rels : Theory.RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath) where
  alignment : Concrete.Splice.Input.PairedCompilerContextAlignment outerWire
    sourceWitness targetWitness
  before : Region targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  after : Region targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  rewrite : Rule.WireSever.Local before after
  target_iso : RegionIso
    (FiniteEquiv.refl (Fin targetWitness.toFocus.holeWires))
    targetWitness.toFocus.holeRels targetWitness.toFocus.body before
  source_iso : RegionIso alignment.holeWire sourceWitness.toFocus.holeRels
    sourceWitness.toFocus.body (alignment.holeRelsEq.symm ▸ after)

theorem rootRouteChildrenEq
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (targetWellFormed : (Target input outer inner).WellFormed)
    {sourceChild targetChild : Fin input.regionCount}
    {sourceRest targetRest : List Nat}
    (sourceParent : (input.regions sourceChild).parent? = some input.root)
    (targetParent : ((Target input outer inner).regions targetChild).parent? =
      some input.root)
    (sourceTail : Concrete.Splice.RegionRoute input sourceChild
      (input.wires inner).scope sourceRest)
    (targetTail : Concrete.Splice.RegionRoute (Target input outer inner)
      targetChild (input.wires inner).scope targetRest) :
    sourceChild = targetChild := by
  have sourceEncloses : input.Encloses sourceChild
      (input.wires inner).scope :=
    Concrete.Splice.Input.RegionRoute.encloses sourceTail inputWellFormed
  have targetEncloses : input.Encloses targetChild
      (input.wires inner).scope := by
    rw [← target_encloses_iff input outer inner]
    exact Concrete.Splice.Input.RegionRoute.encloses targetTail
      targetWellFormed
  have targetParent' : (input.regions targetChild).parent? = some input.root := by
    simpa only [target_regions] using targetParent
  rcases Concrete.Diagram.enclosingRegions_comparable sourceEncloses
      targetEncloses with sourceTarget | targetSource
  · rcases Concrete.Elaboration.encloses_direct_child targetParent'
        sourceTarget with equality | cycle
    · exact equality
    · exact False.elim
        (Concrete.Elaboration.checked_direct_child_not_encloses_parent
          inputWellFormed sourceParent cycle)
  · rcases Concrete.Elaboration.encloses_direct_child sourceParent
        targetSource with equality | cycle
    · exact equality.symm
    · exact False.elim
        (Concrete.Elaboration.checked_direct_child_not_encloses_parent
          inputWellFormed targetParent' cycle)

noncomputable def openCompilerTraceContextIso
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    {sourceEnd targetEnd : Fin source.val.diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceBody : Region source.val.exposedWires.length []}
    {targetBody : Region
      (targetOpenRaw source.val outer inner distinct).exposedWires.length []}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram
      source.val.diagram.root sourceEnd sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute
      (Target source.val.diagram outer inner) source.val.diagram.root
      targetEnd targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetState : Concrete.Splice.OpenRootCompilerState
      (targetOpen source outer inner distinct ordered targetWellFormed)
      targetBody)
    (sourceTrace : Concrete.Splice.OpenCompilerTrace source sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.OpenCompilerTrace
      (targetOpen source outer inner distinct ordered targetWellFormed)
      targetRoute targetWitness targetState)
    (sourceEndEq : sourceEnd = (source.val.diagram.wires inner).scope)
    (targetEndEq : targetEnd = (source.val.diagram.wires inner).scope) :
    OpenCompilerTraceAlignment
      (nestedOuterEquiv source outer inner distinct nested)
      sourceWitness targetWitness := by
  refine @Concrete.Splice.OpenCompilerTrace.rec
    (checked := targetOpen source outer inner distinct ordered targetWellFormed)
    (motive := fun {currentEnd} {currentPath} {currentBody} currentRoute
      currentWitness currentState currentTrace =>
        (currentEndEq : currentEnd =
          (source.val.diagram.wires inner).scope) →
        OpenCompilerTraceAlignment
          (nestedOuterEquiv source outer inner distinct nested)
          sourceWitness currentWitness) ?_ ?_ ?_ _ _ _ _ _ _ targetTrace
            targetEndEq
  case refine_1 =>
      intro currentBody currentState currentEndEq
      exact False.elim (nested currentEndEq)
  case refine_2 =>
      intro targetChild currentEnd targetRest targetParent targetPosition
        targetPositionEq targetTail targetLocal targetSeq targetFocus
        targetChildBody targetAt targetIsCut targetNested targetState
        targetLocalCanonical targetItemsCanonical targetChildState
        targetChildKind targetInherited targetBinders targetFuel
        targetTailTrace currentEndEq
      subst currentEnd
      cases sourceTrace with
      | here sourceState =>
          exact False.elim (nested sourceEndEq)
      | @bubble sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
          sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical
          sourceChildState sourceChildKind sourceInherited sourceBinders
          sourceFuel sourceTailTrace =>
          subst sourceEnd
          have childrenEq := rootRouteChildrenEq source.val.diagram
            source.property.diagram_well_formed outer inner targetWellFormed
            sourceParent targetParent sourceTail targetTail
          subst targetChild
          have targetChildKind' : source.val.diagram.regions sourceChild =
              .cut source.val.diagram.root := by
            simpa only [target_regions] using targetChildKind
          have impossible := sourceChildKind.symm.trans targetChildKind'
          contradiction
      | @cut sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
          sourceChildBody sourceAt sourceIsCut sourceNested sourceState
          sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          subst sourceEnd
          have childrenEq := rootRouteChildrenEq source.val.diagram
            source.property.diagram_well_formed outer inner targetWellFormed
            sourceParent targetParent sourceTail targetTail
          subst targetChild
          let root := rootWitness source outer inner distinct ordered
            targetWellFormed
          let childWitness := contextWitnessCast root sourceInherited
            targetInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans sourceBinders.symm
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by
            have targetFuel' : targetChildState.fuel + 1 =
                source.val.diagram.regionCount := by
              simpa [targetOpen, targetOpenRaw] using targetFuel
            omega
          let childResult := compilerTraceContextIso source.val.diagram
            source.property.diagram_well_formed outer inner distinct ordered
            targetWellFormed rfl sourceChildState targetChildState
            sourceTailTrace targetTailTrace childWitness childBindersEq
            childFuelEq
          have targetPositionEq' : indexOf?
              (Concrete.Elaboration.localOccurrences source.val.diagram
                source.val.diagram.root) (.child sourceChild) =
                some targetPosition := by
            simpa only [target_localOccurrences] using targetPositionEq
          have positionsEq : targetPosition = sourcePosition :=
            Option.some.inj (targetPositionEq'.symm.trans sourcePositionEq)
          have positionVals : targetPosition.val = sourcePosition.val :=
            congrArg Fin.val positionsEq
          let sourceItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion? source.val.diagram
                source.val.diagram.regionCount)
              source.val.rootWires Concrete.Elaboration.BinderContext.empty
              sourceState.itemsComputation
          let targetItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion?
                (Target source.val.diagram outer inner)
                source.val.diagram.regionCount)
              (targetOpenRaw source.val outer inner distinct).rootWires
              Concrete.Elaboration.BinderContext.empty
              targetState.itemsComputation
          let sourceIndex : Fin sourceState.items.length :=
            Fin.cast sourceItemsLength.symm sourcePosition
          let targetIndex : Fin targetState.items.length :=
            Fin.cast targetItemsLength.symm targetPosition
          let rawFrame := openRootRawFrame source outer inner distinct
            ordered targetWellFormed nested sourceParent sourcePosition
            sourcePositionEq sourceTail sourceState targetState sourceIndex
            targetIndex (by simp [sourceIndex])
            (by simpa [targetIndex] using positionVals)
          obtain ⟨sourceIndex', targetIndex', sourceIndexVal,
              targetIndexVal, frame⟩ :=
            openRootFrameAssembly source outer inner distinct ordered
              targetWellFormed nested sourceState targetState
              sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
              targetItemsCanonical rawFrame
          have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have value : sourceIndex'.val = sourcePosition.val := by
              simpa [sourceIndex] using sourceIndexVal
            simpa [value] using sourceAt
          have targetAt' : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have value : targetIndex'.val = targetPosition.val := by
              simpa [targetIndex] using targetIndexVal
            simpa [value] using targetAt
          have sourceNodup : sourceChildState.inheritedWires.Nodup := by
            rw [sourceInherited]
            exact source.val.rootWires_nodup
          have innerAbsent : inner ∉ sourceChildState.inheritedWires := by
            rw [sourceInherited]
            intro member
            have scope := (Concrete.OpenDiagram.rootWires_exact source.val
              source.property).mem_iff inner |>.1 member
            exact nested (Concrete.Elaboration.encloses_sheet_eq
              source.property.diagram_well_formed.root_is_sheet scope).symm
          let childInherited := contextEquiv childWitness sourceNodup
            innerAbsent
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let expectedChild :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              ((nestedRootEquiv source outer inner distinct ordered
                targetWellFormed nested).trans
                (FiniteEquiv.finCast targetLengthEq.symm))
          have childInheritedEq : childInherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := contextWitnessCast_indexMap root sourceInherited
              targetInherited index
            have castEq :
                Fin.cast (congrArg List.length sourceInherited) index =
                  Fin.cast sourceLengthEq index := by
              apply Fin.ext
              rfl
            simpa [childInherited, expectedChild, nestedRootEquiv,
              contextEquiv, FiniteEquiv.finCast, castEq] using
                congrArg Fin.val spec
          subst sourceLocal
          subst targetLocal
          let localWire := nestedLocalEquiv source outer inner distinct ordered
            targetWellFormed nested
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire sourceChildState
                targetChildState childInherited =
              extendWireEquiv
                (nestedOuterEquiv source outer inner distinct nested)
                localWire := by
            rw [childInheritedEq]
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have factor := nestedRootEquiv_factor source outer inner distinct
              ordered targetWellFormed nested
            simpa [Concrete.Splice.Input.compilerBodyOuterWire,
              expectedChild, localWire, FiniteEquiv.finCast] using
                congrArg (fun equivalence => (equivalence index).val) factor
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (nestedOuterEquiv source outer inner distinct nested)
                localWire)
              childResult.holeWire [] sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.cut
                    (targetOpenRaw source.val outer inner distinct).hiddenWires.length
                    targetFocus.before targetFocus.after
                    targetNested.toFocus.context =
                DiagramContext.cut
                  (targetOpenRaw source.val outer inner distinct).hiddenWires.length
                  targetFocus.before targetFocus.after
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childResult.holeRelsEq targetFocus.before targetFocus.after
                targetNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame
            (outerWire := nestedOuterEquiv source outer inner distinct nested)
            (holeWire := childResult.holeWire)
            (sourceChild := sourceNested.toFocus.context)
            (targetChild := childResult.holeRelsEq.symm ▸
              targetNested.toFocus.context) localWire sourceFocus targetFocus
            sourceAt' targetAt' frame childContexts
          exact {
            alignment := {
              holeRelsEq := childResult.holeRelsEq
              holeWire := childResult.holeWire
              contexts := by
                simpa only [Region.ContextPath.toFocus] using
                  (targetContextTransport.symm ▸ cutContexts)
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            target_iso := childResult.target_iso
            source_iso := childResult.source_iso
          }
  case refine_3 =>
      intro targetChild currentEnd targetRest targetParent targetPosition
        targetPositionEq targetTail targetLocal targetArity targetSeq
        targetFocus targetChildBody targetAt targetIsBubble targetNested
        targetState targetLocalCanonical targetItemsCanonical targetChildState
        targetChildKind targetInherited targetBinders targetFuel
        targetTailTrace currentEndEq
      subst currentEnd
      cases sourceTrace with
      | here sourceState =>
          exact False.elim (nested sourceEndEq)
      | @cut sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
          sourceChildBody sourceAt sourceIsCut sourceNested sourceState
          sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          subst sourceEnd
          have childrenEq := rootRouteChildrenEq source.val.diagram
            source.property.diagram_well_formed outer inner targetWellFormed
            sourceParent targetParent sourceTail targetTail
          subst targetChild
          have targetChildKind' : source.val.diagram.regions sourceChild =
              .bubble source.val.diagram.root targetArity := by
            simpa only [target_regions] using targetChildKind
          have impossible := sourceChildKind.symm.trans targetChildKind'
          contradiction
      | @bubble sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
          sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical
          sourceChildState sourceChildKind sourceInherited sourceBinders
          sourceFuel sourceTailTrace =>
          subst sourceEnd
          have childrenEq := rootRouteChildrenEq source.val.diagram
            source.property.diagram_well_formed outer inner targetWellFormed
            sourceParent targetParent sourceTail targetTail
          subst targetChild
          have targetChildKind' : source.val.diagram.regions sourceChild =
              .bubble source.val.diagram.root targetArity := by
            simpa only [target_regions] using targetChildKind
          have aritiesEq : sourceArity = targetArity := by
            have same := sourceChildKind.symm.trans targetChildKind'
            injection same
          subst targetArity
          let root := rootWitness source outer inner distinct ordered
            targetWellFormed
          let childWitness := contextWitnessCast root sourceInherited
            targetInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans sourceBinders.symm
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by
            have targetFuel' : targetChildState.fuel + 1 =
                source.val.diagram.regionCount := by
              simpa [targetOpen, targetOpenRaw] using targetFuel
            omega
          let childResult := compilerTraceContextIso source.val.diagram
            source.property.diagram_well_formed outer inner distinct ordered
            targetWellFormed rfl sourceChildState targetChildState
            sourceTailTrace targetTailTrace childWitness childBindersEq
            childFuelEq
          have targetPositionEq' : indexOf?
              (Concrete.Elaboration.localOccurrences source.val.diagram
                source.val.diagram.root) (.child sourceChild) =
                some targetPosition := by
            simpa only [target_localOccurrences] using targetPositionEq
          have positionsEq : targetPosition = sourcePosition :=
            Option.some.inj (targetPositionEq'.symm.trans sourcePositionEq)
          have positionVals : targetPosition.val = sourcePosition.val :=
            congrArg Fin.val positionsEq
          let sourceItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion? source.val.diagram
                source.val.diagram.regionCount)
              source.val.rootWires Concrete.Elaboration.BinderContext.empty
              sourceState.itemsComputation
          let targetItemsLength :=
            Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion?
                (Target source.val.diagram outer inner)
                source.val.diagram.regionCount)
              (targetOpenRaw source.val outer inner distinct).rootWires
              Concrete.Elaboration.BinderContext.empty
              targetState.itemsComputation
          let sourceIndex : Fin sourceState.items.length :=
            Fin.cast sourceItemsLength.symm sourcePosition
          let targetIndex : Fin targetState.items.length :=
            Fin.cast targetItemsLength.symm targetPosition
          let rawFrame := openRootRawFrame source outer inner distinct
            ordered targetWellFormed nested sourceParent sourcePosition
            sourcePositionEq sourceTail sourceState targetState sourceIndex
            targetIndex (by simp [sourceIndex])
            (by simpa [targetIndex] using positionVals)
          obtain ⟨sourceIndex', targetIndex', sourceIndexVal,
              targetIndexVal, frame⟩ :=
            openRootFrameAssembly source outer inner distinct ordered
              targetWellFormed nested sourceState targetState
              sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
              targetItemsCanonical rawFrame
          have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
              some sourceFocus := by
            have value : sourceIndex'.val = sourcePosition.val := by
              simpa [sourceIndex] using sourceIndexVal
            simpa [value] using sourceAt
          have targetAt' : targetSeq.focusAt? targetIndex'.val =
              some targetFocus := by
            have value : targetIndex'.val = targetPosition.val := by
              simpa [targetIndex] using targetIndexVal
            simpa [value] using targetAt
          have sourceNodup : sourceChildState.inheritedWires.Nodup := by
            rw [sourceInherited]
            exact source.val.rootWires_nodup
          have innerAbsent : inner ∉ sourceChildState.inheritedWires := by
            rw [sourceInherited]
            intro member
            have scope := (Concrete.OpenDiagram.rootWires_exact source.val
              source.property).mem_iff inner |>.1 member
            exact nested (Concrete.Elaboration.encloses_sheet_eq
              source.property.diagram_well_formed.root_is_sheet scope).symm
          let childInherited := contextEquiv childWitness sourceNodup
            innerAbsent
          let sourceLengthEq := congrArg List.length sourceInherited
          let targetLengthEq := congrArg List.length targetInherited
          let expectedChild :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              ((nestedRootEquiv source outer inner distinct ordered
                targetWellFormed nested).trans
                (FiniteEquiv.finCast targetLengthEq.symm))
          have childInheritedEq : childInherited = expectedChild := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have spec := contextWitnessCast_indexMap root sourceInherited
              targetInherited index
            have castEq :
                Fin.cast (congrArg List.length sourceInherited) index =
                  Fin.cast sourceLengthEq index := by
              apply Fin.ext
              rfl
            simpa [childInherited, expectedChild, nestedRootEquiv,
              contextEquiv, FiniteEquiv.finCast, castEq] using
                congrArg Fin.val spec
          subst sourceLocal
          subst targetLocal
          let localWire := nestedLocalEquiv source outer inner distinct ordered
            targetWellFormed nested
          have childOuter :
              Concrete.Splice.Input.compilerBodyOuterWire sourceChildState
                targetChildState childInherited =
              extendWireEquiv
                (nestedOuterEquiv source outer inner distinct nested)
                localWire := by
            rw [childInheritedEq]
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have factor := nestedRootEquiv_factor source outer inner distinct
              ordered targetWellFormed nested
            simpa [Concrete.Splice.Input.compilerBodyOuterWire,
              expectedChild, localWire, FiniteEquiv.finCast] using
                congrArg (fun equivalence => (equivalence index).val) factor
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (nestedOuterEquiv source outer inner distinct nested)
                localWire)
              childResult.holeWire (sourceArity :: [])
              sourceNested.toFocus.holeRels sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.bubble
                    (targetOpenRaw source.val outer inner distinct).hiddenWires.length
                    targetFocus.before targetFocus.after sourceArity
                    targetNested.toFocus.context =
                DiagramContext.bubble
                  (targetOpenRaw source.val outer inner distinct).hiddenWires.length
                  targetFocus.before targetFocus.after sourceArity
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childResult.holeRelsEq targetFocus.before targetFocus.after
                targetNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame
            (outerWire := nestedOuterEquiv source outer inner distinct nested)
            (holeWire := childResult.holeWire)
            (sourceChild := sourceNested.toFocus.context)
            (targetChild := childResult.holeRelsEq.symm ▸
              targetNested.toFocus.context) localWire sourceFocus targetFocus
            sourceAt' targetAt' frame childContexts
          exact {
            alignment := {
              holeRelsEq := childResult.holeRelsEq
              holeWire := childResult.holeWire
              contexts := by
                simpa only [Region.ContextPath.toFocus] using
                  (targetContextTransport.symm ▸ bubbleContexts)
            }
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            target_iso := childResult.target_iso
            source_iso := childResult.source_iso
          }

noncomputable def openSiteContextIso
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceView : Concrete.Splice.OpenSiteView source
      (source.val.diagram.wires inner).scope)
    (targetView : Concrete.Splice.OpenSiteView
      (targetOpen source outer inner distinct ordered targetWellFormed)
      (source.val.diagram.wires inner).scope) :
    OpenCompilerTraceAlignment
      (nestedOuterEquiv source outer inner distinct nested)
      sourceView.intrinsicPath targetView.intrinsicPath := by
  exact openCompilerTraceContextIso source outer inner distinct ordered
    targetWellFormed nested sourceView.result.state targetView.result.state
      sourceView.result.trace targetView.result.trace rfl rfl

end VisualProof.Refinement.Implementation.WireJoinOpenContext
