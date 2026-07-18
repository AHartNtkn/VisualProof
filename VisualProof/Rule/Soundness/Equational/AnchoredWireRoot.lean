import VisualProof.Rule.Soundness.Equational.AnchoredWireRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

private theorem anchored_eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinjective : Function.Injective f) :
    ∀ values : List α, (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← anchored_eraseDups_map_injective f hinjective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      apply Bool.eq_iff_iff.mpr
      simp [hinjective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

/-- The exact ordered-open result of anchored wire splitting.  Only old wire
identities may occur at the serialized boundary; the fresh factor wire is
internal. -/
def anchoredWireSplitSourceOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def anchoredWireSplitRawOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    OpenConcreteDiagram where
  diagram := anchoredWireSplitRaw input wire endpoints target term
  boundary := boundary.map (Fin.castAdd 1)

theorem anchoredWireSplitRawOpen_exposedWires
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target term).exposedWires =
      (anchoredWireSplitSourceOpen input boundary).exposedWires.map
        (Fin.castAdd 1) := by
  unfold anchoredWireSplitRawOpen OpenConcreteDiagram.exposedWires
  have hinjective : Function.Injective
      (Fin.castAdd 1 : Fin input.val.wireCount → Fin (input.val.wireCount + 1)) :=
    by
      intro left right equality
      apply Fin.ext
      exact congrArg (fun value : Fin (input.val.wireCount + 1) => value.val)
        equality
  simpa [anchoredWireSplitSourceOpen] using
    anchored_eraseDups_map_injective (Fin.castAdd 1) hinjective boundary

theorem anchoredWireSplitRawOpen_hiddenWires
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target term).hiddenWires =
      (anchoredWireSplitSourceOpen input boundary).hiddenWires.map
          (Fin.castAdd 1 : Fin input.val.wireCount →
            Fin (input.val.wireCount + 1)) ++
        if input.val.root = target then
          [Fin.last input.val.wireCount]
        else [] := by
  let source := anchoredWireSplitSourceOpen input boundary
  unfold OpenConcreteDiagram.hiddenWires
  change List.filter
      (fun candidate => decide
        (candidate ∉
          (anchoredWireSplitRawOpen input boundary wire endpoints target term).exposedWires))
      (ConcreteElaboration.exactScopeWires
        (anchoredWireSplitRaw input wire endpoints target term) input.val.root) = _
  rw [anchoredWireSplitRaw_exactScopeWires,
    anchoredWireSplitRawOpen_exposedWires]
  have hold :
      List.filter
          (fun candidate => decide
            (candidate ∉ source.exposedWires.map (Fin.castAdd 1)))
          ((ConcreteElaboration.exactScopeWires input.val input.val.root).map
            (Fin.castAdd 1)) =
        source.hiddenWires.map (Fin.castAdd 1) := by
    unfold OpenConcreteDiagram.hiddenWires
    rw [List.filter_map]
    apply congrArg (List.map (Fin.castAdd 1))
    apply congrArg (fun predicate => List.filter predicate
      (ConcreteElaboration.exactScopeWires input.val input.val.root))
    funext candidate
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro notMapped member
      exact notMapped (List.mem_map.mpr ⟨candidate, member, rfl⟩)
    · intro notSource mapped
      rcases List.mem_map.mp mapped with ⟨old, oldMember, equality⟩
      have oldEq : old = candidate := by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.val.wireCount + 1) => value.val) equality
      exact notSource (by simpa [oldEq] using oldMember)
  by_cases atRoot : input.val.root = target
  · simp only [if_pos atRoot]
    have split := List.filter_append
      (p := fun candidate => decide
        (candidate ∉ source.exposedWires.map (Fin.castAdd 1)))
      ((ConcreteElaboration.exactScopeWires input.val input.val.root).map
        (Fin.castAdd 1))
      ((allFin 1).map (Fin.natAdd input.val.wireCount))
    apply Eq.trans split
    rw [hold]
    congr 1
    have freshNot : Fin.last input.val.wireCount ∉
        source.exposedWires.map (Fin.castAdd 1) := by
      intro exposed
      rcases List.mem_map.mp exposed with ⟨old, _, equality⟩
      have values := congrArg
        (fun value : Fin (input.val.wireCount + 1) => value.val) equality
      simp at values
      have oldLt : old.val < input.val.wireCount := by
        simpa [source, anchoredWireSplitSourceOpen] using old.isLt
      omega
    have suffix : (allFin 1).map (Fin.natAdd input.val.wireCount) =
        [Fin.last input.val.wireCount] := by
      simp [allFin_eq_finRange]
      constructor
      · rfl
      · apply Fin.ext
        rfl
    calc
      List.filter
          (fun candidate => decide
            (candidate ∉ source.exposedWires.map (Fin.castAdd 1)))
          ((allFin 1).map (Fin.natAdd input.val.wireCount)) =
          List.filter
            (fun candidate => decide
              (candidate ∉ source.exposedWires.map (Fin.castAdd 1)))
            [Fin.last input.val.wireCount] :=
        congrArg (List.filter (fun candidate => decide
          (candidate ∉ source.exposedWires.map (Fin.castAdd 1)))) suffix
      _ = [Fin.last input.val.wireCount] := by
        apply List.filter_eq_self.mpr
        intro fresh member
        have freshEq := List.mem_singleton.mp member
        subst fresh
        exact decide_eq_true freshNot
  · simp only [if_neg atRoot, List.append_nil]
    exact hold

theorem anchoredWireSplitRawOpen_rootWires
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires =
      (anchoredWireSplitSourceOpen input boundary).exposedWires.map
          (Fin.castAdd 1 : Fin input.val.wireCount →
            Fin (input.val.wireCount + 1)) ++
        ((anchoredWireSplitSourceOpen input boundary).hiddenWires.map
            (Fin.castAdd 1 : Fin input.val.wireCount →
              Fin (input.val.wireCount + 1)) ++
          if input.val.root = target then
            [Fin.last input.val.wireCount]
          else []) := by
  unfold OpenConcreteDiagram.rootWires
  rw [anchoredWireSplitRawOpen_exposedWires,
    anchoredWireSplitRawOpen_hiddenWires]
  rfl

theorem anchoredWireSplitRawOpen_rootWires_of_ne
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (hne : input.val.root ≠ target) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires =
      (anchoredWireSplitSourceOpen input boundary).rootWires.map
        (Fin.castAdd 1 : Fin input.val.wireCount →
          Fin (input.val.wireCount + 1)) := by
  rw [anchoredWireSplitRawOpen_rootWires, if_neg hne]
  simp only [List.append_nil]
  unfold OpenConcreteDiagram.rootWires
  exact (List.map_append).symm

theorem anchoredWireSplitRaw_rootCollapseAway_index_val
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (hne : input.val.root ≠ target)
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (sourceNodup :
      (anchoredWireSplitSourceOpen input boundary).rootWires.Nodup)
    (index : Fin (anchoredWireSplitRawOpen input boundary wire endpoints target
      term).rootWires.length) :
    (collapse.indexMap index).val = index.val := by
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  have rootEq : expanded.rootWires = source.rootWires.map (Fin.castAdd 1) :=
    anchoredWireSplitRawOpen_rootWires_of_ne input boundary wire endpoints target
      term hne
  let mappedIndex : Fin (source.rootWires.map (Fin.castAdd 1)).length :=
    Fin.cast (congrArg List.length rootEq) index
  let sourceIndex : Fin source.rootWires.length :=
    Fin.cast (by simp) mappedIndex
  have targetGet : expanded.rootWires.get index =
      (source.rootWires.get sourceIndex).castSucc := by
    have transported := get_of_eq rootEq mappedIndex
    have indexEq : Fin.cast (congrArg List.length rootEq).symm mappedIndex =
        index := by
      apply Fin.ext
      rfl
    rw [indexEq] at transported
    change expanded.rootWires.get index =
      Fin.castAdd 1 (source.rootWires.get sourceIndex)
    have mappedGet : (source.rootWires.map (Fin.castAdd 1)).get mappedIndex =
        Fin.castAdd 1 (source.rootWires.get sourceIndex) := by
      let expected : Fin (source.rootWires.map (Fin.castAdd 1)).length :=
        Fin.cast (List.length_map (as := source.rootWires) (Fin.castAdd 1)).symm
          sourceIndex
      have mappedEq : mappedIndex = expected := by
        apply Fin.ext
        rfl
      rw [mappedEq]
      simpa only [List.get_eq_getElem, Fin.val_cast] using
        (List.getElem_map (l := source.rootWires) (i := sourceIndex.val)
          (Fin.castAdd 1))
    exact transported.trans mappedGet
  have collapseGet := collapse.get index
  change source.rootWires.get (collapse.indexMap index) =
    splitWireCollapse input wire (expanded.rootWires.get index) at collapseGet
  rw [targetGet] at collapseGet
  have splitGet : splitWireCollapse input wire
      (source.rootWires.get sourceIndex).castSucc =
        source.rootWires.get sourceIndex := by
    simpa [source, anchoredWireSplitSourceOpen] using
      splitWireCollapse_old input wire (source.rootWires.get sourceIndex)
  rw [splitGet] at collapseGet
  have indexEq : collapse.indexMap index = sourceIndex := by
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using collapseGet)
  rw [indexEq]
  rfl

def anchoredWireSplitRawOpenExternalClass
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (external : Fin
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length) :
    Fin (anchoredWireSplitRawOpen input boundary wire endpoints target
      term).exposedWires.length :=
  Fin.cast (by
    rw [anchoredWireSplitRawOpen_exposedWires]
    exact (List.length_map _).symm) external

theorem anchoredWireSplitRawOpenExternalClass_val
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (external : Fin
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length) :
    (anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
      term external).val = external.val := rfl

private theorem rootWires_get_rootExposedIndex
    (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.exposedWires.length) :
    openDiagram.rootWires.get
        (Splice.Input.TwoInputPresentation.rootExposedIndex openDiagram index) =
      openDiagram.exposedWires.get index := by
  simpa [Splice.Input.TwoInputPresentation.rootExposedIndex,
    OpenConcreteDiagram.rootWires, List.get_eq_getElem] using
      (List.getElem_append_left
        (l₂ := openDiagram.hiddenWires) index.isLt)

theorem anchoredWireSplitRaw_rootExposed_get
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (index : Fin
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    expanded.rootWires.get
        (Splice.Input.TwoInputPresentation.rootExposedIndex expanded
          (anchoredWireSplitRawOpenExternalClass input boundary wire endpoints
            target term index)) =
      (source.rootWires.get
        (Splice.Input.TwoInputPresentation.rootExposedIndex source index)).castSucc := by
  dsimp only
  rw [rootWires_get_rootExposedIndex, rootWires_get_rootExposedIndex]
  let exposedEq := anchoredWireSplitRawOpen_exposedWires input boundary wire
    endpoints target term
  let targetIndex := anchoredWireSplitRawOpenExternalClass input boundary wire
    endpoints target term index
  let mappedIndex : Fin
      ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
        (Fin.castAdd 1)).length :=
    Fin.cast (congrArg List.length exposedEq) targetIndex
  have transported := get_of_eq exposedEq mappedIndex
  have recover :
      Fin.cast (congrArg List.length exposedEq).symm mappedIndex =
        targetIndex := by
    apply Fin.ext
    rfl
  rw [recover] at transported
  have mappedGet :
      ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
        (Fin.castAdd 1)).get mappedIndex =
      ((anchoredWireSplitSourceOpen input boundary).exposedWires.get
        index).castSucc := by
    let expected : Fin
        ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
          (Fin.castAdd 1)).length :=
      Fin.cast (List.length_map (as :=
        (anchoredWireSplitSourceOpen input boundary).exposedWires)
        (Fin.castAdd 1)).symm index
    have mappedEq : mappedIndex = expected := by
      apply Fin.ext
      rfl
    rw [mappedEq]
    simpa only [List.get_eq_getElem, Fin.val_cast] using
      (List.getElem_map (l :=
        (anchoredWireSplitSourceOpen input boundary).exposedWires)
        (i := index.val) (Fin.castAdd 1))
  exact transported.trans mappedGet

theorem anchoredWireSplitRaw_rootCollapse_exposed
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (sourceNodup :
      (anchoredWireSplitSourceOpen input boundary).rootWires.Nodup)
    (index : Fin (anchoredWireSplitRawOpen input boundary wire endpoints target
      term).exposedWires.length) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    let sourceIndex : Fin source.exposedWires.length :=
      Fin.cast (by
        rw [anchoredWireSplitRawOpen_exposedWires]
        exact List.length_map _) index
    collapse.indexMap
        (Splice.Input.TwoInputPresentation.rootExposedIndex expanded index) =
      Splice.Input.TwoInputPresentation.rootExposedIndex source sourceIndex := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let sourceIndex : Fin source.exposedWires.length :=
    Fin.cast (by
      rw [anchoredWireSplitRawOpen_exposedWires]
      exact List.length_map _) index
  let targetRootIndex :=
    Splice.Input.TwoInputPresentation.rootExposedIndex expanded index
  let sourceRootIndex :=
    Splice.Input.TwoInputPresentation.rootExposedIndex source sourceIndex
  have targetGet : expanded.rootWires.get targetRootIndex =
      (source.rootWires.get sourceRootIndex).castSucc := by
    rw [rootWires_get_rootExposedIndex, rootWires_get_rootExposedIndex]
    let exposedEq := anchoredWireSplitRawOpen_exposedWires input boundary wire
      endpoints target term
    let mappedIndex : Fin
        ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
          (Fin.castAdd 1)).length :=
      Fin.cast (congrArg List.length exposedEq) index
    have transported := get_of_eq exposedEq mappedIndex
    have recover :
        Fin.cast (congrArg List.length exposedEq).symm mappedIndex = index := by
      apply Fin.ext
      rfl
    rw [recover] at transported
    have mappedGet :
        ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
          (Fin.castAdd 1)).get mappedIndex =
        ((anchoredWireSplitSourceOpen input boundary).exposedWires.get
          sourceIndex).castSucc := by
      let expected : Fin
          ((anchoredWireSplitSourceOpen input boundary).exposedWires.map
            (Fin.castAdd 1)).length :=
        Fin.cast (List.length_map (as :=
          (anchoredWireSplitSourceOpen input boundary).exposedWires)
          (Fin.castAdd 1)).symm sourceIndex
      have mappedEq : mappedIndex = expected := by
        apply Fin.ext
        rfl
      rw [mappedEq]
      simpa only [List.get_eq_getElem, Fin.val_cast] using
        (List.getElem_map (l :=
          (anchoredWireSplitSourceOpen input boundary).exposedWires)
          (i := sourceIndex.val) (Fin.castAdd 1))
    exact transported.trans mappedGet
  have collapseGet := collapse.get targetRootIndex
  change source.rootWires.get (collapse.indexMap targetRootIndex) =
    splitWireCollapse input wire (expanded.rootWires.get targetRootIndex) at collapseGet
  have splitGet : splitWireCollapse input wire
      (source.rootWires.get sourceRootIndex).castSucc =
        source.rootWires.get sourceRootIndex := by
    exact splitWireCollapse_old input wire
      (source.rootWires.get sourceRootIndex)
  rw [targetGet, splitGet] at collapseGet
  apply Fin.ext
  exact (List.getElem_inj sourceNodup).mp (by
    simpa only [List.get_eq_getElem] using collapseGet)

theorem anchoredWireSplitRaw_rootOldIndex_exposed
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (expandedNodup :
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires.Nodup)
    (index : Fin
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    collapse.oldIndex
        (Splice.Input.TwoInputPresentation.rootExposedIndex source index) =
      Splice.Input.TwoInputPresentation.rootExposedIndex expanded
        (anchoredWireSplitRawOpenExternalClass input boundary wire endpoints
          target term index) := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let sourceRootIndex :=
    Splice.Input.TwoInputPresentation.rootExposedIndex source index
  let targetRootIndex :=
    Splice.Input.TwoInputPresentation.rootExposedIndex expanded
      (anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
        term index)
  have oldGet := collapse.old_get sourceRootIndex
  change expanded.rootWires.get (collapse.oldIndex sourceRootIndex) =
    (source.rootWires.get sourceRootIndex).castSucc at oldGet
  have targetGet : expanded.rootWires.get targetRootIndex =
      (source.rootWires.get sourceRootIndex).castSucc :=
    anchoredWireSplitRaw_rootExposed_get input boundary wire endpoints target
      term index
  apply Fin.ext
  exact (List.getElem_inj expandedNodup).mp (by
    simpa only [List.get_eq_getElem] using oldGet.trans targetGet.symm)

theorem anchoredWireSplitRaw_rootEnvironment_collapse_forward
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (sourceNodup :
      (anchoredWireSplitSourceOpen input boundary).rootWires.Nodup)
    (model : Lambda.LambdaModel)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → model.Carrier)
    (sourceLocal : Fin
      (anchoredWireSplitSourceOpen input boundary).hiddenWires.length →
        model.Carrier) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    let sourceOuter := targetOuter ∘
      anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
        term
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires sourceOuter sourceLocal
    ∃ targetLocal : Fin expanded.hiddenWires.length → model.Carrier,
      sourceRaw ∘ collapse.indexMap =
        ConcreteElaboration.rootEnvironment expanded.exposedWires
          expanded.hiddenWires targetOuter targetLocal := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let sourceOuter := targetOuter ∘
    anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
      term
  let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
    source.hiddenWires sourceOuter sourceLocal
  let targetComplete : Fin expanded.rootWires.length → model.Carrier :=
    sourceRaw ∘ collapse.indexMap
  let targetLocal : Fin expanded.hiddenWires.length → model.Carrier :=
    fun index => targetComplete
      (Splice.Input.TwoInputPresentation.rootHiddenIndex expanded index)
  refine ⟨targetLocal, ?_⟩
  have outerEq : (
      fun index => targetComplete
        (Splice.Input.TwoInputPresentation.rootExposedIndex expanded index)) =
      targetOuter := by
    funext index
    let sourceIndex : Fin source.exposedWires.length :=
      Fin.cast (by
        rw [anchoredWireSplitRawOpen_exposedWires]
        exact List.length_map _) index
    have mapped := anchoredWireSplitRaw_rootCollapse_exposed input boundary wire
      endpoints target term collapse sourceNodup index
    change collapse.indexMap
        (Splice.Input.TwoInputPresentation.rootExposedIndex expanded index) =
      Splice.Input.TwoInputPresentation.rootExposedIndex source sourceIndex at mapped
    simp only [targetComplete, Function.comp_apply, mapped, sourceRaw,
      Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex,
      sourceOuter]
    apply congrArg targetOuter
    apply Fin.ext
    rfl
  have complete :=
    Splice.Input.TwoInputPresentation.rootEnvironment_of_complete expanded
      targetComplete
  rw [outerEq] at complete
  change ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal = targetComplete at complete
  exact complete.symm

theorem anchoredWireSplitRaw_rootEnvironment_uncollapse
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (expandedNodup :
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires.Nodup)
    (model : Lambda.LambdaModel)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → model.Carrier)
    (targetLocal : Fin
      (anchoredWireSplitRawOpen input boundary wire endpoints target
        term).hiddenWires.length → model.Carrier)
    (termValue : model.Carrier)
    (targetOldValue : ∀ index,
      (anchoredWireSplitRawOpen input boundary wire endpoints target
        term).rootWires.get index = wire.castSucc →
      ConcreteElaboration.rootEnvironment
          (anchoredWireSplitRawOpen input boundary wire endpoints target
            term).exposedWires
          (anchoredWireSplitRawOpen input boundary wire endpoints target
            term).hiddenWires targetOuter targetLocal index = termValue)
    (targetFreshValue : ∀ index,
      (anchoredWireSplitRawOpen input boundary wire endpoints target
        term).rootWires.get index = Fin.last input.val.wireCount →
      ConcreteElaboration.rootEnvironment
          (anchoredWireSplitRawOpen input boundary wire endpoints target
            term).exposedWires
          (anchoredWireSplitRawOpen input boundary wire endpoints target
            term).hiddenWires targetOuter targetLocal index = termValue) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    let sourceOuter := targetOuter ∘
      anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
        term
    let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal
    ∃ sourceLocal : Fin source.hiddenWires.length → model.Carrier,
      ConcreteElaboration.rootEnvironment source.exposedWires source.hiddenWires
          sourceOuter sourceLocal ∘ collapse.indexMap = targetRaw := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let sourceOuter := targetOuter ∘
    anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
      term
  let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
    expanded.hiddenWires targetOuter targetLocal
  let sourceComplete : Fin source.rootWires.length → model.Carrier :=
    fun index => targetRaw (collapse.oldIndex index)
  let sourceLocal : Fin source.hiddenWires.length → model.Carrier :=
    fun index => sourceComplete
      (Splice.Input.TwoInputPresentation.rootHiddenIndex source index)
  refine ⟨sourceLocal, ?_⟩
  have outerEq : (
      fun index => sourceComplete
        (Splice.Input.TwoInputPresentation.rootExposedIndex source index)) =
      sourceOuter := by
    funext index
    have mapped := anchoredWireSplitRaw_rootOldIndex_exposed input boundary wire
      endpoints target term collapse expandedNodup index
    dsimp only at mapped
    change targetRaw (collapse.oldIndex
      (Splice.Input.TwoInputPresentation.rootExposedIndex source index)) =
        sourceOuter index
    rw [mapped]
    change ConcreteElaboration.rootEnvironment expanded.exposedWires
        expanded.hiddenWires targetOuter targetLocal
          (Splice.Input.TwoInputPresentation.rootExposedIndex expanded
            (anchoredWireSplitRawOpenExternalClass input boundary wire endpoints
              target term index)) =
      targetOuter (anchoredWireSplitRawOpenExternalClass input boundary wire
        endpoints target term index)
    exact Splice.Input.TwoInputPresentation.rootEnvironment_rootExposedIndex
      expanded targetOuter targetLocal _
  have sourceCompleteEq :=
    Splice.Input.TwoInputPresentation.rootEnvironment_of_complete source
      sourceComplete
  rw [outerEq] at sourceCompleteEq
  change ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires sourceOuter sourceLocal = sourceComplete at sourceCompleteEq
  rw [sourceCompleteEq]
  funext targetIndex
  change targetRaw (collapse.oldIndex (collapse.indexMap targetIndex)) =
    targetRaw targetIndex
  refine Fin.lastCases (motive := fun candidate =>
      expanded.rootWires.get targetIndex = candidate →
        targetRaw (collapse.oldIndex (collapse.indexMap targetIndex)) =
          targetRaw targetIndex) ?_ (fun old oldEq => ?_)
    (expanded.rootWires.get targetIndex) rfl
  · intro freshEq
    have collapseGet := collapse.get targetIndex
    change source.rootWires.get (collapse.indexMap targetIndex) =
      splitWireCollapse input wire (expanded.rootWires.get targetIndex) at collapseGet
    rw [freshEq, splitWireCollapse_fresh] at collapseGet
    have oldGet := collapse.old_get (collapse.indexMap targetIndex)
    change expanded.rootWires.get
        (collapse.oldIndex (collapse.indexMap targetIndex)) =
      (source.rootWires.get (collapse.indexMap targetIndex)).castSucc at oldGet
    rw [collapseGet] at oldGet
    exact (targetOldValue _ oldGet).trans
      (targetFreshValue _ freshEq).symm
  ·
    have collapseGet := collapse.get targetIndex
    change source.rootWires.get (collapse.indexMap targetIndex) =
      splitWireCollapse input wire (expanded.rootWires.get targetIndex) at collapseGet
    rw [oldEq, splitWireCollapse_old] at collapseGet
    have oldGet := collapse.old_get (collapse.indexMap targetIndex)
    change expanded.rootWires.get
        (collapse.oldIndex (collapse.indexMap targetIndex)) =
      (source.rootWires.get (collapse.indexMap targetIndex)).castSucc at oldGet
    rw [collapseGet] at oldGet
    have indexEq : collapse.oldIndex (collapse.indexMap targetIndex) =
        targetIndex := by
      apply Fin.ext
      exact (List.getElem_inj expandedNodup).mp (by
        simpa only [List.get_eq_getElem] using oldGet.trans oldEq.symm)
    rw [indexEq]

private theorem extendWireEnv_cast_lengths
    {sourceOuter targetOuter sourceLocal targetLocal : Nat}
    (ambientLength : sourceOuter = targetOuter)
    (localLength : sourceLocal = targetLocal)
    (outerEnv : Fin targetOuter → D)
    (localEnv : Fin targetLocal → D) :
    extendWireEnv (outerEnv ∘ Fin.cast ambientLength)
        (localEnv ∘ Fin.cast localLength) =
      extendWireEnv outerEnv localEnv ∘
        Fin.cast (by omega) := by
  subst targetOuter
  subst targetLocal
  rfl

private theorem rootEnvironment_cast_lengths
    {source target : ConcreteDiagram}
    (sourceAmbient sourceLocals : ConcreteElaboration.WireContext source)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext target)
    (ambientLength : sourceAmbient.length = targetAmbient.length)
    (localLength : sourceLocals.length = targetLocals.length)
    (targetOuter : Fin targetAmbient.length → D)
    (targetLocal : Fin targetLocals.length → D) :
    ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
        (targetOuter ∘ Fin.cast ambientLength)
        (targetLocal ∘ Fin.cast localLength) =
      ConcreteElaboration.rootEnvironment targetAmbient targetLocals
        targetOuter targetLocal ∘
          Fin.cast (by
            rw [List.length_append, List.length_append,
              ambientLength, localLength]) := by
  unfold ConcreteElaboration.rootEnvironment
  rw [extendWireEnv_cast_lengths ambientLength localLength]
  funext index
  apply congrArg (extendWireEnv targetOuter targetLocal)
  apply Fin.ext
  rfl

theorem anchoredWireSplitRaw_rootEnvironmentAway_collapse
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (hne : input.val.root ≠ target)
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (sourceNodup :
      (anchoredWireSplitSourceOpen input boundary).rootWires.Nodup)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → D)
    (targetLocal : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).hiddenWires.length → D) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    let ambientLength : source.exposedWires.length =
        expanded.exposedWires.length := by
      rw [anchoredWireSplitRawOpen_exposedWires]
      exact (List.length_map _).symm
    let localLength : source.hiddenWires.length =
        expanded.hiddenWires.length := by
      rw [anchoredWireSplitRawOpen_hiddenWires, if_neg hne, List.append_nil]
      exact (List.length_map _).symm
    ConcreteElaboration.rootEnvironment source.exposedWires source.hiddenWires
          (targetOuter ∘ Fin.cast ambientLength)
          (targetLocal ∘ Fin.cast localLength) ∘ collapse.indexMap =
      ConcreteElaboration.rootEnvironment expanded.exposedWires
        expanded.hiddenWires targetOuter targetLocal := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let ambientLength : source.exposedWires.length =
      expanded.exposedWires.length := by
    rw [anchoredWireSplitRawOpen_exposedWires]
    exact (List.length_map _).symm
  let localLength : source.hiddenWires.length =
      expanded.hiddenWires.length := by
    rw [anchoredWireSplitRawOpen_hiddenWires, if_neg hne, List.append_nil]
    exact (List.length_map _).symm
  have casted := rootEnvironment_cast_lengths source.exposedWires
    source.hiddenWires expanded.exposedWires expanded.hiddenWires ambientLength
    localLength targetOuter targetLocal
  rw [casted]
  funext index
  apply congrArg (ConcreteElaboration.rootEnvironment expanded.exposedWires
    expanded.hiddenWires targetOuter targetLocal)
  apply Fin.ext
  exact anchoredWireSplitRaw_rootCollapseAway_index_val input boundary wire
    endpoints target term hne collapse sourceNodup index

theorem anchoredWireSplitRaw_finishRoot_away_equiv
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (hne : input.val.root ≠ target)
    (collapse : SplitContextCollapse input wire endpoints target term
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).rootWires
      (anchoredWireSplitSourceOpen input boundary).rootWires)
    (sourceNodup :
      (anchoredWireSplitSourceOpen input boundary).rootWires.Nodup)
    (sourceItems : ItemSeq signature
      (anchoredWireSplitSourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature (anchoredWireSplitRawOpen input boundary
      wire endpoints target term).rootWires.length [])
    (itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceRaw : Fin
        (anchoredWireSplitSourceOpen input boundary).rootWires.length →
          model.Carrier)
      (targetRaw : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
        target term).rootWires.length → model.Carrier),
      sourceRaw ∘ collapse.indexMap = targetRaw →
        (denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
            sourceItems ↔
          denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
            targetItems))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → model.Carrier) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
      term
    denoteRegion (relCtx := []) model named
        (targetOuter ∘ anchoredWireSplitRawOpenExternalClass input boundary wire
          endpoints target term) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) ↔
      denoteRegion (relCtx := []) model named targetOuter PUnit.unit
        (ConcreteElaboration.finishRoot expanded.exposedWires
          expanded.hiddenWires targetItems) := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let ambientLength : source.exposedWires.length =
      expanded.exposedWires.length := by
    rw [anchoredWireSplitRawOpen_exposedWires]
    exact (List.length_map _).symm
  let localLength : source.hiddenWires.length =
      expanded.hiddenWires.length := by
    rw [anchoredWireSplitRawOpen_hiddenWires, if_neg hne, List.append_nil]
    exact (List.length_map _).symm
  have externalEq : anchoredWireSplitRawOpenExternalClass input boundary wire
      endpoints target term = Fin.cast ambientLength := by
    funext external
    apply Fin.ext
    rfl
  rw [externalEq]
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨sourceLocal, sourceDenotes⟩
    let targetLocal : Fin expanded.hiddenWires.length → model.Carrier :=
      sourceLocal ∘ Fin.cast localLength.symm
    refine ⟨targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceDenotes ⊢
    have sourceRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires)))
      (extendWireEnv (targetOuter ∘ Fin.cast ambientLength) sourceLocal)
      PUnit.unit sourceItems).1 sourceDenotes
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires (targetOuter ∘ Fin.cast ambientLength) sourceLocal
    let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal
    have localRecover : targetLocal ∘ Fin.cast localLength = sourceLocal := by
      funext index
      rfl
    have rawAgrees := anchoredWireSplitRaw_rootEnvironmentAway_collapse input
      boundary wire endpoints target term hne collapse sourceNodup targetOuter
      targetLocal
    dsimp only at rawAgrees
    rw [localRecover] at rawAgrees
    change sourceRaw ∘ collapse.indexMap = targetRaw at rawAgrees
    have targetRawDenotes := (itemsEquiv model named sourceRaw targetRaw
      rawAgrees).mp (by
        simpa [sourceRaw, ConcreteElaboration.rootEnvironment] using
          sourceRawDenotes)
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := expanded.exposedWires)
        (bs := expanded.hiddenWires)))
      (extendWireEnv targetOuter targetLocal) PUnit.unit targetItems).2
    simpa [targetRaw, ConcreteElaboration.rootEnvironment] using
      targetRawDenotes
  · rintro ⟨targetLocal, targetDenotes⟩
    let sourceLocal : Fin source.hiddenWires.length → model.Carrier :=
      targetLocal ∘ Fin.cast localLength
    refine ⟨sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetDenotes ⊢
    have targetRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := expanded.exposedWires)
        (bs := expanded.hiddenWires)))
      (extendWireEnv targetOuter targetLocal) PUnit.unit targetItems).1
        targetDenotes
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires (targetOuter ∘ Fin.cast ambientLength) sourceLocal
    let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal
    have rawAgrees := anchoredWireSplitRaw_rootEnvironmentAway_collapse input
      boundary wire endpoints target term hne collapse sourceNodup targetOuter
      targetLocal
    dsimp only at rawAgrees
    change sourceRaw ∘ collapse.indexMap = targetRaw at rawAgrees
    have sourceRawDenotes := (itemsEquiv model named sourceRaw targetRaw
      rawAgrees).mpr (by
        simpa [targetRaw, ConcreteElaboration.rootEnvironment] using
          targetRawDenotes)
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires)))
      (extendWireEnv (targetOuter ∘ Fin.cast ambientLength) sourceLocal)
      PUnit.unit sourceItems).2
    simpa [sourceRaw, ConcreteElaboration.rootEnvironment] using
      sourceRawDenotes

theorem anchoredWireSplitRaw_compileRootOccurrencesAway
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target parent selected : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (selectedParent : (input.val.regions selected).parent? = some parent)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input.val selected target rest)
    (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (originalExact : original.Exact parent)
    (expandedExact : expanded.Exact parent)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (localMembership : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val parent)
    (away : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        original binders occurrences =
      (ConcreteElaboration.compileOccurrencesWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        expanded binders (occurrences.map (splitOldOccurrence input))).map
          (ItemSeq.renameWires collapse.indexMap) := by
  apply compileOccurrencesWith?_collapse
  intro occurrence member
  apply anchoredWireSplitRaw_compileOccurrenceWith?_collapse input wire
    endpoints target term selectedOccurs targetWellFormed parent expanded
    original collapse expandedExact originalExact
    (ConcreteElaboration.compileRegion? signature input.val fuel)
    (ConcreteElaboration.compileRegion? signature
      (anchoredWireSplitRaw input wire endpoints target term) fuel)
    binders occurrence (localMembership occurrence member)
  intro childRels child childBinders occurrenceEq
  subst occurrence
  have childParent :=
    (ConcreteElaboration.mem_localOccurrences_child input.val parent child).mp
      (localMembership (.child child) member)
  have childNe : child ≠ selected := by
    intro equality
    subst child
    exact away member
  have childNotAbove : ¬ input.val.Encloses child target :=
    split_sibling_not_encloses_descendant input.val input.property selectedParent
      childParent (regionRoute_encloses input.val input.property tail) childNe
  have originalChildExact := originalExact.extend_child input.property childParent
  have targetChildParent :
      ((anchoredWireSplitRaw input wire endpoints target term).regions child).parent? =
        some parent := by
    simpa only [anchoredWireSplitRaw_regions] using childParent
  have expandedChildExact :=
    expandedExact.extend_child targetWellFormed targetChildParent
  exact anchoredWireSplitRaw_compileRegion?_collapse_of_not_encloses input wire
    endpoints target term selectedOccurs targetWellFormed wireEnclosesTarget fuel
    child original expanded collapse childBinders childNotAbove
    originalChildExact expandedChildExact

theorem anchoredWireSplitRawOpen_wellFormed
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target term).WellFormed
      signature := by
  constructor
  · exact targetWellFormed
  · intro candidate member
    rcases List.mem_map.mp member with ⟨old, oldMember, rfl⟩
    have oldRoot := sourceRoot old oldMember
    change ((anchoredWireSplitRaw input wire endpoints target term).wires
      old.castSucc).scope =
        (anchoredWireSplitRaw input wire endpoints target term).root
    simpa only [anchoredWireSplitRaw_oldWire_scope,
      anchoredWireSplitRaw_root] using oldRoot

theorem anchoredWireSplitRaw_bindersCover
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    {rels : RelCtx} (binders : ConcreteElaboration.BinderContext input.val rels)
    (region : Fin input.val.regionCount)
    (cover : ConcreteElaboration.BinderContext.Covers
      (d := input.val) binders region) :
    ConcreteElaboration.BinderContext.Covers
      (d := anchoredWireSplitRaw input wire endpoints target term)
      binders region := by
  intro binder parent arity binderKind encloses
  apply cover binder parent arity
  · simpa only [anchoredWireSplitRaw_regions] using binderKind
  · exact (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      binder region).mp encloses

def anchoredWireSplitRaw_binderEnumeration
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    {rels : RelCtx} (binders : ConcreteElaboration.BinderContext input.val rels)
    (region : Fin input.val.regionCount)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val binders region) :
    ConcreteElaboration.BinderContext.Enumeration
      (anchoredWireSplitRaw input wire endpoints target term) binders region where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := by
    intro index
    obtain ⟨parent, kind⟩ := enumeration.bubble index
    exact ⟨parent, by simpa only [anchoredWireSplitRaw_regions] using kind⟩
  encloses := by
    intro index
    exact (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      (enumeration.binder index) region).mpr (enumeration.encloses index)
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

/-- The zero-route witness extractor is independent of the root wire ordering.
Recompile the same occurrences in the canonical exact root context, transport
their denotation through the compiler-certified context isomorphism, and map
the resulting equation back to exposed-then-hidden ordered-open coordinates. -/
theorem anchoredWireSplit_root_witness_value_of_zero_route
    (checked : CheckedOpenDiagram signature)
    (wire : Fin checked.val.diagram.wireCount)
    (witness : Fin checked.val.diagram.nodeCount)
    (witnessRegion : Fin checked.val.diagram.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : checked.val.diagram.nodes witness =
      .term witnessRegion 0 term)
    (witnessOccurs : checked.val.diagram.EndpointOccurs wire
      { node := witness, port := .output })
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute checked.val.diagram
      checked.val.diagram.root witnessRegion path)
    (routeZero : route.HasCutDepth 0)
    (items : ItemSeq signature checked.val.rootWires.length [])
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      checked.val.diagram
      (ConcreteElaboration.compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) = some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (raw : Fin checked.val.rootWires.length → model.Carrier)
    (itemsDenote : denoteItemSeq (relCtx := []) model named raw PUnit.unit
      items) :
    ∀ index, checked.val.rootWires.get index = wire →
      raw index = model.eval term Fin.elim0 := by
  let closed : CheckedDiagram signature :=
    ⟨checked.val.diagram, checked.property.diagram_well_formed⟩
  let exactContext :=
    ConcreteElaboration.exactScopeWires checked.val.diagram
      checked.val.diagram.root
  have exact : ConcreteElaboration.WireContext.Exact exactContext
      checked.val.diagram.root := by
    simpa [exactContext, ConcreteElaboration.WireContext.extend] using
      ConcreteElaboration.closedRootWires_exact
        checked.property.diagram_well_formed
  obtain ⟨closedBody, closedBodyCompiled⟩ :=
    ConcreteElaboration.compileRoot?_complete
      checked.property.diagram_well_formed
      ([] : ConcreteElaboration.WireContext checked.val.diagram) exactContext
      (by simpa using exact)
  simp only [ConcreteElaboration.compileRoot?] at closedBodyCompiled
  cases exactItemsResult : ConcreteElaboration.compileOccurrencesWith?
      signature checked.val.diagram
      (ConcreteElaboration.compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      exactContext ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) with
  | none => simp [exactItemsResult] at closedBodyCompiled
  | some exactItems =>
    let wireEquiv := Diagram.exactContextToOpenRootWireEquiv checked
      exactContext exact
    have itemIso := Diagram.compiledOpenRootItemsIsoFromExactContext checked
      exactContext exact exactItemsResult compiled
    let exactRaw : Fin exactContext.length → model.Carrier :=
      raw ∘ wireEquiv
    have environmentsAgree : EnvironmentsAgree wireEquiv exactRaw raw := by
      intro index
      rfl
    have exactDenotes : denoteItemSeq (relCtx := []) model named exactRaw
        PUnit.unit exactItems :=
      (itemIso.denotation model named exactRaw raw PUnit.unit
        environmentsAgree).mpr itemsDenote
    have exactCompiled : ConcreteElaboration.compileOccurrencesWith? signature
        closed.val
        (ConcreteElaboration.compileRegion? signature closed.val
          closed.val.regionCount)
        (ConcreteElaboration.WireContext.extend
          ([] : ConcreteElaboration.WireContext closed.val) closed.val.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences closed.val closed.val.root) =
          some exactItems := by
      simpa [closed, exactContext, ConcreteElaboration.WireContext.extend] using
        exactItemsResult
    have exactEquation := anchoredWireSplit_witness_value_of_zero_route closed
      wire witness witnessRegion term witnessShape witnessOccurs route routeZero
      ([] : ConcreteElaboration.WireContext closed.val)
      ConcreteElaboration.BinderContext.empty closed.val.regionCount exactItems
      exactCompiled
      (by simpa [closed, exactContext,
        ConcreteElaboration.WireContext.extend] using exact)
      (ConcreteElaboration.BinderContext.empty_covers_root closed.property)
      (ConcreteElaboration.BinderContext.Enumeration.empty closed.val)
      model named Fin.elim0 exactRaw PUnit.unit (by
        rw [ConcreteElaboration.extendedEnvironment_nil_eq_cast]
        exact exactDenotes)
    intro index indexGet
    let exactIndex : Fin exactContext.length := wireEquiv.symm index
    have mappedIndex : wireEquiv exactIndex = index := wireEquiv.right_inv index
    have exactGet : exactContext.get exactIndex = wire := by
      have specification := Diagram.exactContextToOpenRootWireEquiv_spec checked
        exactContext exact exactIndex
      rw [mappedIndex] at specification
      exact specification.symm.trans indexGet
    have value := exactEquation exactIndex (by
      simpa [closed, exactContext, ConcreteElaboration.WireContext.extend] using
        exactGet)
    rw [ConcreteElaboration.extendedEnvironment_nil_eq_cast] at value
    change raw (wireEquiv exactIndex) = model.eval term Fin.elim0 at value
    rw [mappedIndex] at value
    exact value

/-- A bubble-only witness route remains bubble-only after the split.  Route
positions may shift at the split site, so the target route is reconstructed
from enclosure rather than cast positionally. -/
theorem anchoredWireSplitRaw_zero_route_transport
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target start witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (witnessInside : input.val.Encloses start witnessRegion)
    (sameDepth : concreteCutDepth input.val start =
      concreteCutDepth input.val witnessRegion) :
    ∃ path, ∃ route : Diagram.Splice.RegionRoute
        (anchoredWireSplitRaw input wire endpoints target term) start
        witnessRegion path,
      route.HasCutDepth 0 := by
  let targetChecked : CheckedDiagram signature :=
    ⟨anchoredWireSplitRaw input wire endpoints target term, targetWellFormed⟩
  have targetWitnessInside : targetChecked.val.Encloses start witnessRegion :=
    (anchoredWireSplitRaw_encloses_iff input wire endpoints target term start
      witnessRegion).mpr witnessInside
  obtain ⟨path, ⟨route⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses targetChecked.val start
      witnessRegion targetWitnessInside
  obtain ⟨depth, routeDepth⟩ := route.hasCutDepth_exists targetWellFormed
  have depthPreserve : ∀ fuel (region : Fin input.val.regionCount),
      concreteCutDepthAux targetChecked.val fuel region =
        concreteCutDepthAux input.val fuel region := by
    intro fuel
    induction fuel with
    | zero => intro region; rfl
    | succ fuel ih =>
        intro region
        simp only [concreteCutDepthAux]
        rw [show targetChecked.val.regions region = input.val.regions region by
          simp [targetChecked, anchoredWireSplitRaw_regions]]
        cases kind : input.val.regions region with
        | sheet => rfl
        | cut parent => simp only [ih]
        | bubble parent arity => simp only [ih]
  have targetSameDepth : concreteCutDepth targetChecked.val start =
      concreteCutDepth targetChecked.val witnessRegion := by
    unfold concreteCutDepth
    rw [depthPreserve, depthPreserve]
    exact sameDepth
  have depthZero := CongruenceSoundness.route_cutDepth_zero_of_equal
    targetChecked route depth routeDepth targetSameDepth
  subst depth
  exact ⟨path, route, routeDepth⟩

/-- Root-site item equivalence lifted through the authoritative ordered-open
`finishRoot` semantics.  Forward transport chooses the fresh hidden value from
the old wire; inverse transport is justified by the retained old witness and
the inserted fresh equation. -/
theorem anchoredWireSplitRaw_finishRoot_at_root_equiv
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints input.val.root term).WellFormed
        signature)
    (wireEnclosesRoot :
      input.val.Encloses (input.val.wires wire).scope input.val.root)
    (sourceItems : ItemSeq signature
      (anchoredWireSplitSourceOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (anchoredWireSplitRawOpen input boundary wire endpoints input.val.root
        term).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val
      (ConcreteElaboration.compileRegion? signature input.val
        input.val.regionCount)
      (anchoredWireSplitSourceOpen input boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.val input.val.root) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (anchoredWireSplitRaw input wire endpoints input.val.root term)
      (ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints input.val.root term)
        input.val.regionCount)
      (anchoredWireSplitRawOpen input boundary wire endpoints input.val.root
        term).rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (anchoredWireSplitRaw input wire endpoints input.val.root term)
        input.val.root) = some targetItems)
    (sourceWitness : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (raw : Fin (anchoredWireSplitSourceOpen input boundary).rootWires.length →
        model.Carrier),
      denoteItemSeq (relCtx := []) model named raw PUnit.unit sourceItems →
      ∀ index,
        (anchoredWireSplitSourceOpen input boundary).rootWires.get index = wire →
        raw index = model.eval term Fin.elim0)
    (targetWitness : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (raw : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
        input.val.root term).rootWires.length → model.Carrier),
      denoteItemSeq (relCtx := []) model named raw PUnit.unit targetItems →
      ∀ index,
        (anchoredWireSplitRawOpen input boundary wire endpoints input.val.root
          term).rootWires.get index = wire.castSucc →
        raw index = model.eval term Fin.elim0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      input.val.root term).exposedWires.length → model.Carrier) :
    let source := anchoredWireSplitSourceOpen input boundary
    let expanded := anchoredWireSplitRawOpen input boundary wire endpoints
      input.val.root term
    denoteRegion (relCtx := []) model named
        (targetOuter ∘ anchoredWireSplitRawOpenExternalClass input boundary wire
          endpoints input.val.root term) PUnit.unit
        (ConcreteElaboration.finishRoot source.exposedWires source.hiddenWires
          sourceItems) ↔
      denoteRegion (relCtx := []) model named targetOuter PUnit.unit
        (ConcreteElaboration.finishRoot expanded.exposedWires
          expanded.hiddenWires targetItems) := by
  dsimp only
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints
    input.val.root term
  have sourceWellFormed : source.WellFormed signature := {
    diagram_well_formed := input.property
    boundary_is_root_scoped := sourceRoot
  }
  have expandedWellFormed : expanded.WellFormed signature :=
    anchoredWireSplitRawOpen_wellFormed input boundary sourceRoot wire endpoints
      input.val.root term targetWellFormed
  have sourceExact := OpenConcreteDiagram.rootWires_exact source sourceWellFormed
  have expandedExact := OpenConcreteDiagram.rootWires_exact expanded
    expandedWellFormed
  let collapse := SplitContextCollapse.ofExact input wire endpoints input.val.root
    term wireEnclosesRoot input.val.root expanded.rootWires source.rootWires
    expandedExact sourceExact
  let sourceOuter := targetOuter ∘
    anchoredWireSplitRawOpenExternalClass input boundary wire endpoints
      input.val.root term
  unfold ConcreteElaboration.finishRoot
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨sourceLocal, sourceDenotes⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceDenotes
    have sourceRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires)))
      (extendWireEnv sourceOuter sourceLocal) PUnit.unit sourceItems).1
        sourceDenotes
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires sourceOuter sourceLocal
    change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
      sourceItems at sourceRawDenotes
    obtain ⟨targetLocal, rawAgrees⟩ :=
      anchoredWireSplitRaw_rootEnvironment_collapse_forward input boundary wire
        endpoints input.val.root term collapse sourceExact.nodup model
        targetOuter sourceLocal
    refine ⟨targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires]
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := expanded.exposedWires)
        (bs := expanded.hiddenWires)))
      (extendWireEnv targetOuter targetLocal) PUnit.unit targetItems).2
    let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal
    change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
      targetItems
    exact (anchoredWireSplitRaw_target_items_equiv input wire endpoints
      input.val.root term selectedOccurs targetWellFormed wireEnclosesRoot
      input.val.regionCount source.rootWires expanded.rootWires collapse
      ConcreteElaboration.BinderContext.empty sourceExact expandedExact
      sourceItems targetItems sourceCompiled targetCompiled model named sourceRaw
      targetRaw PUnit.unit rawAgrees
      (sourceWitness model named sourceRaw)).mp sourceRawDenotes
  · rintro ⟨targetLocal, targetDenotes⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetDenotes
    have targetRawDenotes := (denoteItemSeq_renameWires (relCtx := []) model
      named (Fin.cast (List.length_append (as := expanded.exposedWires)
        (bs := expanded.hiddenWires)))
      (extendWireEnv targetOuter targetLocal) PUnit.unit targetItems).1
        targetDenotes
    let targetRaw := ConcreteElaboration.rootEnvironment expanded.exposedWires
      expanded.hiddenWires targetOuter targetLocal
    change denoteItemSeq (relCtx := []) model named targetRaw PUnit.unit
      targetItems at targetRawDenotes
    have oldValue := targetWitness model named targetRaw targetRawDenotes
    have freshValue := anchoredWireSplitRaw_fresh_value_of_target_items input
      wire endpoints input.val.root term targetWellFormed input.val.regionCount
      expanded.rootWires ConcreteElaboration.BinderContext.empty expandedExact
      targetItems targetCompiled model named targetRaw PUnit.unit targetRawDenotes
    obtain ⟨sourceLocal, rawAgrees⟩ :=
      anchoredWireSplitRaw_rootEnvironment_uncollapse input boundary wire
        endpoints input.val.root term collapse expandedExact.nodup model
        targetOuter targetLocal (model.eval term Fin.elim0) oldValue freshValue
    refine ⟨sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires]
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (List.length_append (as := source.exposedWires)
        (bs := source.hiddenWires)))
      (extendWireEnv sourceOuter sourceLocal) PUnit.unit sourceItems).2
    let sourceRaw := ConcreteElaboration.rootEnvironment source.exposedWires
      source.hiddenWires sourceOuter sourceLocal
    change denoteItemSeq (relCtx := []) model named sourceRaw PUnit.unit
      sourceItems
    exact (anchoredWireSplitRaw_target_items_equiv input wire endpoints
      input.val.root term selectedOccurs targetWellFormed wireEnclosesRoot
      input.val.regionCount source.rootWires expanded.rootWires collapse
      ConcreteElaboration.BinderContext.empty sourceExact expandedExact
      sourceItems targetItems sourceCompiled targetCompiled model named sourceRaw
      targetRaw PUnit.unit rawAgrees
      (sourceWitness model named sourceRaw)).mpr targetRawDenotes

/-- A complete semantic kernel at one certified availability region. -/
def AnchoredAvailableKernel
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature) :
    Prop :=
  ∀ {rels : RelCtx} (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (bindersCover : binders.Covers available)
    (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val binders available)
    (originalExact : (original.extend available).Exact available)
    (expandedExact : (expanded.extend available).Exact available)
    (sourceBody : Region signature original.length rels)
    (targetBody : Region signature expanded.length rels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
      (fuel + 1) available original binders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (anchoredWireSplitRaw input wire endpoints target term)
      (fuel + 1) available expanded binders = some targetBody)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin original.length → model.Carrier)
    (targetOuter : Fin expanded.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    sourceOuter ∘ collapse.indexMap = targetOuter →
      (denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody)

theorem anchoredWireSplitRaw_certified_available_kernel
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs wire
      { node := witness, port := .output })
    (witnessKept : { node := witness, port := CPort.output } ∉ endpoints)
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature)
    (wireEnclosesAvailable :
      input.val.Encloses (input.val.wires wire).scope available)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {witnessPath targetPath : List Nat}
    (witnessRoute : Diagram.Splice.RegionRoute input.val available witnessRegion
      witnessPath)
    (witnessZero : witnessRoute.HasCutDepth 0)
    (sameDepth : concreteCutDepth input.val available =
      concreteCutDepth input.val witnessRegion)
    (targetRoute : Diagram.Splice.RegionRoute input.val available target
      targetPath) :
    AnchoredAvailableKernel input wire endpoints target available term
      targetWellFormed := by
  let targetChecked : CheckedDiagram signature :=
    ⟨anchoredWireSplitRaw input wire endpoints target term, targetWellFormed⟩
  have targetWitnessEncloses : targetChecked.val.Encloses available witnessRegion :=
    (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      available witnessRegion).mpr
      (regionRoute_encloses input.val input.property witnessRoute)
  obtain ⟨targetWitnessPath, ⟨targetWitnessRoute⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses targetChecked.val available
      witnessRegion targetWitnessEncloses
  obtain ⟨targetWitnessDepth, targetWitnessDepthProof⟩ :=
    targetWitnessRoute.hasCutDepth_exists targetWellFormed
  have depthPreserve : ∀ fuel (region : Fin input.val.regionCount),
      concreteCutDepthAux targetChecked.val fuel region =
        concreteCutDepthAux input.val fuel region := by
    intro fuel
    induction fuel with
    | zero => intro region; rfl
    | succ fuel ih =>
        intro region
        simp only [concreteCutDepthAux]
        rw [show targetChecked.val.regions region = input.val.regions region by
          simp [targetChecked, anchoredWireSplitRaw_regions]]
        cases kind : input.val.regions region with
        | sheet => rfl
        | cut parent => simp only [ih]
        | bubble parent arity => simp only [ih]
  have targetSameDepth : concreteCutDepth targetChecked.val available =
      concreteCutDepth targetChecked.val witnessRegion := by
    unfold concreteCutDepth
    rw [depthPreserve, depthPreserve]
    exact sameDepth
  have targetDepthZero := CongruenceSoundness.route_cutDepth_zero_of_equal
    targetChecked targetWitnessRoute targetWitnessDepth targetWitnessDepthProof
    targetSameDepth
  subst targetWitnessDepth
  have targetWitnessShape : targetChecked.val.nodes witness.castSucc =
      .term witnessRegion 0 term := by
    simpa [targetChecked, witnessShape] using
      anchoredWireSplitRaw_oldNode input wire endpoints target term witness
  have targetWitnessOccurs : targetChecked.val.EndpointOccurs wire.castSucc
      { node := witness.castSucc, port := .output } := by
    simpa using (anchoredWireSplitRaw_old_oldEndpointOccurs_iff input wire wire
      endpoints target term { node := witness, port := .output }).mpr
        ⟨witnessOccurs, fun _ => witnessKept⟩
  intro rels fuel original expanded collapse binders bindersCover
    binderEnumeration originalExact expandedExact sourceBody targetBody
    sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
    outerAgrees
  simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
  cases sourceItemsResult :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (original.extend available) binders
        (ConcreteElaboration.localOccurrences input.val available) with
  | none => simp [sourceItemsResult] at sourceCompiled
  | some sourceItems =>
    simp [sourceItemsResult] at sourceCompiled
    subst sourceBody
    cases targetItemsResult :
        ConcreteElaboration.compileOccurrencesWith? signature targetChecked.val
          (ConcreteElaboration.compileRegion? signature targetChecked.val fuel)
          (expanded.extend available) binders
          (ConcreteElaboration.localOccurrences targetChecked.val available) with
    | none => simp [targetChecked, targetItemsResult] at targetCompiled
    | some targetItems =>
      simp [targetChecked, targetItemsResult] at targetCompiled
      subst targetBody
      apply anchoredWireSplitRaw_available_route_equiv input wire endpoints target
        term selectedOccurs targetWellFormed wireEnclosesAvailable
        wireEnclosesTarget targetRoute fuel original expanded collapse binders
        originalExact expandedExact sourceItems targetItems sourceItemsResult
        (by simpa [targetChecked] using targetItemsResult) model named sourceOuter
        targetOuter relEnv outerAgrees
      · intro sourceLocal sourceDenotes
        apply anchoredWireSplit_witness_value_of_zero_route input wire witness
          witnessRegion term witnessShape witnessOccurs witnessRoute witnessZero
          original binders fuel sourceItems sourceItemsResult originalExact
          bindersCover binderEnumeration model named sourceOuter sourceLocal relEnv
        simpa [ConcreteElaboration.extendedEnvironment, splitExtendedEnv] using
          sourceDenotes
      · intro targetLocal targetDenotes
        apply anchoredWireSplit_witness_value_of_zero_route targetChecked
          wire.castSucc witness.castSucc witnessRegion term targetWitnessShape
          targetWitnessOccurs targetWitnessRoute targetWitnessDepthProof expanded binders
          fuel targetItems (by simpa [targetChecked] using targetItemsResult)
          expandedExact (anchoredWireSplitRaw_bindersCover input wire endpoints
            target term binders available bindersCover)
          (anchoredWireSplitRaw_binderEnumeration input wire endpoints target term
            binders available binderEnumeration)
          model named
          targetOuter targetLocal relEnv
        simpa [ConcreteElaboration.extendedEnvironment, splitExtendedEnv] using
          targetDenotes

theorem anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (regionNe : region ≠ target)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (originalExact : (original.extend region).Exact region)
    (expandedExact : (expanded.extend region).Exact region)
    (sourceBefore : ItemSeq signature (original.extend region).length rels)
    (sourceFocus : Item signature (original.extend region).length rels)
    (sourceAfter : ItemSeq signature (original.extend region).length rels)
    (targetBefore : ItemSeq signature (expanded.extend region).length rels)
    (targetFocus : Item signature (expanded.extend region).length rels)
    (targetAfter : ItemSeq signature (expanded.extend region).length rels)
    (beforeEq : sourceBefore = targetBefore.renameWires
      (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap)
    (afterEq : sourceAfter = targetAfter.renameWires
      (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin original.length → model.Carrier)
    (targetOuter : Fin expanded.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (focusEquiv : ∀ sourceRaw targetRaw,
      sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap = targetRaw →
      (denoteItem model named sourceRaw relEnv sourceFocus ↔
        denoteItem model named targetRaw relEnv targetFocus)) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val original region
          (sourceBefore.append (.cons sourceFocus sourceAfter))) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (anchoredWireSplitRaw input wire endpoints target term) expanded region
          (targetBefore.append (.cons targetFocus targetAfter))) := by
  constructor
  · intro sourceDenotes
    unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
    simp only [denoteRegion_mk] at sourceDenotes ⊢
    obtain ⟨sourceLocal, sourceCast⟩ := sourceDenotes
    let targetLocal := splitTargetLocalEnv collapse wireEnclosesTarget region
      expandedExact originalExact sourceOuter sourceLocal
    refine ⟨targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCast ⊢
    let sourceRaw := splitExtendedEnv original region sourceOuter sourceLocal
    let targetRaw := splitExtendedEnv expanded region targetOuter targetLocal
    have sourceRawItems := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original region))
      (extendWireEnv sourceOuter sourceLocal) relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))).mp sourceCast
    change denoteItemSeq model named sourceRaw relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter)) at sourceRawItems
    have envCollapse := splitExtendedEnv_collapse collapse wireEnclosesTarget
      region expandedExact originalExact sourceOuter sourceLocal
    rw [outerAgrees] at envCollapse
    change sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
      originalExact).indexMap = targetRaw at envCollapse
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded region))
      (extendWireEnv targetOuter targetLocal) relEnv
      (targetBefore.append (.cons targetFocus targetAfter))).mpr
    change denoteItemSeq model named targetRaw relEnv
      (targetBefore.append (.cons targetFocus targetAfter))
    rw [denoteItemSeq_frame] at sourceRawItems ⊢
    have targetBeforeDenotes : denoteItemSeq model named targetRaw relEnv
        targetBefore := by
      rw [beforeEq] at sourceRawItems
      rw [← envCollapse]
      exact (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetBefore).mp
            sourceRawItems.1
    have targetAfterDenotes : denoteItemSeq model named targetRaw relEnv
        targetAfter := by
      rw [afterEq] at sourceRawItems
      rw [← envCollapse]
      exact (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetAfter).mp
            sourceRawItems.2.2
    exact ⟨targetBeforeDenotes,
      (focusEquiv sourceRaw targetRaw envCollapse).mp sourceRawItems.2.1,
      targetAfterDenotes⟩
  · intro targetDenotes
    unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
    simp only [denoteRegion_mk] at targetDenotes ⊢
    obtain ⟨targetLocal, targetCast⟩ := targetDenotes
    let sourceLocal := splitSourceLocalEnvOfNe input wire endpoints target region
      term regionNe targetLocal
    refine ⟨sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetCast ⊢
    let sourceRaw := splitExtendedEnv original region sourceOuter sourceLocal
    let targetRaw := splitExtendedEnv expanded region targetOuter targetLocal
    have targetRawItems := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded region))
      (extendWireEnv targetOuter targetLocal) relEnv
      (targetBefore.append (.cons targetFocus targetAfter))).mp targetCast
    change denoteItemSeq model named targetRaw relEnv
      (targetBefore.append (.cons targetFocus targetAfter)) at targetRawItems
    have envCollapse := splitExtendedEnv_uncollapse_of_ne collapse
      wireEnclosesTarget region regionNe expandedExact originalExact sourceOuter
      targetOuter outerAgrees targetLocal
    change sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
      originalExact).indexMap = targetRaw at envCollapse
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original region))
      (extendWireEnv sourceOuter sourceLocal) relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))).mpr
    change denoteItemSeq model named sourceRaw relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))
    rw [denoteItemSeq_frame] at targetRawItems ⊢
    have sourceBeforeDenotes : denoteItemSeq model named sourceRaw relEnv
        sourceBefore := by
      rw [beforeEq]
      apply (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetBefore).mpr
      rw [envCollapse]
      exact targetRawItems.1
    have sourceAfterDenotes : denoteItemSeq model named sourceRaw relEnv
        sourceAfter := by
      rw [afterEq]
      apply (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetAfter).mpr
      rw [envCollapse]
      exact targetRawItems.2.2
    exact ⟨sourceBeforeDenotes,
      (focusEquiv sourceRaw targetRaw envCollapse).mpr targetRawItems.2.1,
      sourceAfterDenotes⟩

/-- Any complete availability kernel lifts through every unchanged compiler
frame between the root and that region. -/
theorem anchoredWireSplitRaw_compileRegion_route_to_available
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {start : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val start available path)
    {availableTargetPath : List Nat}
    (availableRoute : Diagram.Splice.RegionRoute input.val available target
      availableTargetPath)
    (site : AnchoredAvailableKernel input wire endpoints target available term
      targetWellFormed) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (original : ConcreteElaboration.WireContext input.val)
      (expanded : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term))
      (collapse : SplitContextCollapse input wire endpoints target term
        expanded original)
      (binders : ConcreteElaboration.BinderContext input.val rels)
      (bindersCover : binders.Covers start)
      (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
        input.val binders start)
      (originalExact : (original.extend start).Exact start)
      (expandedExact : (expanded.extend start).Exact start)
      (sourceBody : Region signature original.length rels)
      (targetBody : Region signature expanded.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
        (fuel + 1) start original binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (fuel + 1) start expanded binders = some targetBody)
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceOuter : Fin original.length → model.Carrier)
      (targetOuter : Fin expanded.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels)
      (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter),
      denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody := by
  induction route with
  | here => exact site
  | @step start child available rest hparent position hposition tail ih =>
      intro rels fuel original expanded collapse binders bindersCover
        binderEnumeration originalExact
        expandedExact sourceBody targetBody sourceCompiled targetCompiled model
        named sourceOuter targetOuter relEnv outerAgrees
      have startNe : start ≠ target := by
        intro equality
        subst start
        have targetEnclosesAvailable :=
          ConcreteElaboration.checked_encloses_trans input.property
            (split_direct_child_encloses hparent)
            (regionRoute_encloses input.val input.property tail)
        have availableEnclosesTarget :=
          regionRoute_encloses input.val input.property availableRoute
        have equal := ConcreteElaboration.checked_encloses_antisymm input.property
          targetEnclosesAvailable availableEnclosesTarget
        subst available
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property hparent) (regionRoute_encloses input.val input.property tail)
      have startNeAvailable : start ≠ available := by
        intro equality
        subst start
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property hparent) (regionRoute_encloses input.val input.property tail)
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val start child position hposition
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (original.extend start) binders
            (ConcreteElaboration.localOccurrences input.val start) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (anchoredWireSplitRaw input wire endpoints target term)
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints target term) fuel)
              (expanded.extend start) binders
              (ConcreteElaboration.localOccurrences
                (anchoredWireSplitRaw input wire endpoints target term) start) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          have targetLocalEq :
              ConcreteElaboration.localOccurrences
                  (anchoredWireSplitRaw input wire endpoints target term) start =
                (before ++ .child child :: after).map
                  (splitOldOccurrence input) := by
            rw [anchoredWireSplitRaw_localOccurrences_of_ne input wire endpoints
              target start term startNe, localEq]
          have sourceFramed := sourceItemsResult
          rw [localEq] at sourceFramed
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input.val fuel)
              (original.extend start) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed := targetItemsResult
          rw [targetLocalEq, List.map_append, List.map_cons] at targetFramed
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints target term) fuel)
              (expanded.extend start) binders
              (before.map (splitOldOccurrence input))
              (after.map (splitOldOccurrence input))
              (splitOldOccurrence input (.child child)) targetItems targetFramed
          cases fuel with
          | zero =>
              cases kind : input.val.regions child <;>
                simp [ConcreteElaboration.compileOccurrenceWith?, kind,
                  ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            have beforeMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints target start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent
              (tail.trans availableRoute)
              (childFuel + 1) original expanded collapse binders originalExact
              expandedExact before (by
                intro occurrence member
                rw [localEq]
                simp [member]) beforeAway
            rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
            have beforeEq : sourceBefore = targetBefore.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj beforeMap
            have afterMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints target start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent
              (tail.trans availableRoute)
              (childFuel + 1) original expanded collapse binders originalExact
              expandedExact after (by
                intro occurrence member
                rw [localEq]
                simp [member]) afterAway
            rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
            have afterEq : sourceAfter = targetAfter.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj afterMap
            have childOriginalExact := originalExact.extend_child input.property hparent
            have targetParent :
                ((anchoredWireSplitRaw input wire endpoints target term).regions
                  child).parent? = some start := by
              simpa only [anchoredWireSplitRaw_regions] using hparent
            have childExpandedExact :=
              expandedExact.extend_child targetWellFormed targetParent
            cases childKind : input.val.regions child with
            | sheet => simp [childKind, CRegion.parent?] at hparent
            | cut childParent =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start) binders with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints target term)
                      (childFuel + 1) child (expanded.extend start) binders with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  rw [sourceItemsEq, targetItemsEq]
                  apply anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne input
                    wire endpoints target start term startNe wireEnclosesTarget
                    original expanded collapse originalExact expandedExact
                    sourceBefore (.cut sourceChild) sourceAfter targetBefore
                    (.cut targetChild) targetAfter beforeEq afterEq model named
                    sourceOuter targetOuter relEnv outerAgrees
                  intro sourceRaw targetRaw agrees
                  have childEquiv := ih availableRoute site childFuel
                    (original.extend start)
                    (expanded.extend start)
                    (collapse.extend wireEnclosesTarget start expandedExact
                      originalExact) binders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      bindersCover childKind)
                    (binderEnumeration.cutChild input.property childKind)
                    childOriginalExact childExpandedExact
                    sourceChild targetChild sourceChildResult targetChildResult
                    model named sourceRaw targetRaw relEnv agrees
                  exact not_congr childEquiv
            | bubble childParent arity =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start)
                    (binders.push child arity) with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                change (ConcreteElaboration.compileRegion? signature
                    (anchoredWireSplitRaw input wire endpoints target term)
                    (childFuel + 1) child (expanded.extend start)
                    (binders.push child arity)).bind
                      (fun body => some (Item.bubble arity body)) =
                    some targetFocus at targetFocusCompiled
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints target term)
                      (childFuel + 1) child (expanded.extend start)
                      (binders.push child arity) with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  rw [sourceItemsEq, targetItemsEq]
                  apply anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne input
                    wire endpoints target start term startNe wireEnclosesTarget
                    original expanded collapse originalExact expandedExact
                    sourceBefore (.bubble arity sourceChild) sourceAfter
                    targetBefore (.bubble arity targetChild) targetAfter
                    beforeEq afterEq model named sourceOuter targetOuter relEnv
                    outerAgrees
                  intro sourceRaw targetRaw agrees
                  constructor
                  · rintro ⟨relation, sourceChildDenotes⟩
                    have childEquiv := ih availableRoute site childFuel
                      (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        bindersCover childKind)
                      (binderEnumeration.bubbleChild input.property childKind)
                      childOriginalExact childExpandedExact sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw (relation, relEnv) agrees
                    exact ⟨relation, childEquiv.mp sourceChildDenotes⟩
                  · rintro ⟨relation, targetChildDenotes⟩
                    have childEquiv := ih availableRoute site childFuel
                      (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        bindersCover childKind)
                      (binderEnumeration.bubbleChild input.property childKind)
                      childOriginalExact childExpandedExact sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw (relation, relEnv) agrees
                    exact ⟨relation, childEquiv.mpr targetChildDenotes⟩

/-- A certified descendant availability lifts through the compiler's actual
ordered-open root frame. -/
theorem anchoredWireSplitRaw_compileRoot_route_to_available
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {rootPath availableTargetPath : List Nat}
    (route : Diagram.Splice.RegionRoute input.val input.val.root available
      rootPath)
    (rootNe : input.val.root ≠ available)
    (availableRoute : Diagram.Splice.RegionRoute input.val available target
      availableTargetPath)
    (site : AnchoredAvailableKernel input wire endpoints target available term
      targetWellFormed)
    (sourceBody : Region signature
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length [])
    (targetBody : Region signature (anchoredWireSplitRawOpen input boundary wire
      endpoints target term).exposedWires.length [])
    (sourceCompiled : ConcreteElaboration.compileRoot? signature input.val
      (anchoredWireSplitSourceOpen input boundary).exposedWires
      (anchoredWireSplitSourceOpen input boundary).hiddenWires = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRoot? signature
      (anchoredWireSplitRaw input wire endpoints target term)
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).exposedWires
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).hiddenWires =
        some targetBody)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → model.Carrier) :
    denoteRegion (relCtx := []) model named
        (targetOuter ∘ anchoredWireSplitRawOpenExternalClass input boundary wire
          endpoints target term) PUnit.unit sourceBody ↔
      denoteRegion (relCtx := []) model named targetOuter PUnit.unit targetBody := by
  let source := anchoredWireSplitSourceOpen input boundary
  let expanded := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  have sourceWellFormed : source.WellFormed signature := {
    diagram_well_formed := input.property
    boundary_is_root_scoped := sourceRoot
  }
  have expandedWellFormed : expanded.WellFormed signature :=
    anchoredWireSplitRawOpen_wellFormed input boundary sourceRoot wire endpoints
      target term targetWellFormed
  have sourceExact := OpenConcreteDiagram.rootWires_exact source sourceWellFormed
  have expandedExact := OpenConcreteDiagram.rootWires_exact expanded
    expandedWellFormed
  let collapse := SplitContextCollapse.ofExact input wire endpoints target term
    wireEnclosesTarget input.val.root expanded.rootWires source.rootWires
    expandedExact sourceExact
  have rootTargetNe : input.val.root ≠ target := by
    intro equality
    subst target
    have rootAbove := regionRoute_encloses input.val input.property route
    have availableAbove :=
      regionRoute_encloses input.val input.property availableRoute
    have availableEq := ConcreteElaboration.checked_encloses_antisymm
      input.property availableAbove rootAbove
    exact rootNe availableEq.symm
  cases route with
  | here => exact (rootNe rfl).elim
  | @step _ child _ rest parentEq position positionEq tail =>
    change ConcreteElaboration.compileRoot? signature input.val
        source.exposedWires source.hiddenWires = some sourceBody at sourceCompiled
    change ConcreteElaboration.compileRoot? signature expanded.diagram
        expanded.exposedWires expanded.hiddenWires = some targetBody at targetCompiled
    simp only [ConcreteElaboration.compileRoot?] at sourceCompiled targetCompiled
    change (ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val
          input.val.regionCount)
        source.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.val input.val.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot source.exposedWires
            source.hiddenWires items)) = some sourceBody at sourceCompiled
    change (ConcreteElaboration.compileOccurrencesWith? signature expanded.diagram
        (ConcreteElaboration.compileRegion? signature expanded.diagram
          input.val.regionCount)
        expanded.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences expanded.diagram input.val.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot expanded.exposedWires
            expanded.hiddenWires items)) = some targetBody at targetCompiled
    cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith?
        signature input.val
        (ConcreteElaboration.compileRegion? signature input.val
          input.val.regionCount)
        source.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.val input.val.root) with
    | none => simp [sourceItemsResult] at sourceCompiled
    | some sourceItems =>
      simp [sourceItemsResult] at sourceCompiled
      subst sourceBody
      cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith?
          signature expanded.diagram
          (ConcreteElaboration.compileRegion? signature expanded.diagram
            input.val.regionCount)
          expanded.rootWires ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences expanded.diagram input.val.root) with
      | none => simp [expanded, targetItemsResult] at targetCompiled
      | some targetItems =>
        simp [expanded, targetItemsResult] at targetCompiled
        subst targetBody
        obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
          localOccurrences_split_at_child input.val input.val.root child position
            positionEq
        have targetLocalEq : ConcreteElaboration.localOccurrences
              expanded.diagram input.val.root =
            (before ++ .child child :: after).map (splitOldOccurrence input) := by
          change ConcreteElaboration.localOccurrences
              (anchoredWireSplitRaw input wire endpoints target term)
              input.val.root = _
          rw [anchoredWireSplitRaw_localOccurrences_of_ne input wire endpoints
            target input.val.root term rootTargetNe, localEq]
        have sourceFramed := sourceItemsResult
        rw [localEq] at sourceFramed
        obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
            sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
          compileOccurrencesWith?_frame_split
            (ConcreteElaboration.compileRegion? signature input.val
              input.val.regionCount)
            source.rootWires ConcreteElaboration.BinderContext.empty before after
            (.child child) sourceItems sourceFramed
        have targetFramed := targetItemsResult
        rw [targetLocalEq, List.map_append, List.map_cons] at targetFramed
        obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
            targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
          compileOccurrencesWith?_frame_split
            (ConcreteElaboration.compileRegion? signature expanded.diagram
              input.val.regionCount)
            expanded.rootWires ConcreteElaboration.BinderContext.empty
            (before.map (splitOldOccurrence input))
            (after.map (splitOldOccurrence input))
            (splitOldOccurrence input (.child child)) targetItems targetFramed
        dsimp only [expanded, anchoredWireSplitRawOpen] at targetBeforeCompiled targetFocusCompiled targetAfterCompiled
        have beforeMap := anchoredWireSplitRaw_compileRootOccurrencesAway input
          wire endpoints target input.val.root child term selectedOccurs
          targetWellFormed wireEnclosesTarget parentEq
          (tail.trans availableRoute) input.val.regionCount source.rootWires
          expanded.rootWires collapse ConcreteElaboration.BinderContext.empty
          sourceExact expandedExact before (by
            intro occurrence member
            rw [localEq]
            simp [member]) beforeAway
        dsimp only [expanded, anchoredWireSplitRawOpen] at beforeMap
        rw [sourceBeforeCompiled] at beforeMap
        have beforeMapped := congrArg
          (Option.map (ItemSeq.renameWires collapse.indexMap))
          targetBeforeCompiled
        have beforeEq : sourceBefore =
            targetBefore.renameWires collapse.indexMap :=
          Option.some.inj (beforeMap.trans beforeMapped)
        have afterMap := anchoredWireSplitRaw_compileRootOccurrencesAway input
          wire endpoints target input.val.root child term selectedOccurs
          targetWellFormed wireEnclosesTarget parentEq
          (tail.trans availableRoute) input.val.regionCount source.rootWires
          expanded.rootWires collapse ConcreteElaboration.BinderContext.empty
          sourceExact expandedExact after (by
            intro occurrence member
            rw [localEq]
            simp [member]) afterAway
        dsimp only [expanded, anchoredWireSplitRawOpen] at afterMap
        rw [sourceAfterCompiled] at afterMap
        have afterMapped := congrArg
          (Option.map (ItemSeq.renameWires collapse.indexMap))
          targetAfterCompiled
        have afterEq : sourceAfter =
            targetAfter.renameWires collapse.indexMap :=
          Option.some.inj (afterMap.trans afterMapped)
        cases countEq : input.val.regionCount with
        | zero =>
          let impossible : Fin 0 := Fin.cast (by simpa [countEq]) child
          exact Fin.elim0 impossible
        | succ childFuel =>
          change (input.val.regions child).parent? = some input.val.root at parentEq
          cases childKind : input.val.regions child with
          | sheet => simp [childKind, CRegion.parent?] at parentEq
          | cut parent =>
            have parentIsRoot : parent = input.val.root := by
              simpa [childKind, CRegion.parent?] using parentEq
            subst parent
            simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
              splitOldOccurrence, anchoredWireSplitRaw_regions]
              at sourceFocusCompiled targetFocusCompiled
            rw [countEq] at sourceFocusCompiled targetFocusCompiled
            cases sourceChildResult : ConcreteElaboration.compileRegion?
                signature input.val (childFuel + 1) child source.rootWires
                ConcreteElaboration.BinderContext.empty with
            | none => simp [sourceChildResult] at sourceFocusCompiled
            | some sourceChild =>
              simp [sourceChildResult] at sourceFocusCompiled
              subst sourceFocus
              cases targetChildResult : ConcreteElaboration.compileRegion?
                  signature (anchoredWireSplitRaw input wire endpoints target term)
                  (childFuel + 1) child
                  expanded.rootWires ConcreteElaboration.BinderContext.empty with
              | none =>
                dsimp only [expanded, anchoredWireSplitRawOpen] at targetChildResult
                have bindEq := congrArg
                  (fun result => result.bind (fun body => some (Item.cut body)))
                  targetChildResult
                simp only [Option.bind_none] at bindEq
                have impossible := bindEq.symm.trans targetFocusCompiled
                simp at impossible
              | some targetChild =>
                dsimp only [expanded, anchoredWireSplitRawOpen] at targetChildResult
                have bindEq := congrArg
                  (fun result => result.bind (fun body => some (Item.cut body)))
                  targetChildResult
                simp only [Option.bind_some] at bindEq
                have focusEq : Item.cut targetChild = targetFocus :=
                  Option.some.inj (bindEq.symm.trans targetFocusCompiled)
                subst targetFocus
                rw [sourceItemsEq, targetItemsEq]
                change ItemSeq signature
                    (anchoredWireSplitSourceOpen input boundary).rootWires.length
                    [] at sourceBefore sourceAfter
                change Region signature
                    (anchoredWireSplitSourceOpen input boundary).rootWires.length
                    [] at sourceChild
                change ItemSeq signature
                    (anchoredWireSplitRawOpen input boundary wire endpoints target
                      term).rootWires.length [] at targetBefore targetAfter
                change Region signature
                    (anchoredWireSplitRawOpen input boundary wire endpoints target
                      term).rootWires.length [] at targetChild
                apply anchoredWireSplitRaw_finishRoot_away_equiv input boundary
                  wire endpoints target term rootTargetNe collapse
                  sourceExact.nodup
                  (sourceBefore.append (.cons (.cut sourceChild) sourceAfter))
                  (targetBefore.append (.cons (.cut targetChild) targetAfter)) _
                  model named targetOuter
                intro currentModel currentNamed sourceRaw targetRaw rawAgrees
                rw [denoteItemSeq_frame, denoteItemSeq_frame]
                constructor
                · rintro ⟨beforeDenotes, focusDenotes, afterDenotes⟩
                  have childEquiv :=
                    anchoredWireSplitRaw_compileRegion_route_to_available input
                      wire endpoints target available term selectedOccurs
                      targetWellFormed wireEnclosesTarget tail availableRoute site
                      childFuel source.rootWires expanded.rootWires collapse
                      ConcreteElaboration.BinderContext.empty
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        (ConcreteElaboration.BinderContext.empty_covers_root
                          input.property) childKind)
                      ((ConcreteElaboration.BinderContext.Enumeration.empty
                        input.val).cutChild input.property childKind)
                      (sourceExact.extend_child input.property parentEq)
                      (expandedExact.extend_child targetWellFormed (by
                        simpa only [anchoredWireSplitRaw_regions] using parentEq))
                      sourceChild targetChild sourceChildResult targetChildResult
                      currentModel currentNamed sourceRaw targetRaw PUnit.unit
                      rawAgrees
                  refine ⟨?_, (not_congr childEquiv).mp focusDenotes, ?_⟩
                  · have renamed : denoteItemSeq (relCtx := []) currentModel
                        currentNamed sourceRaw PUnit.unit
                        (targetBefore.renameWires collapse.indexMap) := by
                      exact beforeEq ▸ beforeDenotes
                    have transported := (denoteItemSeq_renameWires
                      (relCtx := []) currentModel currentNamed collapse.indexMap
                      sourceRaw PUnit.unit targetBefore).1 renamed
                    exact rawAgrees ▸ transported
                  · have renamed : denoteItemSeq (relCtx := []) currentModel
                        currentNamed sourceRaw PUnit.unit
                        (targetAfter.renameWires collapse.indexMap) := by
                      exact afterEq ▸ afterDenotes
                    have transported := (denoteItemSeq_renameWires
                      (relCtx := []) currentModel currentNamed collapse.indexMap
                      sourceRaw PUnit.unit targetAfter).1 renamed
                    exact rawAgrees ▸ transported
                · rintro ⟨beforeDenotes, focusDenotes, afterDenotes⟩
                  have childEquiv :=
                    anchoredWireSplitRaw_compileRegion_route_to_available input
                      wire endpoints target available term selectedOccurs
                      targetWellFormed wireEnclosesTarget tail availableRoute site
                      childFuel source.rootWires expanded.rootWires collapse
                      ConcreteElaboration.BinderContext.empty
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        (ConcreteElaboration.BinderContext.empty_covers_root
                          input.property) childKind)
                      ((ConcreteElaboration.BinderContext.Enumeration.empty
                        input.val).cutChild input.property childKind)
                      (sourceExact.extend_child input.property parentEq)
                      (expandedExact.extend_child targetWellFormed (by
                        simpa only [anchoredWireSplitRaw_regions] using parentEq))
                      sourceChild targetChild sourceChildResult targetChildResult
                      currentModel currentNamed sourceRaw targetRaw PUnit.unit
                      rawAgrees
                  refine ⟨?_, (not_congr childEquiv).mpr focusDenotes, ?_⟩
                  · rw [beforeEq]
                    apply (denoteItemSeq_renameWires (relCtx := []) currentModel
                      currentNamed collapse.indexMap sourceRaw PUnit.unit
                      targetBefore).2
                    exact rawAgrees.symm ▸ beforeDenotes
                  · rw [afterEq]
                    apply (denoteItemSeq_renameWires (relCtx := []) currentModel
                      currentNamed collapse.indexMap sourceRaw PUnit.unit
                      targetAfter).2
                    exact rawAgrees.symm ▸ afterDenotes
          | bubble parent arity =>
            have parentIsRoot : parent = input.val.root := by
              simpa [childKind, CRegion.parent?] using parentEq
            subst parent
            simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
              splitOldOccurrence, anchoredWireSplitRaw_regions]
              at sourceFocusCompiled targetFocusCompiled
            rw [countEq] at sourceFocusCompiled targetFocusCompiled
            cases sourceChildResult : ConcreteElaboration.compileRegion?
                signature input.val (childFuel + 1) child source.rootWires
                (ConcreteElaboration.BinderContext.empty.push child arity) with
            | none => simp [sourceChildResult] at sourceFocusCompiled
            | some sourceChild =>
              simp [sourceChildResult] at sourceFocusCompiled
              subst sourceFocus
              cases targetChildResult : ConcreteElaboration.compileRegion?
                  signature (anchoredWireSplitRaw input wire endpoints target term)
                  (childFuel + 1) child
                  expanded.rootWires
                  (ConcreteElaboration.BinderContext.empty.push child arity) with
              | none =>
                dsimp only [expanded, anchoredWireSplitRawOpen] at targetChildResult
                have bindEq := congrArg
                  (fun result => result.bind
                    (fun body => some (Item.bubble arity body)))
                  targetChildResult
                simp only [Option.bind_none] at bindEq
                have impossible := bindEq.symm.trans targetFocusCompiled
                simp at impossible
              | some targetChild =>
                dsimp only [expanded, anchoredWireSplitRawOpen] at targetChildResult
                have bindEq := congrArg
                  (fun result => result.bind
                    (fun body => some (Item.bubble arity body)))
                  targetChildResult
                simp only [Option.bind_some] at bindEq
                have focusEq : Item.bubble arity targetChild = targetFocus :=
                  Option.some.inj (bindEq.symm.trans targetFocusCompiled)
                subst targetFocus
                rw [sourceItemsEq, targetItemsEq]
                change ItemSeq signature
                    (anchoredWireSplitSourceOpen input boundary).rootWires.length
                    [] at sourceBefore sourceAfter
                change Region signature
                    (anchoredWireSplitSourceOpen input boundary).rootWires.length
                    [arity] at sourceChild
                change ItemSeq signature
                    (anchoredWireSplitRawOpen input boundary wire endpoints target
                      term).rootWires.length [] at targetBefore targetAfter
                change Region signature
                    (anchoredWireSplitRawOpen input boundary wire endpoints target
                      term).rootWires.length [arity] at targetChild
                apply anchoredWireSplitRaw_finishRoot_away_equiv input boundary
                  wire endpoints target term rootTargetNe collapse
                  sourceExact.nodup
                  (sourceBefore.append
                    (.cons (.bubble arity sourceChild) sourceAfter))
                  (targetBefore.append
                    (.cons (.bubble arity targetChild) targetAfter)) _ model
                  named targetOuter
                intro currentModel currentNamed sourceRaw targetRaw rawAgrees
                rw [denoteItemSeq_frame, denoteItemSeq_frame]
                have childEquiv : ∀ relation : Relation currentModel.Carrier arity,
                    denoteRegion (relCtx := [arity]) currentModel currentNamed sourceRaw
                        (relation, PUnit.unit) sourceChild ↔
                      denoteRegion (relCtx := [arity]) currentModel currentNamed targetRaw
                        (relation, PUnit.unit) targetChild := by
                  intro relation
                  exact anchoredWireSplitRaw_compileRegion_route_to_available
                    input wire endpoints target available term selectedOccurs
                    targetWellFormed wireEnclosesTarget tail availableRoute site
                    childFuel source.rootWires expanded.rootWires collapse
                    (ConcreteElaboration.BinderContext.empty.push child arity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      (ConcreteElaboration.BinderContext.empty_covers_root
                        input.property) childKind)
                    ((ConcreteElaboration.BinderContext.Enumeration.empty
                      input.val).bubbleChild input.property childKind)
                    (sourceExact.extend_child input.property parentEq)
                    (expandedExact.extend_child targetWellFormed (by
                      simpa only [anchoredWireSplitRaw_regions] using parentEq))
                    sourceChild targetChild sourceChildResult targetChildResult
                    currentModel currentNamed sourceRaw targetRaw
                    (relation, PUnit.unit) rawAgrees
                constructor
                · rintro ⟨beforeDenotes, ⟨relation, focusDenotes⟩,
                    afterDenotes⟩
                  refine ⟨?_, ⟨relation, (childEquiv relation).mp focusDenotes⟩,
                    ?_⟩
                  · have renamed : denoteItemSeq (relCtx := []) currentModel
                        currentNamed sourceRaw PUnit.unit
                        (targetBefore.renameWires collapse.indexMap) := by
                      exact beforeEq ▸ beforeDenotes
                    have transported := (denoteItemSeq_renameWires
                      (relCtx := []) currentModel currentNamed collapse.indexMap
                      sourceRaw PUnit.unit targetBefore).1 renamed
                    exact rawAgrees ▸ transported
                  · have renamed : denoteItemSeq (relCtx := []) currentModel
                        currentNamed sourceRaw PUnit.unit
                        (targetAfter.renameWires collapse.indexMap) := by
                      exact afterEq ▸ afterDenotes
                    have transported := (denoteItemSeq_renameWires
                      (relCtx := []) currentModel currentNamed collapse.indexMap
                      sourceRaw PUnit.unit targetAfter).1 renamed
                    exact rawAgrees ▸ transported
                · rintro ⟨beforeDenotes, ⟨relation, focusDenotes⟩,
                    afterDenotes⟩
                  refine ⟨?_, ⟨relation, (childEquiv relation).mpr focusDenotes⟩,
                    ?_⟩
                  · rw [beforeEq]
                    apply (denoteItemSeq_renameWires (relCtx := []) currentModel
                      currentNamed collapse.indexMap sourceRaw PUnit.unit
                      targetBefore).2
                    exact rawAgrees.symm ▸ beforeDenotes
                  · rw [afterEq]
                    apply (denoteItemSeq_renameWires (relCtx := []) currentModel
                      currentNamed collapse.indexMap sourceRaw PUnit.unit
                      targetAfter).2
                    exact rawAgrees.symm ▸ afterDenotes

end AnchoredWireSoundness

end VisualProof.Rule
