import VisualProof.Rule.Soundness.AttachmentAliasSemanticCompiler

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Semantic

private theorem listGet_cast_of_eq {left right : List α}
    (equality : left = right) (index : Fin left.length) :
    left.get index = right.get (Fin.cast (congrArg List.length equality) index) := by
  subst right
  rfl

private theorem listGet_map_cast_soundness (values : List α) (f : α → β)
    (index : Fin values.length) :
    (values.map f).get
        (Fin.cast (List.length_map (as := values) f).symm index) =
      f (values.get index) := by
  simpa only [List.get_eq_getElem, Fin.val_cast] using
    (List.getElem_map (l := values) (i := index.val) f)

/-- Away from the root, materialization changes only the representation of
wire identities: the exact local list is the ordered lift of the source list. -/
theorem materialized_exactScopeWires_of_ne_root
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer region : Fin pattern.diagram.regionCount)
    (hne : region ≠ pattern.diagram.root) :
    ConcreteElaboration.exactScopeWires
        (materializedDiagram pattern attachment bodyContainer) region =
      (ConcreteElaboration.exactScopeWires pattern.diagram region).map
        (liftOldWire pattern attachment) := by
  unfold ConcreteElaboration.exactScopeWires filterFin
  change List.filter _
      (allFin (pattern.diagram.wireCount + aliasCount pattern attachment)) = _
  rw [allFin_add pattern.diagram.wireCount (aliasCount pattern attachment)]
  rw [List.filter_append, List.filter_map, List.filter_map]
  have oldFilter :
      List.filter
          ((fun wire => decide
            (((materializedDiagram pattern attachment bodyContainer).wires
              wire).scope = region)) ∘
            Fin.castAdd (aliasCount pattern attachment))
          (allFin pattern.diagram.wireCount) =
        List.filter
          (fun wire => decide ((pattern.diagram.wires wire).scope = region))
          (allFin pattern.diagram.wireCount) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin pattern.diagram.wireCount))
    funext wire
    simp [materializedDiagram, liftOldWire]
  have aliasEmpty :
      List.filter
          ((fun wire => decide
            (((materializedDiagram pattern attachment bodyContainer).wires
              wire).scope = region)) ∘
            Fin.natAdd pattern.diagram.wireCount)
          (allFin (aliasCount pattern attachment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro aliasIndex _ member
    apply hne
    simpa [materializedDiagram] using (of_decide_eq_true member).symm
  have aliasMapped :
      List.map (Fin.natAdd pattern.diagram.wireCount)
        (List.filter
          ((fun wire => decide
            (((materializedDiagram pattern attachment bodyContainer).wires
              wire).scope = region)) ∘ Fin.natAdd pattern.diagram.wireCount)
          (allFin (aliasCount pattern attachment))) = [] := by
    rw [aliasEmpty]
    rfl
  calc
    _ = List.map (Fin.castAdd (aliasCount pattern attachment))
          (List.filter
            ((fun wire => decide
              (((materializedDiagram pattern attachment bodyContainer).wires
                wire).scope = region)) ∘
              Fin.castAdd (aliasCount pattern attachment))
            (allFin pattern.diagram.wireCount)) ++ [] :=
      congrArg
        (fun tail => List.map (Fin.castAdd (aliasCount pattern attachment))
          (List.filter
            ((fun wire => decide
              (((materializedDiagram pattern attachment bodyContainer).wires
                wire).scope = region)) ∘
              Fin.castAdd (aliasCount pattern attachment))
            (allFin pattern.diagram.wireCount)) ++ tail) aliasMapped
    _ = _ := by
      rw [List.append_nil]
      simpa [liftOldWire] using congrArg
        (List.map (Fin.castAdd (aliasCount pattern attachment))) oldFilter

theorem materialized_exactScopeWires_length_of_ne_root
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer region : Fin pattern.diagram.regionCount)
    (hne : region ≠ pattern.diagram.root) :
    (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern attachment bodyContainer) region).length =
    (ConcreteElaboration.exactScopeWires pattern.diagram region).length := by
  rw [materialized_exactScopeWires_of_ne_root pattern attachment bodyContainer
    region hne]
  exact List.length_map _

noncomputable def extendCollapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region) :
    ContextCollapse pattern attachment spine
      (expanded.extend region) (original.extend region) :=
  ContextCollapse.ofExact pattern attachment spine contract region
    (expanded.extend region) (original.extend region) expandedExact originalExact

theorem extendCollapse_index_inherited
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin expanded.length) :
    (extendCollapse pattern attachment spine contract expanded original collapse
        region expandedExact originalExact).indexMap
          (expanded.outerIndex region index) =
      original.outerIndex region (collapse.indexMap index) := by
  apply Fin.ext
  exact (List.getElem_inj originalExact.nodup).mp (by
    have mapped := (extendCollapse pattern attachment spine contract expanded
      original collapse region expandedExact originalExact).get
        (expanded.outerIndex region index)
    have expandedGet : (expanded.extend region).get
        (expanded.outerIndex region index) = expanded.get index := by
      simpa only [List.get_eq_getElem] using expanded.extend_outer region index
    rw [expandedGet] at mapped
    have originalGet : (original.extend region).get
        (original.outerIndex region (collapse.indexMap index)) =
          original.get (collapse.indexMap index) := by
      simpa only [List.get_eq_getElem] using
        original.extend_outer region (collapse.indexMap index)
    exact (mapped.trans (collapse.get index).symm).trans originalGet.symm)

theorem extendCollapse_index_local
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (hne : region ≠ pattern.val.diagram.root)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern.val attachment spine.bodyContainer)
        region).length) :
    (extendCollapse pattern attachment spine contract expanded original collapse
        region expandedExact originalExact).indexMap
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend expanded region).symm
            (Fin.natAdd expanded.length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend original region).symm
        (Fin.natAdd original.length
          (Fin.cast
            (materialized_exactScopeWires_length_of_ne_root pattern.val attachment
              spine.bodyContainer region hne) index)) := by
  let sourceIndex := Fin.cast
    (materialized_exactScopeWires_length_of_ne_root pattern.val attachment
      spine.bodyContainer region hne) index
  apply Fin.ext
  exact (List.getElem_inj originalExact.nodup).mp (by
    have mapped := (extendCollapse pattern attachment spine contract expanded
      original collapse region expandedExact originalExact).get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length index))
    have expandedGet : (expanded.extend region).get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length index)) =
        (ConcreteElaboration.exactScopeWires
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          region).get index := by
      simpa only [List.get_eq_getElem] using expanded.extend_local region index
    rw [expandedGet] at mapped
    have targetGet := listGet_cast_of_eq
      (materialized_exactScopeWires_of_ne_root pattern.val attachment
        spine.bodyContainer region hne) index
    have targetGet' :
        (ConcreteElaboration.exactScopeWires
          (materializedDiagram pattern.val attachment spine.bodyContainer)
            region).get index =
          liftOldWire pattern.val attachment
            ((ConcreteElaboration.exactScopeWires pattern.val.diagram region).get
              sourceIndex) := by
      simpa [sourceIndex] using targetGet.trans
        (listGet_map_cast_soundness
          (ConcreteElaboration.exactScopeWires pattern.val.diagram region)
          (liftOldWire pattern.val attachment) sourceIndex)
    rw [targetGet', collapseWire_old] at mapped
    have originalGet : (original.extend region).get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original region).symm
          (Fin.natAdd original.length sourceIndex)) =
        (ConcreteElaboration.exactScopeWires pattern.val.diagram region).get
          sourceIndex := by
      simpa only [List.get_eq_getElem] using
        original.extend_local region sourceIndex
    exact mapped.trans originalGet.symm)

theorem extendCollapse_oldIndex_inherited
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin original.length) :
    (extendCollapse pattern attachment spine contract expanded original collapse
        region expandedExact originalExact).oldIndex
          (original.outerIndex region index) =
      expanded.outerIndex region (collapse.oldIndex index) := by
  apply Fin.ext
  exact (List.getElem_inj expandedExact.nodup).mp (by
    have oldGet := (extendCollapse pattern attachment spine contract expanded
      original collapse region expandedExact originalExact).old_get
        (original.outerIndex region index)
    have originalGet : (original.extend region).get
        (original.outerIndex region index) = original.get index := by
      simpa only [List.get_eq_getElem] using original.extend_outer region index
    rw [originalGet] at oldGet
    have expandedGet : (expanded.extend region).get
        (expanded.outerIndex region (collapse.oldIndex index)) =
          expanded.get (collapse.oldIndex index) := by
      simpa only [List.get_eq_getElem] using
        expanded.extend_outer region (collapse.oldIndex index)
    exact oldGet.trans ((collapse.old_get index).symm.trans expandedGet.symm))

theorem extendCollapse_oldIndex_local
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (hne : region ≠ pattern.val.diagram.root)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      pattern.val.diagram region).length) :
    (extendCollapse pattern attachment spine contract expanded original collapse
        region expandedExact originalExact).oldIndex
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend original region).symm
            (Fin.natAdd original.length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend expanded region).symm
        (Fin.natAdd expanded.length
          (Fin.cast
            (materialized_exactScopeWires_length_of_ne_root pattern.val attachment
              spine.bodyContainer region hne).symm index)) := by
  apply Fin.ext
  exact (List.getElem_inj expandedExact.nodup).mp (by
    have oldGet := (extendCollapse pattern attachment spine contract expanded
      original collapse region expandedExact originalExact).old_get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original region).symm
          (Fin.natAdd original.length index))
    have originalGet : (original.extend region).get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original region).symm
          (Fin.natAdd original.length index)) =
        (ConcreteElaboration.exactScopeWires pattern.val.diagram region).get
          index := by
      simpa only [List.get_eq_getElem] using original.extend_local region index
    rw [originalGet] at oldGet
    have scopeEq := materialized_exactScopeWires_of_ne_root pattern.val attachment
      spine.bodyContainer region hne
    let targetIndex := Fin.cast
      (materialized_exactScopeWires_length_of_ne_root pattern.val attachment
        spine.bodyContainer region hne).symm index
    have targetGet := listGet_cast_of_eq scopeEq targetIndex
    have targetGet' :
        (ConcreteElaboration.exactScopeWires
          (materializedDiagram pattern.val attachment spine.bodyContainer)
            region).get targetIndex =
          liftOldWire pattern.val attachment
            ((ConcreteElaboration.exactScopeWires pattern.val.diagram region).get
              index) := by
      simpa [targetIndex] using targetGet.trans
        (listGet_map_cast_soundness
          (ConcreteElaboration.exactScopeWires pattern.val.diagram region)
          (liftOldWire pattern.val attachment) index)
    have expandedGet : (expanded.extend region).get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length
            targetIndex)) =
        liftOldWire pattern.val attachment
          ((ConcreteElaboration.exactScopeWires pattern.val.diagram region).get
            index) := by
      have localGet : (expanded.extend region).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend expanded region).symm
            (Fin.natAdd expanded.length targetIndex)) =
          (ConcreteElaboration.exactScopeWires
            (materializedDiagram pattern.val attachment spine.bodyContainer)
              region).get targetIndex := by
        simpa only [List.get_eq_getElem] using
          expanded.extend_local region targetIndex
      exact localGet.trans targetGet'
    exact oldGet.trans expandedGet.symm)

def extendedEnv
    (context : ConcreteElaboration.WireContext input)
    (region : Fin input.regionCount)
    (outer : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires input region).length → D) :
    Fin (context.extend region).length → D :=
  ConcreteElaboration.extendedEnvironment context region outer localEnv

theorem extendedEnv_outer
    (context : ConcreteElaboration.WireContext input)
    (region : Fin input.regionCount)
    (outer : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires input region).length → D)
    (index : Fin context.length) :
    extendedEnv context region outer localEnv (context.outerIndex region index) =
      outer index := by
  unfold extendedEnv ConcreteElaboration.extendedEnvironment
  change extendWireEnv outer localEnv
      (Fin.cast (ConcreteElaboration.WireContext.length_extend context region)
        (context.outerIndex region index)) = outer index
  rw [show Fin.cast _ (context.outerIndex region index) =
      Fin.castAdd (ConcreteElaboration.exactScopeWires input region).length index by
    apply Fin.ext
    rfl]
  exact Fin.addCases_left index

noncomputable def targetLocal
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      pattern.val.diagram region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern.val attachment spine.bodyContainer)
        region).length → D :=
  fun index => extendedEnv original region sourceOuter sourceLocal
    ((extendCollapse pattern attachment spine contract expanded original collapse
      region expandedExact originalExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded region).symm
          (Fin.natAdd expanded.length index)))

theorem extendedEnv_collapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      pattern.val.diagram region).length → D) :
    extendedEnv original region sourceOuter sourceLocal ∘
        (extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).indexMap =
      extendedEnv expanded region (sourceOuter ∘ collapse.indexMap)
        (targetLocal pattern attachment spine contract expanded original collapse
          region expandedExact originalExact sourceOuter sourceLocal) := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by apply Fin.ext; rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · rw [show Fin.cast _ (Fin.castAdd _ inherited) =
        expanded.outerIndex region inherited by apply Fin.ext; rfl]
    change extendedEnv original region sourceOuter sourceLocal
        ((extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).indexMap
            (expanded.outerIndex region inherited)) = _
    rw [extendCollapse_index_inherited pattern attachment spine contract
      expanded original collapse region expandedExact originalExact inherited]
    rw [extendedEnv_outer, extendedEnv_outer]
    rfl
  · simp [targetLocal, extendedEnv, ConcreteElaboration.extendedEnvironment,
      extendWireEnv, Function.comp_def]

def sourceLocal
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (region : Fin pattern.val.diagram.regionCount)
    (hne : region ≠ pattern.val.diagram.root)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern.val attachment spine.bodyContainer)
        region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires pattern.val.diagram region).length → D :=
  targetLocal ∘ Fin.cast
    (materialized_exactScopeWires_length_of_ne_root pattern.val attachment
      spine.bodyContainer region hne).symm

theorem extendedEnv_uncollapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (hne : region ≠ pattern.val.diagram.root)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (targetLocalEnv : Fin (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern.val attachment spine.bodyContainer)
        region).length → D) :
    extendedEnv original region sourceOuter
          (sourceLocal pattern attachment spine region hne targetLocalEnv) ∘
        (extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).indexMap =
      extendedEnv expanded region targetOuter targetLocalEnv := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded region).symm
      split = targetIndex := by apply Fin.ext; rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · rw [show Fin.cast _ (Fin.castAdd _ inherited) =
        expanded.outerIndex region inherited by apply Fin.ext; rfl]
    change extendedEnv original region sourceOuter
        (sourceLocal pattern attachment spine region hne targetLocalEnv)
        ((extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).indexMap
            (expanded.outerIndex region inherited)) = _
    rw [extendCollapse_index_inherited pattern attachment spine contract
      expanded original collapse region expandedExact originalExact inherited]
    rw [extendedEnv_outer, extendedEnv_outer]
    exact congrFun outerAgrees inherited
  · change extendedEnv original region sourceOuter
        (sourceLocal pattern attachment spine region hne targetLocalEnv)
        ((extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).indexMap
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend expanded region).symm
              (Fin.natAdd expanded.length localIndex))) = _
    rw [extendCollapse_index_local pattern attachment spine contract expanded
      original collapse region hne expandedExact originalExact localIndex]
    simp [sourceLocal, extendedEnv, ConcreteElaboration.extendedEnvironment,
      extendWireEnv, Function.comp_def]

/-- The canonical lifted-old indices transport an arbitrary target local
valuation back to the source without imposing any equality on fresh aliases. -/
theorem extendedEnv_oldIndex
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (expanded : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (original : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine expanded original)
    (region : Fin pattern.val.diagram.regionCount)
    (hne : region ≠ pattern.val.diagram.root)
    (expandedExact : (expanded.extend region).Exact region)
    (originalExact : (original.extend region).Exact region)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerEq : sourceOuter = targetOuter ∘ collapse.oldIndex)
    (targetLocalEnv : Fin (ConcreteElaboration.exactScopeWires
      (materializedDiagram pattern.val attachment spine.bodyContainer)
        region).length → D) :
    extendedEnv original region sourceOuter
        (sourceLocal pattern attachment spine region hne targetLocalEnv) =
      extendedEnv expanded region targetOuter targetLocalEnv ∘
        (extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).oldIndex := by
  funext sourceIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend original region) sourceIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend original region).symm
      split = sourceIndex := by apply Fin.ext; rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · rw [show Fin.cast _ (Fin.castAdd _ inherited) =
        original.outerIndex region inherited by apply Fin.ext; rfl]
    change extendedEnv original region sourceOuter
        (sourceLocal pattern attachment spine region hne targetLocalEnv)
        (original.outerIndex region inherited) =
      extendedEnv expanded region targetOuter targetLocalEnv
        ((extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).oldIndex
            (original.outerIndex region inherited))
    rw [extendCollapse_oldIndex_inherited pattern attachment spine contract
      expanded original collapse region expandedExact originalExact inherited]
    rw [extendedEnv_outer, extendedEnv_outer, outerEq]
    rfl
  · change extendedEnv original region sourceOuter
        (sourceLocal pattern attachment spine region hne targetLocalEnv)
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original region).symm
          (Fin.natAdd original.length localIndex)) =
      extendedEnv expanded region targetOuter targetLocalEnv
        ((extendCollapse pattern attachment spine contract expanded original
          collapse region expandedExact originalExact).oldIndex
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend original region).symm
              (Fin.natAdd original.length localIndex)))
    rw [extendCollapse_oldIndex_local pattern attachment spine contract expanded
      original collapse region hne expandedExact originalExact localIndex]
    simp [sourceLocal, extendedEnv, ConcreteElaboration.extendedEnvironment,
      extendWireEnv, Function.comp_def]

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
