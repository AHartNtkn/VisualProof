import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural.Blank

def blankPattern : OpenDiagram [] where
  external := []
  boundaryWire := .nil
  boundarySurjective := fun wire => Fin.elim0 wire
  body := Region.blank []
  canonical := by
    simp [Region.blank, Region.Canonical, ItemSeq.ChildrenCanonical]
  externalTwoEnded := by
    intro signature wire
    cases wire

/-- Instantiating the literal blank pattern is a presentation of the blank
region. -/
noncomputable def blankPatternInstantiationIso
    (application : Vars wires []) :
    RegionIso (WireEquiv.refl wires)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application) (Region.blank wires) := by
  cases application
  let inner := RegionIso.blankConjoin (Region.blank (wires ++ []))
  let hosted := RegionIso.adjoinAt [] .nil inner
  let collapsed := hosted.trans
    (RegionIso.adjoinAtNil (Region.blank (wires ++ []))).symm
  simpa [
    VisualProof.Rule.Comprehension.Instantiation.instantiate,
    blankPattern, Region.blank, Region.renameWires] using collapsed

def supportBlankTail (wires : List Sig) : ItemSeq wires :=
  (Erasure.Exposure.supportPins
      (Region.ofItems (ItemSeq.nil : ItemSeq wires)) wires
      (Erasure.Exposure.identityBoundary wires)).renameWires
    (WireEquiv.appendNil wires).toRenaming

theorem supportBlankMaterial_canonical (wires : List Sig) :
    (Region.ofItems (ItemSeq.nil : ItemSeq wires)).Canonical := by
  constructor
  · intro localIndex
    exact Fin.elim0 localIndex
  · exact True.intro

theorem supportBlankBody_eq (wires : List Sig) :
    Erasure.Exposure.supportBody
        (Region.ofItems (ItemSeq.nil : ItemSeq wires)) =
      Region.ofItems (supportBlankTail wires) := by
  unfold Erasure.Exposure.supportBody supportBlankTail
  simp only [Region.ofItems, Region.locals, Region.items]
  have appendEq : (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming wires (wires ++ [])) =
      (WireEquiv.appendNil wires).symm.toRenaming := by
    apply WireRenaming.ext
    intro signature wire
    exact (WireEquiv.appendNil_symm_apply wires wire).symm
  rw [appendEq, ItemSeq.renameWires_comp]
  have renameEq : WireRenaming.comp
      (WireEquiv.appendNil wires).symm.toRenaming
      (WireEquiv.appendNil wires).toRenaming = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    exact (WireEquiv.appendNil wires).left_inv wire
  simp only [ItemSeq.renameWires, ItemSeq.nil_append]
  rw [renameEq]
  exact congrArg (fun items => Region.mk [] items)
    (ItemSeq.renameWires_id _).symm

theorem supportBlankInstantiationScope
    (application : Vars common wires) :
    let substitution := EqualityNormalization.formalSubstitution application
    let pins := EqualityNormalization.allPins wires substitution
    ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))
          (supportBlankMaterial_canonical wires)) application)
      (((Erasure.Exposure.supportBody
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))).renameWires
            substitution).conjoin
        (Region.ofItems (pins.append pins))) := by
  exact EqualityNormalization.supportInstantiationPinnedScope
    (Region.ofItems (ItemSeq.nil : ItemSeq wires))
    (supportBlankMaterial_canonical wires) application

def endsFormalPrefixSource
    (frame : Transform.Frame [] common sourceWires targetWires)
    (hostItems : ItemSeq common) (application : Vars common []) :
    ItemSeq sourceWires :=
  (hostItems.renameWires frame.sourceKeep).append
    (.cons (.atom frame.selected
      (application.map fun wire => frame.sourceKeep wire)) .nil)

def endsFormalPrefixResult
    (hostItems : ItemSeq common) (application : Vars common []) :
    Region common :=
  match hostItems with
  | .nil =>
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application).conjoin (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (endsFormalPrefixResult tail application)

theorem endsFormalPrefixResult_renameWires
    (hostItems : ItemSeq sourceWires) (application : Vars sourceWires [])
    (rename : WireRenaming sourceWires targetWires) :
    (endsFormalPrefixResult hostItems application).renameWires rename =
      endsFormalPrefixResult (hostItems.renameWires rename)
        (application.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold endsFormalPrefixResult
      rw [Region.renameWires_conjoin,
        EqualityNormalization.instantiate_renameWires]
      rfl
  | cons item tail =>
      simp only [endsFormalPrefixResult, ItemSeq.renameWires]
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        endsFormalPrefixResult_renameWires tail application rename]

def endsFormalPrefixEvidence
    (frame : Transform.Frame [] common sourceWires targetWires)
    (hostItems : ItemSeq common) (application : Vars common []) :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult blankPattern
      frame.sourceKeep frame.selected
      (endsFormalPrefixSource frame hostItems application)
      (endsFormalPrefixResult hostItems application) := by
  cases hostItems with
  | nil =>
      exact VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          application)
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
  | cons item tail =>
      simp only [endsFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, endsFormalPrefixResult]
      exact VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (retainedItemResult blankPattern frame item)
        (endsFormalPrefixEvidence frame tail application)
termination_by sizeOf hostItems

def endsFormalPrefixRecordingSites
    (frame : Transform.Frame [] common sourceWires targetWires)
    (hostItems : ItemSeq common) (application : Vars common patternArguments) :
    ItemsSites
      (recordingOperation (Content.Ends.operation []) patternArguments)
      PUnit.unit (endsFormalPrefixEvidence frame hostItems .nil) :=
  match hostItems with
  | .nil =>
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            blankPattern frame.sourceKeep frame.selected .nil
              (Region.blank common) :=
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom (pattern := blankPattern) (frame := frame)
          .nil ⟨PUnit.unit, application⟩)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites blankPattern
          (recordingOperation (Content.Ends.operation []) patternArguments)
          frame PUnit.unit item)
        (endsFormalPrefixRecordingSites frame tail application)
termination_by sizeOf hostItems

theorem endsFormalPrefixArgumentItemsEdit_source
    (recordedFrame : Transform.Frame [] common
      recordedSourceWires recordedTargetWires)
    (targetFrame : Transform.Frame arguments common sourceWires targetWires)
    (hostItems : ItemSeq common) (application : Vars common patternArguments)
    (current : Vars patternArguments arguments) :
    (argumentItemsEdit
      (endsFormalPrefixRecordingSites recordedFrame hostItems application)
      current (normalizationOperation arguments) targetFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1 =
        (hostItems.renameWires targetFrame.sourceKeep).append
          (.cons (.atom targetFrame.selected
            (current.map fun wire => targetFrame.sourceKeep
              (EqualityNormalization.formalSubstitution application wire)))
            .nil) := by
  cases hostItems with
  | nil =>
      simp only [endsFormalPrefixRecordingSites, argumentItemsEdit,
        argumentItemEdit, ItemSeq.renameWires, ItemSeq.append, Vars.map_map]
  | cons item tail =>
      simp only [endsFormalPrefixRecordingSites, argumentItemsEdit,
        ItemSeq.renameWires, ItemSeq.append]
      congr 1
      · exact retainedItemSites_argumentItemEdit_source blankPattern
          (Content.Ends.operation []) recordedFrame PUnit.unit targetFrame item
          current
      · exact endsFormalPrefixArgumentItemsEdit_source recordedFrame
          targetFrame tail application current
termination_by sizeOf hostItems

theorem endsFormalPrefixSource_eq_argumentItemsEdit
    (frame : Transform.Frame [] common sourceWires targetWires)
    (hostItems : ItemSeq common) (application : Vars common patternArguments)
    (values : Vars patternArguments [])
    (rename : WireRenaming patternArguments common)
    (_applicationEq : application =
      (EqualityNormalization.formalPorts patternArguments).map
        fun wire => rename wire) :
    endsFormalPrefixSource frame hostItems .nil =
      (argumentItemsEdit
        (endsFormalPrefixRecordingSites frame hostItems application)
        values (normalizationOperation []) frame PUnit.unit
        (fun _ _ _ => PUnit.unit)).1 := by
  cases values
  rw [endsFormalPrefixArgumentItemsEdit_source]
  rfl

noncomputable def endsFormalPrefixResultIso
    (hostItems : ItemSeq common) (application : Vars common []) :
    RegionIso (WireEquiv.refl common)
      (endsFormalPrefixResult hostItems application)
      ((Region.ofItems hostItems).conjoin
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          blankPattern application)) :=
  match hostItems with
  | .nil => by
      let inner := VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application
      exact (RegionIso.conjoinBlank inner).trans
        (RegionIso.blankConjoin inner).symm
  | .cons item tail => by
      let inner := VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (endsFormalPrefixResultIso tail application)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) inner).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl inner)
      exact children.trans (associated.trans prefixIso)
termination_by sizeOf hostItems

structure EndsSpawnScope
    {arguments common sourceWires targetWires : List Sig}
    (frame : Transform.Frame arguments common sourceWires targetWires)
    (source : Region sourceWires) (target : Region targetWires) : Prop where
  canonical : target.Canonical → source.Canonical
  retained : ∀ {signature} (wire : Var common signature),
    SupportParallelIncidenceScope
      (target.incidencePaths (frame.targetKeep wire).index.val)
      (source.incidencePaths (frame.sourceKeep wire).index.val)

theorem EndsSpawnScope.iso
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (scope : EndsSpawnScope frame sourceAfter targetBefore) :
    EndsSpawnScope frame sourceBefore targetAfter := by
  constructor
  · intro targetCanonical
    exact sourceIso.canonical_iff.mpr
      (scope.canonical (targetIso.canonical_iff.mpr targetCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.iso targetIso.symm sourceIso.symm
      (frame.targetKeep wire) (frame.sourceKeep wire)
      (scope.retained wire)

theorem EndsSpawnScope.conjoin
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : EndsSpawnScope frame sourceFirst targetFirst)
    (second : EndsSpawnScope frame sourceSecond targetSecond) :
    EndsSpawnScope frame (sourceFirst.conjoin sourceSecond)
      (targetFirst.conjoin targetSecond) := by
  constructor
  · intro targetCanonical
    have pieces := (Region.Canonical.conjoin_iff _ _).mp targetCanonical
    exact (Region.Canonical.conjoin_iff _ _).mpr
      ⟨first.canonical pieces.1, second.canonical pieces.2⟩
  · intro signature wire
    exact SupportParallelIncidenceScope.conjoin
      (frame.targetKeep wire) (frame.sourceKeep wire)
      (first.retained wire) (second.retained wire)

theorem EndsSpawnScope.cut
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (scope : EndsSpawnScope frame source target) :
    EndsSpawnScope frame (Region.singleton (.cut source))
      (Region.singleton (.cut target)) := by
  constructor
  · intro targetCanonical
    exact (Region.singleton_cut_canonical_iff source).mpr
      (scope.canonical
        ((Region.singleton_cut_canonical_iff target).mp targetCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.cut
      (frame.targetKeep wire) (frame.sourceKeep wire)
      (scope.retained wire)

theorem EndsSpawnScope.adjoin
    {frame : Transform.Frame arguments common sourceWires targetWires}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (scope : EndsSpawnScope (frame.append locals) source target) :
    EndsSpawnScope frame (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil target) := by
  constructor
  · intro targetCanonical
    have targetMaterialCanonical : target.Canonical :=
      Region.Canonical.material_of_adjoinAt locals .nil target targetCanonical
    have sourceMaterialCanonical := scope.canonical targetMaterialCanonical
    apply Region.Canonical.adjoinAt_of_material_roots locals .nil source
      True.intro sourceMaterialCanonical
    intro localIndex
    let localWire : Var (common ++ locals) (locals.get localIndex) :=
      Var.appendRight common (Var.ofIndex localIndex)
    have targetRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil target
        targetCanonical localIndex
    have targetRoot' : RegionPath.RootedTwo
        (target.incidencePaths
          ((frame.append locals).targetKeep localWire).index.val) := by
      simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
        using targetRoot
    have sourceRoot := (scope.retained localWire).rooted targetRoot'
    simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
      using sourceRoot
  · intro signature wire
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      ((frame.targetKeep wire).appendLeft locals)
    have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      ((frame.sourceKeep wire).appendLeft locals)
    rw [show (frame.targetKeep wire).index.val =
        ((frame.targetKeep wire).appendLeft locals).index.val by simp,
      targetPaths,
      show (frame.sourceKeep wire).index.val =
        ((frame.sourceKeep wire).appendLeft locals).index.val by simp,
      sourcePaths]
    simpa [Transform.Frame.append, WireRenaming.appendRight] using
      scope.retained (wire.appendLeft locals)

mutual
  theorem endsRegionEditSpawnScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Ends.operation []).Data frame}
      {source : Region sourceWires}
      (invariant : Transform.RetainedIndexInvariant frame)
      (edit : Transform.RegionEdit (Content.Ends.operation [])
        frame data source) :
      EndsSpawnScope frame source edit.run := by
    cases edit with
    | mk itemsEdit =>
        exact EndsSpawnScope.iso
          (RegionIso.adjoinAtOfItems _ _).symm (RegionIso.refl _)
          (EndsSpawnScope.adjoin _
            (endsItemsEditSpawnScope (invariant.append _) itemsEdit))
  termination_by sizeOf source

  theorem endsItemsEditSpawnScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Ends.operation []).Data frame}
      {source : ItemSeq sourceWires}
      (invariant : Transform.RetainedIndexInvariant frame)
      (edit : Transform.ItemsEdit (Content.Ends.operation [])
        frame data source) :
      EndsSpawnScope frame (Region.ofItems source) edit.run := by
    cases edit with
    | nil =>
        constructor
        · intro canonical
          simpa [Transform.ItemsEdit.run] using canonical
        · intro signature wire
          simp only [Transform.ItemsEdit.run, Region.incidencePaths_ofItems,
            ItemSeq.incidencePaths]
          exact SupportParallelIncidenceScope.refl []
    | cons headEdit tailEdit =>
        rw [← Region.singleton_conjoin_ofItems]
        exact EndsSpawnScope.conjoin
          (endsItemEditSpawnScope invariant headEdit)
          (endsItemsEditSpawnScope invariant tailEdit)
  termination_by sizeOf source

  theorem endsItemEditSpawnScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Ends.operation []).Data frame}
      {source : Item sourceWires}
      (invariant : Transform.RetainedIndexInvariant frame)
      (edit : Transform.ItemEdit (Content.Ends.operation [])
        frame data source) :
      EndsSpawnScope frame (Region.singleton source) edit.run := by
    cases edit with
    | atom head ports =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro signature wire
          have headEq := invariant.reflects head wire
          have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
            frame.sourceKeep frame.targetKeep invariant.reflects wire
          simp only [Transform.ItemEdit.run, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft,
            Vars.countIndex_map_appendLeft_nil]
          simp only [headEq, portsEq]
          exact SupportParallelIncidenceScope.refl _
    | selectedAtom ports siteData =>
        cases ports
        cases siteData
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro signature wire
          have fresh := invariant.selectedFresh wire
          simp only [Transform.ItemEdit.run, Content.Ends.operation,
            Region.blank, Region.singleton, Region.ofItems,
            Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
            ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
            Var.index_appendLeft]
          rw [if_neg fresh]
          exact SupportParallelIncidenceScope.refl []
    | selectedPin ports selected =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro signature wire
          have fresh := invariant.selectedFresh wire
          simp only [Transform.ItemEdit.run, Content.Ends.operation,
            Region.blank, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft, List.ofFn_succ,
            List.ofFn_zero, List.count_cons, List.count_nil]
          rw [selected]
          simp [fresh]
          exact SupportParallelIncidenceScope.refl []
    | identity signature arity ports =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro wireSignature wire
          have portsEq := Transform.countPorts_map_eq_of_reflection arity ports
            frame.sourceKeep frame.targetKeep invariant.reflects wire
          simp only [Transform.ItemEdit.run, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft]
          rw [← portsEq]
          exact SupportParallelIncidenceScope.refl _
    | cut childEdit =>
        exact EndsSpawnScope.cut
          (endsRegionEditSpawnScope invariant childEdit)
  termination_by sizeOf source
end

theorem endsTargetSourceScope
    {outer before after : List Sig}
    {items : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    (edit : Transform.ItemsEdit (Content.Ends.operation [])
      (Content.Ends.rootFrame outer before after []) PUnit.unit items)
    (selectedRooted : RegionPath.RootedTwo
      (items.incidencePaths (outer.length + before.length) 0)) :
    ScopePreservation
      (Region.adjoinAt (before ++ after) .nil edit.run)
      (.mk (before ++ .rel [] :: after) items : Region outer) := by
  let sourceLocals := before ++ .rel [] :: after
  let targetLocals := before ++ after
  let frame := Content.Ends.rootFrame outer before after []
  have invariant : Transform.RetainedIndexInvariant frame :=
    Transform.RetainedIndexInvariant.replace outer before after [] []
  have materialScope := endsItemsEditSpawnScope invariant edit
  have sourceCanonical :
      (Region.adjoinAt targetLocals .nil edit.run).Canonical →
        (.mk sourceLocals items : Region outer).Canonical := by
    intro targetCanonical
    have targetMaterialCanonical : edit.run.Canonical :=
      Region.Canonical.material_of_adjoinAt targetLocals .nil edit.run
        targetCanonical
    have sourceMaterialCanonical :=
      materialScope.canonical targetMaterialCanonical
    refine ⟨?_, (ItemSeq.ChildrenCanonical.renameWires_iff items _).mp
      sourceMaterialCanonical.2⟩
    intro localIndex
    by_cases beforeCase : localIndex.val < before.length
    · let beforeIndex : Fin before.length := ⟨localIndex.val, beforeCase⟩
      let targetIndex : Fin targetLocals.length :=
        ⟨beforeIndex.val, by simp only [targetLocals, List.length_append]; omega⟩
      let commonWire := Var.appendRight outer
        ((Var.ofIndex beforeIndex).appendLeft after)
      have targetRoot :=
        Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil edit.run
          targetCanonical targetIndex
      have sourceRoot := (materialScope.retained commonWire).rooted (by
        simpa [frame, targetIndex, commonWire, Content.Ends.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendRight, Var.index] using
          targetRoot)
      rw [Region.incidencePaths_ofItems] at sourceRoot
      simpa [sourceLocals, beforeIndex, frame, commonWire,
        Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep,
        Var.appendRight, Var.index] using sourceRoot
    · by_cases selectedCase : localIndex.val = before.length
      · simpa only [selectedCase] using selectedRooted
      · let afterIndex : Fin after.length :=
          ⟨localIndex.val - before.length - 1, by
            have bound := localIndex.isLt
            simp only [sourceLocals, List.length_append, List.length_cons] at bound
            omega⟩
        let targetIndex : Fin targetLocals.length :=
          ⟨before.length + afterIndex.val, by
            simp only [targetLocals, List.length_append]
            omega⟩
        let commonWire := Var.appendRight outer
          (Var.appendRight before (Var.ofIndex afterIndex))
        have targetRoot :=
          Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil edit.run
            targetCanonical targetIndex
        have sourceRoot := (materialScope.retained commonWire).rooted (by
          simpa [frame, targetIndex, commonWire, Content.Ends.rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight, Var.index] using
            targetRoot)
        rw [Region.incidencePaths_ofItems] at sourceRoot
        have sourceIndexEq :
            outer.length + (before.length + (afterIndex.val + 1)) =
              outer.length + localIndex.val := by
          have afterIndexVal : afterIndex.val =
              localIndex.val - before.length - 1 := rfl
          rw [afterIndexVal]
          omega
        simpa [sourceLocals, afterIndex, frame, commonWire,
          Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep,
          Var.appendRight, Var.index, sourceIndexEq] using sourceRoot
  have outerScope : ∀ {signature} (wire : Var outer signature),
      SupportParallelIncidenceScope
        ((Region.adjoinAt targetLocals .nil edit.run).incidencePaths
          wire.index.val)
        ((.mk sourceLocals items : Region outer).incidencePaths
          wire.index.val) := by
    intro signature wire
    let commonWire : Var (outer ++ (before ++ after)) signature :=
      wire.appendLeft (before ++ after)
    have material := materialScope.retained commonWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil edit.run
      (wire.appendLeft targetLocals)
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems items) (wire.appendLeft sourceLocals)
    have adjoined : SupportParallelIncidenceScope
        ((Region.adjoinAt targetLocals .nil edit.run).incidencePaths
          wire.index.val)
        ((Region.adjoinAt sourceLocals .nil
          (Region.ofItems items)).incidencePaths wire.index.val) := by
      have targetEq :
          (Region.adjoinAt targetLocals .nil edit.run).incidencePaths
              wire.index.val = edit.run.incidencePaths wire.index.val := by
        simpa [targetLocals] using targetPaths
      have sourceEq :
          (Region.adjoinAt sourceLocals .nil
              (Region.ofItems items)).incidencePaths wire.index.val =
            (Region.ofItems items).incidencePaths wire.index.val := by
        simpa [sourceLocals] using sourcePaths
      rw [targetEq, sourceEq]
      simpa [frame, commonWire, Content.Ends.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using material
    exact SupportParallelIncidenceScope.iso
      (RegionIso.refl _) (RegionIso.adjoinAtOfItems sourceLocals items)
      wire wire adjoined
  exact {
    canonical := sourceCanonical
    incidenceNonempty := fun wire => (outerScope wire).nonempty
    rootedTwo := fun wire => (outerScope wire).rooted
  }

def endsDataNaturality (arguments : List Sig) :
    DataNaturality (Content.Ends.operation arguments) where
  Coherent := fun _ _ _ _ _ _ => True
  append := by intros; trivial
  appendAssoc := by intros; trivial
  conjoinLeft := by intros; trivial
  conjoinRight := by intros; trivial
  appendNil := by intros; trivial
  site := by
    intros
    exact ⟨PUnit.unit, ⟨RegionIso.ofEq (by rfl)⟩⟩

theorem supportBlankSelectedTargetItem
    {wires itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {itemFrame : Transform.Frame wires itemCommon itemSourceWires
      itemTargetWires}
    {itemOperation : Transform.Operation wires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon wires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame [] itemCommon formalSourceWires
      formalTargetWires) :
    TargetItem
      (targetPattern := blankPattern)
      (targetOperation := Content.Ends.operation [])
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := Erasure.Exposure.supportPattern
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))
          (supportBlankMaterial_canonical wires))
        (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := Erasure.Exposure.supportPattern
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))
          (supportBlankMaterial_canonical wires))
        (frame := itemFrame) application siteData)
      (.nil : Vars wires []) formalFrame PUnit.unit
      (fun retained _formalSource formalResult _formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (Region.ofItems (ItemSeq.nil : ItemSeq wires))
                  (supportBlankMaterial_canonical wires)) application)
              staged ∧
            ScopePreservation
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (Region.ofItems (ItemSeq.nil : ItemSeq wires))
                  (supportBlankMaterial_canonical wires)) application)
              staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
              retained = [] ∧
              let authoritativeFrame : Transform.Frame wires itemCommon
                  itemSourceWires itemSourceWires := {
                sourceKeep := itemFrame.sourceKeep
                targetKeep := itemFrame.sourceKeep
                selected := itemFrame.selected
              }
              let direct := Region.singleton (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
              let authoritative := Region.adjoinAt retained .nil
                (Region.ofItems
                  (argumentItemsEdit formalSites
                    (EqualityNormalization.formalPorts wires)
                    (normalizationOperation wires)
                    (authoritativeFrame.append retained)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1)
              HostedStrict direct authoritative ∧
                HostedScope direct authoritative) := by
  unfold TargetItem
  let commonEquiv := WireEquiv.appendNil itemCommon
  let commonAppend := commonEquiv.symm.toRenaming
  let mappedApplication := application.map fun wire => commonAppend wire
  let substitution := EqualityNormalization.formalSubstitution mappedApplication
  let mappedPins := EqualityNormalization.allPins wires substitution
  let hostItems := (supportBlankTail wires).renameWires substitution |>.append
    (mappedPins.append mappedPins)
  let childFrame := formalFrame.append []
  let formalSource := endsFormalPrefixSource childFrame hostItems .nil
  let formalResult := endsFormalPrefixResult hostItems .nil
  let formalEvidence := endsFormalPrefixEvidence childFrame hostItems .nil
  let formalSites := endsFormalPrefixRecordingSites childFrame hostItems
    mappedApplication
  refine ⟨[], formalSource, formalResult, formalEvidence, formalSites, ?_, ?_⟩
  · apply endsFormalPrefixSource_eq_argumentItemsEdit childFrame hostItems
      mappedApplication .nil substitution
    exact (EqualityNormalization.formalPorts_map_substitution
      mappedApplication).symm
  · let rawSubstitution := EqualityNormalization.formalSubstitution application
    let rawSupportItems :=
      (supportBlankTail wires).renameWires rawSubstitution
    let rawPins := EqualityNormalization.allPins wires rawSubstitution
    let rawHostItems := rawSupportItems.append (rawPins.append rawPins)
    let staged := endsFormalPrefixResult rawHostItems .nil
    refine ⟨staged, ?_, ?_, ?_, rfl, ?_⟩
    · let material := Region.ofItems (ItemSeq.nil : ItemSeq wires)
      let materialCanonical := supportBlankMaterial_canonical wires
      let supported := Erasure.Exposure.supportBody material
      let supportedCanonical := Erasure.Exposure.supportBody_canonical
        material materialCanonical
      have supportedPinsNil : Erasure.Exposure.supportPins supported wires
          (Erasure.Exposure.identityBoundary wires) = .nil := by
        apply EqualityNormalization.supportPins_eq_nil
        intro position
        exact Erasure.Exposure.supportBody_incidence_nonempty material
          ((Erasure.Exposure.identityBoundary wires).get position)
      have supportedFixed : Erasure.Exposure.supportBody supported = supported :=
        EqualityNormalization.supportBody_eq_of_supportPins_nil supported
          supportedPinsNil
      have patternEq : Erasure.Exposure.supportPattern supported
            supportedCanonical =
          Erasure.Exposure.supportPattern material materialCanonical := by
        apply EqualityNormalization.OpenDiagram.eq_of_data
        · rfl
        · rfl
        · exact heq_of_eq supportedFixed
      have sourceToSupported : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (supported.renameWires rawSubstitution) := by
        rw [← patternEq]
        exact supportInstantiationHosted supported supportedCanonical application
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems rawSupportItems := by
        change (Erasure.Exposure.supportBody
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))).renameWires
            rawSubstitution = _
        rw [supportBlankBody_eq wires, Region.ofItems_renameWires]
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          blankPattern (.nil : Vars itemCommon [])
      let positionalToBlank := blankPatternInstantiationIso
        (.nil : Vars itemCommon [])
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (positional.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.blankConjoin supportPins).symm.trans
            (RegionIso.conjoinCongr positionalToBlank.symm
              (RegionIso.refl supportPins)))
      have sourceToPositionalPins : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (positional.conjoin supportPins) :=
        HostedStrict.iso (RegionIso.refl _) supportedPresentation
          sourceToSupported
      let source :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern material materialCanonical)
          application
      let pinned := HostedStrict.conjoin source (Region.blank itemCommon)
        (positional.conjoin supportPins) allPins sourceToPositionalPins
        (HostedStrict.allPinsTwice wires rawSubstitution)
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (endsFormalPrefixResultIso rawHostItems .nil).symm))
      exact HostedStrict.iso (RegionIso.conjoinBlank source).symm
        resultPresentation pinned
    · let material := Region.ofItems (ItemSeq.nil : ItemSeq wires)
      let supported := Erasure.Exposure.supportBody material
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          blankPattern (.nil : Vars itemCommon [])
      have sourceToSupportedPins := supportBlankInstantiationScope application
      have supportedTargetEq : supported.renameWires rawSubstitution =
          supportPins := by
        change (Erasure.Exposure.supportBody
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))).renameWires
            rawSubstitution = _
        rw [supportBlankBody_eq wires, Region.ofItems_renameWires]
      let positionalToBlank := blankPatternInstantiationIso
        (.nil : Vars itemCommon [])
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (positional.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.blankConjoin supportPins).symm.trans
            (RegionIso.conjoinCongr positionalToBlank.symm
              (RegionIso.refl supportPins)))
      have supportedToPositional : ScopePreservation
          ((supported.renameWires rawSubstitution).conjoin allPins)
          ((positional.conjoin supportPins).conjoin allPins) :=
        ScopePreservation.ofIso
          (RegionIso.conjoinCongr supportedPresentation
            (RegionIso.refl allPins))
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (endsFormalPrefixResultIso rawHostItems .nil).symm))
      exact sourceToSupportedPins.trans
        (supportedToPositional.trans
          (ScopePreservation.ofIso resultPresentation))
    · have mappedResultEq : staged.renameWires commonAppend = formalResult := by
        rw [endsFormalPrefixResult_renameWires]
        have hostItemsEq : rawHostItems.renameWires commonAppend = hostItems := by
          have substitutionEq :
              WireRenaming.comp commonAppend rawSubstitution = substitution := by
            apply WireRenaming.ext
            intro signature wire
            exact (EqualityNormalization.formalSubstitution_map
              application commonAppend wire).symm
          have supportItemsEq : rawSupportItems.renameWires commonAppend =
              (supportBlankTail wires).renameWires substitution := by
            unfold rawSupportItems rawSubstitution
            rw [ItemSeq.renameWires_comp, substitutionEq]
          have pinsEq : rawPins.renameWires commonAppend = mappedPins := by
            unfold rawPins mappedPins rawSubstitution
            rw [EqualityNormalization.allPins_renameWires, substitutionEq]
          unfold rawHostItems hostItems
          simp only [ItemSeq.renameWires_append, supportItemsEq, pinsEq]
        rw [hostItemsEq]
        rfl
      let intoMapped : RegionIso commonEquiv.symm staged formalResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonAppend commonEquiv.symm (by intro signature wire; rfl)
        rw [Region.renameWires_id, mappedResultEq] at renamed
        exact renamed
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv
            (by intro signature wire; rfl)
      let chained := (intoMapped.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq : (commonEquiv.symm.trans commonEquiv).trans
          (WireEquiv.refl itemCommon) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      exact ⟨chained.castAmbient ambientEq⟩
    · dsimp only
      simp only [formalSites]
      let authoritativeFrame : Transform.Frame wires itemCommon
          itemSourceWires itemSourceWires := {
        sourceKeep := itemFrame.sourceKeep
        targetKeep := itemFrame.sourceKeep
        selected := itemFrame.selected
      }
      have editedEq :=
        endsFormalPrefixArgumentItemsEdit_source childFrame
          (authoritativeFrame.append []) hostItems mappedApplication
          (EqualityNormalization.formalPorts wires)
      change
        let direct := Region.singleton (.atom itemFrame.selected
          (application.map fun wire => itemFrame.sourceKeep wire))
        let authoritative := Region.adjoinAt [] .nil
          (Region.ofItems
            (argumentItemsEdit
              (endsFormalPrefixRecordingSites childFrame hostItems
                mappedApplication)
              (EqualityNormalization.formalPorts wires)
              (normalizationOperation wires)
              (authoritativeFrame.append []) PUnit.unit
              (fun _ _ _ => PUnit.unit)).1)
        HostedStrict direct authoritative ∧
          HostedScope direct authoritative
      rw [editedEq]
      let rawSubstitution :=
        EqualityNormalization.formalSubstitution application
      let targetSubstitution : WireRenaming wires itemSourceWires :=
        WireRenaming.comp itemFrame.sourceKeep rawSubstitution
      let direct := Region.singleton (.atom itemFrame.selected
        (application.map fun wire => itemFrame.sourceKeep wire))
      let supportPins := Region.ofItems
        ((supportBlankTail wires).renameWires targetSubstitution)
      let pins := EqualityNormalization.allPins wires targetSubstitution
      let allPins := Region.ofItems (pins.append pins)
      let material := Region.ofItems (ItemSeq.nil : ItemSeq wires)
      have supportStep : HostedStrict (Region.blank itemSourceWires)
          supportPins := by
        have base : HostedStrict (Region.blank wires)
            (Region.ofItems (supportBlankTail wires)) := by
          apply HostedStrict.specialize
            (HostedStrict.supportPins material
              (Erasure.Exposure.identityBoundary wires))
            (WireEquiv.appendNil wires).toRenaming
          · change (Region.blank (wires ++ [])).renameWires
                (WireEquiv.appendNil wires).toRenaming =
              Region.blank wires
            rfl
          · unfold material
            rw [Region.ofItems_renameWires]
            simp [supportBlankTail] <;> rfl
        apply HostedStrict.specialize base targetSubstitution
        · rfl
        · unfold supportPins
          exact Region.ofItems_renameWires
            (supportBlankTail wires) targetSubstitution
      have allPinsStep : HostedStrict (Region.blank itemSourceWires)
          allPins :=
        HostedStrict.allPinsTwice wires targetSubstitution
      let hostStep := HostedStrict.conjoin
        (Region.blank itemSourceWires) (Region.blank itemSourceWires)
        supportPins allPins supportStep allPinsStep
      let host := supportPins.conjoin allPins
      let hostFromBlank : HostedStrict (Region.blank itemSourceWires) host :=
        HostedStrict.iso (RegionIso.blankConjoin _).symm
          (RegionIso.refl host) hostStep
      let directHost := HostedStrict.conjoin direct
        (Region.blank itemSourceWires) direct host
        (HostedStrict.refl direct) hostFromBlank
      let directToHostDirect : HostedStrict direct (host.conjoin direct) :=
        HostedStrict.iso (RegionIso.conjoinBlank direct).symm
          (RegionIso.conjoinComm direct host) directHost
      let authoritativeSource :=
        (hostItems.renameWires
            (authoritativeFrame.append []).sourceKeep).append
          (.cons (.atom (authoritativeFrame.append []).selected
            ((EqualityNormalization.formalPorts wires).map fun wire =>
              (authoritativeFrame.append []).sourceKeep
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire))) .nil)
      let child := Region.ofItems authoritativeSource
      have childDownEq :
          child.renameWires (WireEquiv.appendNil itemSourceWires).toRenaming =
            host.conjoin direct := by
        let down := (WireEquiv.appendNil itemSourceWires).toRenaming
        let downFrame : WireRenaming (itemCommon ++ []) itemSourceWires :=
          WireRenaming.comp down
            (authoritativeFrame.append []).sourceKeep
        have downFrameCommonEq : ∀ {wireSignature}
            (wire : Var itemCommon wireSignature),
            downFrame (commonAppend wire) = itemFrame.sourceKeep wire := by
          intro wireSignature wire
          unfold downFrame down commonAppend authoritativeFrame
          rw [show commonEquiv.symm.toRenaming wire =
              wire.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon wire]
          simp [WireRenaming.comp, Transform.Frame.append,
            WireRenaming.appendRight, Var.appendMap_left,
            WireEquiv.appendNil_apply]
        have combinedSubstitutionEq :
            WireRenaming.comp downFrame substitution =
              targetSubstitution := by
          apply WireRenaming.ext
          intro wireSignature wire
          change downFrame
              (EqualityNormalization.formalSubstitution mappedApplication
                wire) =
            itemFrame.sourceKeep
              (EqualityNormalization.formalSubstitution application wire)
          rw [EqualityNormalization.formalSubstitution_map
            application commonAppend wire]
          exact downFrameCommonEq _
        have selectedPortsEq :
            (EqualityNormalization.formalPorts wires).map (fun wire =>
              downFrame
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire)) =
              application.map fun wire => itemFrame.sourceKeep wire := by
          calc
            _ = ((EqualityNormalization.formalPorts wires).map
                (fun wire =>
                  EqualityNormalization.formalSubstitution mappedApplication
                    wire)).map (fun wire => downFrame wire) := by
              rw [Vars.map_map]
            _ = mappedApplication.map (fun wire => downFrame wire) := by
              rw [EqualityNormalization.formalPorts_map_substitution]
            _ = application.map (fun wire => itemFrame.sourceKeep wire) := by
              unfold mappedApplication
              rw [Vars.map_map]
              apply Vars.map_congr
              intro wireSignature wire
              exact downFrameCommonEq wire
        have selectedHeadEq :
            down ((authoritativeFrame.append []).selected) =
              itemFrame.selected := by
          unfold down authoritativeFrame
          simp [Transform.Frame.append, WireEquiv.appendNil_apply]
        have hostItemsDownEq :
            hostItems.renameWires downFrame =
              ((supportBlankTail wires).renameWires
                  targetSubstitution).append
                (pins.append pins) := by
          unfold hostItems mappedPins pins
          simp only [ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp,
            EqualityNormalization.allPins_renameWires]
          rw [combinedSubstitutionEq]
        unfold host supportPins allPins direct
        unfold child authoritativeSource pins
        rw [Region.ofItems_renameWires]
        rw [show Region.singleton
              (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) =
            Region.ofItems
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
                .nil) by rfl]
        rw [Region.ofItems_conjoin]
        rw [Region.ofItems_conjoin]
        apply congrArg Region.ofItems
        simp only [ItemSeq.renameWires_append, ItemSeq.renameWires,
          Item.renameWires, ItemSeq.renameWires_comp, Vars.map_map]
        change
          (hostItems.renameWires downFrame).append
              (.cons (.atom
                (down ((authoritativeFrame.append []).selected))
                ((EqualityNormalization.formalPorts wires).map fun wire =>
                  downFrame
                    (EqualityNormalization.formalSubstitution
                      mappedApplication wire))) .nil) =
            (((supportBlankTail wires).renameWires
                targetSubstitution).append
              ((EqualityNormalization.allPins wires
                  targetSubstitution).append
                (EqualityNormalization.allPins wires
                  targetSubstitution))).append
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) .nil)
        rw [hostItemsDownEq, selectedHeadEq, selectedPortsEq]
      have supportPinsCanonical : supportPins.Canonical := by
        have baseCanonical :
            (Region.ofItems (supportBlankTail wires)).Canonical := by
          constructor
          · intro localIndex
            exact Fin.elim0 localIndex
          · unfold supportBlankTail
            exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
              ((ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
                (Erasure.Exposure.supportPins_childrenCanonical material
                  (Erasure.Exposure.identityBoundary wires)))
        simpa only [supportPins, Region.ofItems_renameWires] using
          (Region.Canonical.renameWires_iff
            (Region.ofItems (supportBlankTail wires))
            targetSubstitution).mpr baseCanonical
      have allPinsCanonical : allPins.Canonical := by
        constructor
        · intro localIndex
          exact Fin.elim0 localIndex
        · exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
            (EqualityNormalization.allPins_twice_childrenCanonical
              wires targetSubstitution)
      have hostCanonical : host.Canonical := by
        exact EqualityNormalization.canonical_conjoin supportPinsCanonical
          allPinsCanonical
      have directToHostDirectScope : HostedScope direct
          (host.conjoin direct) := by
        intro target rename
        let mappedApplication :=
          (application.map fun wire => itemFrame.sourceKeep wire).map
            (fun wire => rename wire)
        let mappedSubstitution : WireRenaming wires target :=
          EqualityNormalization.formalSubstitution mappedApplication
        have mappedSubstitutionEq : mappedSubstitution =
            WireRenaming.comp rename targetSubstitution := by
          apply WireRenaming.ext
          intro wireSignature wire
          unfold mappedSubstitution mappedApplication targetSubstitution
            rawSubstitution
          calc
            _ = rename
                (EqualityNormalization.formalSubstitution
                  (application.map fun wire => itemFrame.sourceKeep wire)
                  wire) :=
              EqualityNormalization.formalSubstitution_map
                (application.map fun wire => itemFrame.sourceKeep wire)
                rename wire
            _ = rename
                (itemFrame.sourceKeep
                  (EqualityNormalization.formalSubstitution application
                    wire)) := by
              rw [EqualityNormalization.formalSubstitution_map]
            _ = _ := rfl
        have directRenameEq : direct.renameWires rename =
            Region.singleton (.atom (rename itemFrame.selected)
              mappedApplication) := by
          unfold direct mappedApplication
          simp only [Region.singleton_renameWires, Item.renameWires,
            Vars.map_map]
        have hostRenameCanonical : (host.renameWires rename).Canonical :=
          (Region.Canonical.renameWires_iff host rename).mpr hostCanonical
        have scopeProof : ScopePreservation
            (direct.renameWires rename)
            ((host.renameWires rename).conjoin
              (direct.renameWires rename)) :=
          ScopePreservation.hostLeft
            (direct.renameWires rename) (host.renameWires rename)
            hostRenameCanonical (by
              intro wireSignature wire hostNonempty
              rw [directRenameEq]
              intro directEmpty
              let appendNil : WireRenaming target (target ++ []) :=
                ⟨fun selected => selected.appendLeft []⟩
              have mappedCountEq :
                  (mappedApplication.map fun selected =>
                    appendNil selected).countIndex wire.index.val =
                    mappedApplication.countIndex wire.index.val :=
                Vars.countIndex_map_of_sameIndex mappedApplication appendNil
                  (fun selected => Var.index_appendLeft selected [])
                  wire.index.val
              simp only [Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.renameWires,
                Item.renameWires, ItemSeq.incidencePaths,
                Item.incidencePaths, List.append_nil,
                Var.index_appendLeft] at directEmpty
              rw [mappedCountEq] at directEmpty
              have countZero : mappedApplication.countIndex
                  wire.index.val = 0 := by
                have totalZero :
                    (if (rename itemFrame.selected).index.val =
                        wire.index.val then 1 else 0) +
                      mappedApplication.countIndex wire.index.val = 0 := by
                  simpa only [List.replicate_eq_nil_iff] using directEmpty
                omega
              have noPreimage : ∀ {sourceSignature}
                  (sourceWire : Var wires sourceSignature),
                  ((WireRenaming.comp rename targetSubstitution)
                      sourceWire).index.val ≠ wire.index.val := by
                intro sourceSignature sourceWire
                rw [← mappedSubstitutionEq]
                exact EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                  mappedApplication wire countZero sourceWire
              have supportEmpty :
                  (supportPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                unfold supportPins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_comp, Region.incidencePaths_ofItems]
                exact ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
                  (supportBlankTail wires)
                  (WireRenaming.comp rename targetSubstitution)
                  wire.index.val 0 wire.index.isLt noPreimage
              have firstPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val 0 = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val 0
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have secondPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val
                      (EqualityNormalization.allPins wires
                        mappedSubstitution).length = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val
                  (EqualityNormalization.allPins wires
                    mappedSubstitution).length
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have allPinsEmpty :
                  (allPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                rw [mappedSubstitutionEq] at firstPinsEmpty secondPinsEmpty
                unfold allPins pins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_append,
                  EqualityNormalization.allPins_renameWires,
                  Region.incidencePaths_ofItems,
                  ItemSeq.incidencePaths_append, firstPinsEmpty]
                simpa only [List.nil_append, Nat.zero_add] using
                  secondPinsEmpty
              unfold host at hostNonempty
              rw [Region.renameWires_conjoin,
                Region.incidencePaths_conjoin, supportEmpty, allPinsEmpty]
                at hostNonempty
              exact hostNonempty (by simp))
        simpa only [Region.renameWires_conjoin] using scopeProof
      let targetPresentation :=
        (RegionIso.ofEq childDownEq).symm.trans
          (RegionIso.adjoinAtNil child)
      exact ⟨HostedStrict.iso (RegionIso.refl direct)
          targetPresentation directToHostDirect, by
        intro target rename
        exact (directToHostDirectScope rename).trans
          ((HostedScope.ofIso targetPresentation) rename)⟩

mutual
  /-- The Ends operation has unit site data at every selected blank-pattern
  application, so the region evidence supports exact sites. -/
  theorem endsRegionSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := endsItemsSites_nonempty
          (frame := frame.append _) childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem endsItemsSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := endsItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := endsItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem endsItemSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := blankPattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := blankPattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := blankPattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := endsRegionSites_nonempty childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

noncomputable def endsItemsSites
    {frame : Transform.Frame [] common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        blankPattern frame.sourceKeep frame.selected source result) :
    ItemsSites (Content.Ends.operation []) PUnit.unit evidence :=
  Classical.choice (endsItemsSites_nonempty evidence)

mutual
  /-- Ends removes precisely the selected blank applications; its recursive
  edit endpoint is therefore a presentation of the authoritative result. -/
  theorem endsRegionEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (regionEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites =>
        by
          have childIdentity :
              (frame.append locals).targetKeep = WireRenaming.id := by
            apply WireRenaming.ext
            intro signature wire
            change frame.targetKeep.appendRight locals wire = wire
            rw [targetKeepEq]
            exact WireRenaming.appendRight_id_apply locals wire
          obtain ⟨childIso⟩ :=
            endsItemsEndpointIso_nonempty childSites childIdentity
          exact ⟨RegionIso.adjoinAt locals .nil childIso⟩
  termination_by sizeOf source

  theorem endsItemsEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (itemsEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | .nil _ => ⟨RegionIso.refl _⟩
    | .cons itemSites tailSites => by
          obtain ⟨itemIso⟩ :=
            endsItemEndpointIso_nonempty itemSites targetKeepEq
          obtain ⟨tailIso⟩ :=
            endsItemsEndpointIso_nonempty tailSites targetKeepEq
          exact ⟨RegionIso.conjoinCongr itemIso tailIso⟩
  termination_by sizeOf source

  theorem endsItemEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (itemEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | .atom head ports => by
        have portsEq :
            ports.map (fun wire => frame.targetKeep wire) = ports := by
          rw [targetKeepEq]
          exact Diagram.vars_map_id ports
        have headEq : frame.targetKeep head = head := by
          rw [targetKeepEq]
          rfl
        exact ⟨RegionIso.ofEq (by
          simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
            headEq, portsEq])⟩
    | .selectedAtom application siteData => by
        exact ⟨(blankPatternInstantiationIso application).symm⟩
    | .identity signature arity ports => by
        have portsEq :
            (fun position => frame.targetKeep (ports position)) = ports := by
          funext position
          rw [targetKeepEq]
          rfl
        exact ⟨RegionIso.ofEq (by
          simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
            portsEq])⟩
    | .cut childSites => by
        obtain ⟨childIso⟩ :=
          endsRegionEndpointIso_nonempty childSites targetKeepEq
        exact ⟨RegionIso.singletonCutCongr childIso⟩
  termination_by sizeOf source
end

/-- Derive every authoritative blank-pattern site through one Ends spawn at
the binder home. Sites, the deterministic edit, and its presentation of the
authoritative result are all derived internally from the evidence. -/
theorem itemsEnds
    {outer before after : List Sig}
    {source : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    {result : Region (outer ++ (before ++ after))}
    {instantiated : Region outer}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        blankPattern
        (Content.Ends.rootFrame outer before after []).sourceKeep
        (Content.Ends.rootFrame outer before after []).selected source result)
    (request : Telescope.Request instantiated
      (.mk (before ++ .rel [] :: after) source))
    (basePreparation : request.Preparation
      (Region.adjoinAt (before ++ after) .nil result)) :
    request.Result := by
  let frame := Content.Ends.rootFrame outer before after []
  let sites := endsItemsSites evidence
  let output := itemsEdit (operation := Content.Ends.operation []) PUnit.unit
    evidence sites
  have targetKeepEq : frame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun wire => frame.targetKeep wire = WireRenaming.id wire)
    · intro inheritedSignature inherited
      simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          frame.targetKeep (Var.appendRight outer localWire) =
            WireRenaming.id (Var.appendRight outer localWire))
      · intro beforeSignature beforeWire
        simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp only [frame, Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendMap_right]
        apply Var.eq_of_index_eq
        apply Fin.ext
        simp [Var.index_appendRight, Var.appendRight]
  obtain ⟨endpointIso⟩ :=
    endsItemsEndpointIso_nonempty sites targetKeepEq
  let description : Content.Ends.Delete.Description outer := {
    arguments := []
    before := before
    after := after
    items := source
    itemsEdit := output.edit
  }
  let instantiated := Region.adjoinAt (before ++ after) .nil result
  have rawPreparedEq :
      Region.adjoinAt (before ++ after) .nil output.endpoint =
        description.target := by
    change Region.adjoinAt (before ++ after) .nil output.endpoint =
      Region.adjoinAt (before ++ after) .nil output.edit.run
    rw [output.run_eq]
  let rawPreparedIso : RegionIso (WireEquiv.refl outer)
      instantiated description.target :=
    (RegionIso.adjoinAt (before ++ after) .nil endpointIso.symm).trans
      (RegionIso.ofEq rawPreparedEq)
  let preparation : request.Preparation description.target :=
    basePreparation.rawIso rawPreparedIso
  have pendingEq :
      (.mk (before ++ .rel [] :: after) source : Region outer) =
        description.source := by
    rfl
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical := by
    rw [← pendingEq]
    exact request.pendingCanonical
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    intro signature wire
    rw [← pendingEq]
    exact request.pendingExternalTwoEnded wire
  let branch : request.Branch preparation.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := Content.Ends.Local
    inject := fun step => Step.ends step
    preparedCanonical := preparation.preparedCanonical
    preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
    rawPreparedCanonical := preparation.rawPreparedCanonical
    rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := preparation.preparedIso
    pendingIso := RegionIso.ofEq pendingEq
    localStep := .spawn (.mk description)
    preparation := preparation.telescope
  }
  exact branch.derive

end Structural.Blank

namespace Structural

/-- The empty item-sequence constructor is derivable by Ends. -/
theorem supportBlankDerives
    {wires : List Sig} :
    SupportDerives (Region.ofItems (ItemSeq.nil : ItemSeq wires)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence request
  have patternEq :
      Erasure.Exposure.supportPattern
          (Region.ofItems (ItemSeq.nil : ItemSeq wires)) materialCanonical =
        Erasure.Exposure.supportPattern
          (Region.ofItems (ItemSeq.nil : ItemSeq wires))
          (Structural.Blank.supportBlankMaterial_canonical wires) := by
    apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
  rw [patternEq] at evidence
  let sites := normalizationSites
    (frame := normalizationFrame structuralOuter structuralBefore
      structuralAfter wires) evidence
  let targetFrame := Content.Ends.rootFrame structuralOuter structuralBefore
    structuralAfter []
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      formalCoherence, staged, hosted, stagedScope, ⟨stagedPresentation⟩,
      _endpointPresentation, sourceCleanup, retainedEq⟩ :=
    accumulateHostedTargetWith
      (outer := structuralOuter) (before := structuralBefore)
      (after := structuralAfter) (targetInserted := []) evidence sites
      (.nil : Vars wires []) PUnit.unit
      (EqualityNormalization.formalPorts wires)
      ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun before after => HostedStrict before after ∧
        HostedScope before after)
      (fun region => ⟨HostedStrict.refl region,
        fun rename => ScopePreservation.refl _⟩)
      (fun locals before after transformation =>
        ⟨HostedStrict.adjoinAt locals before after transformation.1,
          HostedScope.adjoinAt locals before after transformation.2⟩)
      (fun first second =>
        ⟨HostedStrict.conjoin _ _ _ _ first.1 second.1, by
          intro target rename
          simpa only [Region.renameWires_conjoin] using
            ScopePreservation.conjoin (first.2 rename) (second.2 rename)⟩)
      (fun transformation =>
        ⟨HostedStrict.cut _ _ transformation.1, by
          intro target rename
          simpa only [Region.singleton_renameWires, Item.renameWires] using
            ScopePreservation.cut (transformation.2 rename)⟩)
      (fun sourceIso targetIso transformation =>
        ⟨HostedStrict.iso sourceIso targetIso transformation.1, by
          intro target rename
          exact ((HostedScope.ofIso sourceIso) rename).trans
            ((transformation.2 rename).trans
              ((HostedScope.ofIso targetIso) rename))⟩)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (Structural.Blank.endsDataNaturality [])
      (fun retained => retained = []) rfl
      (fun first second firstEq secondEq => by
        simp only [firstEq, secondEq, List.nil_append])
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame _ => by
        obtain ⟨selectedRetained, selectedSource, selectedResult,
            selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
            selectedHosted, selectedScope, selectedPresentation,
            selectedRetainedEq, selectedCleanup⟩ :=
          Structural.Blank.supportBlankSelectedTargetItem application siteData
            selectedFrame
        exact ⟨selectedRetained, selectedSource, selectedResult,
          selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
          selectedHosted, selectedScope, selectedPresentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects,
          selectedCleanup, selectedRetainedEq⟩)
  subst retained
  let common := structuralOuter ++ (structuralBefore ++ structuralAfter)
  let positionalSourceWires := structuralOuter ++
    (structuralBefore ++ .rel [] :: structuralAfter)
  let authoritativeSourceWires := structuralOuter ++
    (structuralBefore ++ .rel wires :: structuralAfter)
  let commonRename : WireRenaming (common ++ []) common :=
    (WireEquiv.appendNil common).toRenaming
  let positionalSourceRename : WireRenaming
      (positionalSourceWires ++ []) positionalSourceWires :=
    (WireEquiv.appendNil positionalSourceWires).toRenaming
  let authoritativeSourceRename : WireRenaming
      (authoritativeSourceWires ++ []) authoritativeSourceWires :=
    (WireEquiv.appendNil authoritativeSourceWires).toRenaming
  let authoritativeFrame : Transform.Frame wires common
      authoritativeSourceWires authoritativeSourceWires :=
    Transform.Frame.replace structuralOuter structuralBefore structuralAfter
      [.rel wires] wires
  have sourceKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
        targetFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
          positionalSourceRename
            ((targetFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => positionalSourceRename
          ((targetFrame.append []).sourceKeep value)) liftEq.symm
      _ = positionalSourceRename
          ((targetFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.sourceKeep baseWire := by
        simpa only [positionalSourceRename] using
          WireEquiv.appendNil_apply positionalSourceWires
            (targetFrame.sourceKeep baseWire)
      _ = targetFrame.sourceKeep (commonRename wire) := rfl
  have targetKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      commonRename ((targetFrame.append []).targetKeep wire) =
        targetFrame.targetKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      commonRename ((targetFrame.append []).targetKeep wire) =
          commonRename ((targetFrame.append []).targetKeep
            (baseWire.appendLeft [])) :=
        congrArg (fun value => commonRename
          ((targetFrame.append []).targetKeep value)) liftEq.symm
      _ = commonRename ((targetFrame.targetKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.targetKeep baseWire := by
        simpa only [commonRename] using WireEquiv.appendNil_apply common
          (targetFrame.targetKeep baseWire)
      _ = targetFrame.targetKeep (commonRename wire) := rfl
  have selectedCommutes :
      positionalSourceRename (targetFrame.append []).selected =
        targetFrame.selected := by
    simpa only [positionalSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply positionalSourceWires
        targetFrame.selected
  have argumentKeepCommutes : ∀ {signature}
      (wire : Var (common ++ []) signature),
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
        authoritativeFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
          authoritativeSourceRename
            ((authoritativeFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep value)) liftEq.symm
      _ = authoritativeSourceRename
          ((authoritativeFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = authoritativeFrame.sourceKeep baseWire := by
        simpa only [authoritativeSourceRename] using
          WireEquiv.appendNil_apply authoritativeSourceWires
            (authoritativeFrame.sourceKeep baseWire)
      _ = authoritativeFrame.sourceKeep (commonRename wire) := rfl
  have argumentSelectedCommutes :
      authoritativeSourceRename (authoritativeFrame.append []).selected =
        authoritativeFrame.selected := by
    simpa only [authoritativeSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply authoritativeSourceWires
        authoritativeFrame.selected
  obtain ⟨flatFormalSource, flatFormalResult, flatFormalEvidence,
      flatFormalSites, flatSourceEq, flatPositionalEq, flatAuthoritativeEq,
      ⟨flatResultIso⟩, _flatEndpointIso⟩ :=
    targetItemsReindex
      (baseOperation := Content.Ends.operation [])
      (external := wires) (mappedFrame := targetFrame)
      (mappedData := PUnit.unit) formalEvidence formalSites
      (.nil : Vars wires [])
      (EqualityNormalization.formalPorts wires)
      (authoritativeFrame.append []) authoritativeFrame
      commonRename positionalSourceRename commonRename
      authoritativeSourceRename sourceKeepCommutes targetKeepCommutes
      selectedCommutes argumentKeepCommutes argumentSelectedCommutes
      (Structural.Blank.endsDataNaturality []) True.intro
  let oldLocals := structuralBefore ++ structuralAfter
  let pendingLocals := structuralBefore ++ .rel wires :: structuralAfter
  let pending : Region structuralOuter := .mk pendingLocals items
  let authoritativeItems :=
    (argumentItemsEdit flatFormalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) authoritativeFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1
  let authoritativePending := argumentNormalizedRegionAt
    (outer := structuralOuter) (localBefore := structuralBefore)
    (localAfter := structuralAfter) flatFormalSites
    (EqualityNormalization.formalPorts wires)
  let rawAuthoritativeItems :=
    (argumentItemsEdit formalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) (authoritativeFrame.append [])
      PUnit.unit (fun _ _ _ => PUnit.unit)).1
  let rawAuthoritative := Region.ofItems rawAuthoritativeItems
  let flatAuthoritative := Region.ofItems authoritativeItems
  have renamedAuthoritativeEq :
      rawAuthoritative.renameWires authoritativeSourceRename =
        flatAuthoritative := by
    simpa only [rawAuthoritative, flatAuthoritative, authoritativeItems,
      rawAuthoritativeItems, Region.ofItems_renameWires] using
        congrArg Region.ofItems flatAuthoritativeEq
  let cleanupPresentation : RegionIso
      (WireEquiv.refl authoritativeSourceWires)
      (Region.adjoinAt [] .nil rawAuthoritative)
      flatAuthoritative :=
    (RegionIso.adjoinAtNil rawAuthoritative).symm.trans
      (RegionIso.ofEq renamedAuthoritativeEq)
  have sourceCleanupFlat :
      HostedStrict (Region.ofItems items) flatAuthoritative ∧
        HostedScope (Region.ofItems items) flatAuthoritative := by
    refine ⟨HostedStrict.iso (RegionIso.refl _) cleanupPresentation
        sourceCleanup.1, ?_⟩
    intro target rename
    exact (sourceCleanup.2 rename).trans
      ((HostedScope.ofIso cleanupPresentation) rename)
  have cleanupHosted : HostedStrict pending authoritativePending := by
    have lifted := HostedStrict.adjoinAt pendingLocals
      (Region.ofItems items) flatAuthoritative sourceCleanupFlat.1
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems pendingLocals items).symm
      (by
        simpa only [authoritativePending, argumentNormalizedRegionAt,
          authoritativeItems] using
            RegionIso.adjoinAtOfItems pendingLocals authoritativeItems)
      lifted
  have cleanupHostedScope : HostedScope pending authoritativePending := by
    have lifted : HostedScope
        (Region.adjoinAt pendingLocals .nil (Region.ofItems items))
        (Region.adjoinAt pendingLocals .nil flatAuthoritative) := by
      intro target rename
      exact HostedScope.adjoinAt pendingLocals
        (Region.ofItems items) flatAuthoritative sourceCleanupFlat.2 rename
    intro target rename
    exact ((HostedScope.ofIso
        (RegionIso.adjoinAtOfItems pendingLocals items).symm) rename).trans
      ((lifted rename).trans
        ((HostedScope.ofIso (by
          simpa only [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems] using
              RegionIso.adjoinAtOfItems pendingLocals authoritativeItems))
          rename))
  have cleanupScope : ScopePreservation pending authoritativePending := by
    simpa only [Region.renameWires_id] using
      cleanupHostedScope WireRenaming.id
  have pendingCanonical :
      (request.occurrence.context.fill pending).Canonical := by
    simpa only [pending, pendingLocals] using request.pendingCanonical
  have pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill pending) := by
    intro signature wire
    simpa only [pending, pendingLocals] using
      request.pendingExternalTwoEnded wire
  have authoritativeValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context pending
    authoritativePending pendingCanonical pendingExternalTwoEnded cleanupScope
  have cleanupTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending pending authoritativeValidity.1
      authoritativeValidity.2 pendingCanonical pendingExternalTwoEnded :=
    telescopeOfHostedExact cleanupHosted.symm request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativeValidity.1 authoritativeValidity.2 pendingCanonical
      pendingExternalTwoEnded request.continuation.1
  have authoritativeContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending request.endpoint authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    telescopeTrans cleanupTelescope (by
      simpa only [pending, pendingLocals] using request.continuation)
  let positionalValues := (.nil : Vars wires [])
  have flatFormalCoherence : flatFormalSource =
      (argumentItemsEdit flatFormalSites positionalValues
        (normalizationOperation []) targetFrame PUnit.unit
        (fun _ _ _ => PUnit.unit)).1 := by
    have mappedCoherence : formalSource.renameWires positionalSourceRename =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation []) (targetFrame.append []) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1.renameWires
            positionalSourceRename :=
      congrArg (fun source => source.renameWires positionalSourceRename)
        formalCoherence
    exact flatSourceEq.symm.trans (mappedCoherence.trans flatPositionalEq)
  let positionalPending : Region structuralOuter :=
    .mk (structuralBefore ++ .rel [] :: structuralAfter) flatFormalSource
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt
        (outer := structuralOuter) (localBefore := structuralBefore)
        (localAfter := structuralAfter) flatFormalSites positionalValues := by
    let positionalFrame : Transform.Frame []
        (structuralOuter ++ (structuralBefore ++ structuralAfter))
        (structuralOuter ++ (structuralBefore ++ .rel [] :: structuralAfter))
        (structuralOuter ++ (structuralBefore ++ .rel [] :: structuralAfter)) :=
      Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [.rel []] []
    have sourceIndependent := argumentItemsEdit_source_independent
      flatFormalSites positionalValues (normalizationOperation [])
      targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation []) positionalFrame PUnit.unit
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        rfl) (by rfl)
    have normalizedCoherence : flatFormalSource =
        (argumentItemsEdit flatFormalSites positionalValues
          (normalizationOperation []) positionalFrame PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 :=
      flatFormalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (structuralBefore ++ .rel [] :: structuralAfter))
      normalizedCoherence
  let stagedToFlatFormal : RegionIso (WireEquiv.refl common) staged
      flatFormalResult :=
    stagedPresentation.trans
      ((RegionIso.adjoinAtNil formalResult).symm.trans flatResultIso)
  have resultToFormal : HostedStrict result flatFormalResult :=
    HostedStrict.iso (RegionIso.refl result) stagedToFlatFormal hosted
  have resultToFormalScope : ScopePreservation result flatFormalResult :=
    stagedScope.trans (ScopePreservation.ofIso stagedToFlatFormal)
  let instantiated := Region.adjoinAt oldLocals .nil result
  let formalInstantiated :=
    Region.adjoinAt oldLocals .nil flatFormalResult
  have instantiatedToFormal : HostedStrict instantiated formalInstantiated := by
    simpa only [instantiated, formalInstantiated] using
      HostedStrict.adjoinAt oldLocals result flatFormalResult resultToFormal
  have instantiatedToFormalScope : ScopePreservation instantiated
      formalInstantiated :=
    adjoinAt_preserves_scope oldLocals .nil result flatFormalResult
      resultToFormalScope
  have instantiatedCanonical :
      (request.occurrence.context.fill instantiated).Canonical := by
    simpa only [instantiated, oldLocals] using request.instantiatedCanonical
  have instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill instantiated) := by
    intro signature wire
    simpa only [instantiated, oldLocals] using
      request.instantiatedExternalTwoEnded wire
  have formalValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context instantiated
    formalInstantiated instantiatedCanonical instantiatedExternalTwoEnded
    instantiatedToFormalScope
  have preparationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      instantiated formalInstantiated instantiatedCanonical
      instantiatedExternalTwoEnded formalValidity.1 formalValidity.2 :=
    telescopeOfHostedExact instantiatedToFormal request.polarity
      request.occurrence.interface request.occurrence.context
      instantiatedCanonical instantiatedExternalTwoEnded formalValidity.1
      formalValidity.2 request.continuation.1
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    request.occurrence.context.holeCanonical authoritativePending
      authoritativeValidity.1
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths flatFormalSites
    (EqualityNormalization.formalPorts wires)
    (normalizationOperation wires) authoritativeFrame PUnit.unit
    (fun _ _ _ => PUnit.unit) authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant targetFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := flatFormalSites.source_selectedPaths formalInvariant 0
  let selectedLocalIndex : Fin pendingLocals.length :=
    ⟨structuralBefore.length, by simp [pendingLocals]⟩
  have authoritativeRoot :=
    authoritativeLocalCanonical.1 selectedLocalIndex
  have selectedRooted : RegionPath.RootedTwo
      (flatFormalSource.incidencePaths
        (structuralOuter.length + structuralBefore.length) 0) := by
    have pathEq : flatFormalSource.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 =
        authoritativePending.items.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 := by
      calc
        flatFormalSource.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 =
            flatFormalSites.selectedPaths 0 := by
          simpa [targetFrame, Content.Ends.rootFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead]
            using formalPaths
        _ = authoritativePending.items.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems, authoritativeFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead,
            normalizationFrame] using authoritativePaths
    rw [pathEq]
    simpa [authoritativePending, selectedLocalIndex, pendingLocals] using
      authoritativeRoot
  let primitiveSites := Structural.Blank.endsItemsSites flatFormalEvidence
  let output := itemsEdit (operation := Content.Ends.operation [])
    PUnit.unit flatFormalEvidence primitiveSites
  have targetKeepIdentity : targetFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := structuralOuter)
      (right := structuralBefore ++ structuralAfter)
      (motive := fun wire => targetFrame.targetKeep wire = wire)
    · intro outerSignature outerWire
      simp [targetFrame, Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep]
    · intro localSignature localWire
      apply Var.appendCases (left := structuralBefore)
        (right := structuralAfter)
        (motive := fun localWire =>
          targetFrame.targetKeep
              (Var.appendRight structuralOuter localWire) =
            Var.appendRight structuralOuter localWire)
      · intro beforeSignature beforeWire
        simp [targetFrame, Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep]
      · intro afterSignature afterWire
        simp only [targetFrame, Content.Ends.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep,
          Var.appendMap_right]
        apply Var.eq_of_index_eq
        apply Fin.ext
        simp [Var.index_appendRight, Var.appendRight]
  obtain ⟨outputEndpointIso⟩ :=
    Structural.Blank.endsItemsEndpointIso_nonempty primitiveSites
      targetKeepIdentity
  let rawFormalInstantiated :=
    Region.adjoinAt oldLocals .nil output.edit.run
  let runToEndpoint : RegionIso (WireEquiv.refl common)
      output.edit.run output.endpoint :=
    RegionIso.ofEq output.run_eq
  let runToResult : RegionIso (WireEquiv.refl common)
      output.edit.run flatFormalResult :=
    runToEndpoint.trans outputEndpointIso
  let rawToFormal : RegionIso (WireEquiv.refl structuralOuter)
      rawFormalInstantiated formalInstantiated :=
    RegionIso.adjoinAt oldLocals .nil runToResult
  have rawToPositional : ScopePreservation rawFormalInstantiated
      positionalPending := by
    simpa only [rawFormalInstantiated, positionalPending, oldLocals] using
      Structural.Blank.endsTargetSourceScope output.edit selectedRooted
  have formalToPositional : ScopePreservation formalInstantiated
      positionalPending :=
    (ScopePreservation.ofIso rawToFormal.symm).trans rawToPositional
  have positionalValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context
    formalInstantiated positionalPending formalValidity.1 formalValidity.2
    formalToPositional
  have normalizationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      positionalPending request.endpoint positionalValidity.1
      positionalValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    argumentNormalizationTelescopeAllAt
      (outer := structuralOuter) (localBefore := structuralBefore)
      (localAfter := structuralAfter) flatFormalSites positionalValues
      request.occurrence.interface request.occurrence.context positionalEq
      positionalValidity.1 positionalValidity.2 authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded request.polarity request.continuation.1
      authoritativeContinuation
  let formalRequest : Telescope.Request instantiated positionalPending := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := positionalValidity.1
    pendingExternalTwoEnded := positionalValidity.2
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  let preparation : formalRequest.Preparation formalInstantiated := {
    prepared := formalInstantiated
    preparedCanonical := formalValidity.1
    preparedExternalTwoEnded := formalValidity.2
    rawPreparedCanonical := formalValidity.1
    rawPreparedExternalTwoEnded := formalValidity.2
    preparedIso := RegionIso.refl formalInstantiated
    telescope := by
      simpa only [formalRequest] using preparationTelescope
  }
  exact Structural.Blank.itemsEnds flatFormalEvidence formalRequest preparation

end Structural

end VisualProof.Rule.Completeness.Comprehension
