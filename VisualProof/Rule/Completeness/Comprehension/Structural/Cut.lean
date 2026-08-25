import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

structure SupportCutWrapScope
    {common sourceWires targetWires : List Sig}
    (frame : Transform.Frame [] common sourceWires targetWires)
    (data : (Content.Cut.operation []).Data frame)
    (source : Region sourceWires) (target : Region targetWires) : Prop where
  canonical : source.Canonical → target.Canonical
  retained : ∀ {signature} (wire : Var common signature),
    SupportParallelIncidenceScope
      (source.incidencePaths (frame.sourceKeep wire).index.val)
      (target.incidencePaths (frame.targetKeep wire).index.val)
  selected : SupportParallelIncidenceScope
    (source.incidencePaths frame.selected.index.val)
    (target.incidencePaths data.index.val)

theorem SupportCutWrapScope.iso
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Content.Cut.operation []).Data frame}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (scope : SupportCutWrapScope frame data sourceAfter targetBefore) :
    SupportCutWrapScope frame data sourceBefore targetAfter := by
  constructor
  · intro sourceCanonical
    exact targetIso.canonical_iff.mp
      (scope.canonical (sourceIso.canonical_iff.mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.iso sourceIso targetIso
      (frame.sourceKeep wire) (frame.targetKeep wire)
      (scope.retained wire)
  · exact SupportParallelIncidenceScope.iso sourceIso targetIso
      frame.selected data scope.selected

theorem SupportCutWrapScope.conjoin
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Content.Cut.operation []).Data frame}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : SupportCutWrapScope frame data sourceFirst targetFirst)
    (second : SupportCutWrapScope frame data sourceSecond targetSecond) :
    SupportCutWrapScope frame data (sourceFirst.conjoin sourceSecond)
      (targetFirst.conjoin targetSecond) := by
  constructor
  · intro sourceCanonical
    have pieces := (Region.Canonical.conjoin_iff _ _).mp sourceCanonical
    exact (Region.Canonical.conjoin_iff _ _).mpr
      ⟨first.canonical pieces.1, second.canonical pieces.2⟩
  · intro signature wire
    exact SupportParallelIncidenceScope.conjoin
      (frame.sourceKeep wire) (frame.targetKeep wire)
      (first.retained wire) (second.retained wire)
  · exact SupportParallelIncidenceScope.conjoin frame.selected data
      first.selected second.selected

theorem SupportCutWrapScope.cut
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Content.Cut.operation []).Data frame}
    {source : Region sourceWires} {target : Region targetWires}
    (scope : SupportCutWrapScope frame data source target) :
    SupportCutWrapScope frame data
      (Region.singleton (.cut source)) (Region.singleton (.cut target)) := by
  constructor
  · intro sourceCanonical
    exact (Region.singleton_cut_canonical_iff target).mpr
      (scope.canonical
        ((Region.singleton_cut_canonical_iff source).mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.cut
      (frame.sourceKeep wire) (frame.targetKeep wire)
      (scope.retained wire)
  · exact SupportParallelIncidenceScope.cut frame.selected data scope.selected

theorem SupportCutWrapScope.adjoin
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Content.Cut.operation []).Data frame}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (scope : SupportCutWrapScope (frame.append locals)
      ((Content.Cut.operation []).appendData frame data locals)
      source target) :
    SupportCutWrapScope frame data
      (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil target) := by
  constructor
  · intro sourceCanonical
    have sourceMaterialCanonical : source.Canonical :=
      Region.Canonical.material_of_adjoinAt locals .nil source sourceCanonical
    have targetMaterialCanonical := scope.canonical sourceMaterialCanonical
    apply Region.Canonical.adjoinAt_of_material_roots locals .nil target
      True.intro targetMaterialCanonical
    intro localIndex
    let localWire : Var (common ++ locals) (locals.get localIndex) :=
      Var.appendRight common (Var.ofIndex localIndex)
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
        sourceCanonical localIndex
    have sourceRoot' : RegionPath.RootedTwo
        (source.incidencePaths
          ((frame.append locals).sourceKeep localWire).index.val) := by
      simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
        using sourceRoot
    have targetRoot := (scope.retained localWire).rooted sourceRoot'
    simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
      using targetRoot
  · intro signature wire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      ((frame.sourceKeep wire).appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      ((frame.targetKeep wire).appendLeft locals)
    rw [show (frame.sourceKeep wire).index.val =
        ((frame.sourceKeep wire).appendLeft locals).index.val by simp,
      sourcePaths,
      show (frame.targetKeep wire).index.val =
        ((frame.targetKeep wire).appendLeft locals).index.val by simp,
      targetPaths]
    simpa [Transform.Frame.append, WireRenaming.appendRight] using
      scope.retained (wire.appendLeft locals)
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (frame.selected.appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      (data.appendLeft locals)
    rw [show frame.selected.index.val =
        (frame.selected.appendLeft locals).index.val by simp,
      sourcePaths,
      show data.index.val = (data.appendLeft locals).index.val by simp,
      targetPaths]
    simpa [Transform.Frame.append, Content.Cut.operation] using scope.selected

mutual
  theorem cutRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Content.Cut.operation arguments).Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Content.Cut.operation arguments) data evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := cutItemsSites_nonempty
          (data := (Content.Cut.operation arguments).appendData frame data _)
          childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem cutItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Content.Cut.operation arguments).Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (Content.Cut.operation arguments) data evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := cutItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := cutItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem cutItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Content.Cut.operation arguments).Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Content.Cut.operation arguments) data evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := cutRegionSites_nonempty childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

mutual
  theorem cutRegionEditScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Cut.operation []).Data frame}
      {source : Region sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.RegionEdit (Content.Cut.operation []) frame data
        source) :
      SupportCutWrapScope frame data source edit.run := by
    cases edit with
    | mk childEdit =>
        exact SupportCutWrapScope.iso
          (RegionIso.adjoinAtOfItems _ _).symm
          (RegionIso.refl _)
          (SupportCutWrapScope.adjoin _
          (cutItemsEditScope
            (Transform.RetainedIndexInvariant.append retainedInvariant _)
            (Transform.IndexedHeadInvariant.append headInvariant _)
            childEdit))
  termination_by sizeOf source

  theorem cutItemsEditScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Cut.operation []).Data frame}
      {source : ItemSeq sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemsEdit (Content.Cut.operation []) frame data
        source) :
      SupportCutWrapScope frame data (Region.ofItems source) edit.run := by
    cases edit with
    | nil =>
        constructor
        · intro canonical
          simpa [Transform.ItemsEdit.run] using canonical
        · intro signature wire
          have sourceEmpty :
              (Region.ofItems (ItemSeq.nil : ItemSeq sourceWires)).incidencePaths
              (frame.sourceKeep wire).index.val = [] := by
            rw [Region.incidencePaths_ofItems]
            rfl
          rw [sourceEmpty]
          exact SupportParallelIncidenceScope.refl []
        · have sourceEmpty :
              (Region.ofItems (ItemSeq.nil : ItemSeq sourceWires)).incidencePaths
              frame.selected.index.val = [] := by
            rw [Region.incidencePaths_ofItems]
            rfl
          rw [sourceEmpty]
          exact SupportParallelIncidenceScope.refl []
    | cons headEdit tailEdit =>
        rw [← Region.singleton_conjoin_ofItems]
        exact SupportCutWrapScope.conjoin
          (cutItemEditScope retainedInvariant headInvariant headEdit)
          (cutItemsEditScope retainedInvariant headInvariant tailEdit)
  termination_by sizeOf source

  theorem cutItemEditScope
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Content.Cut.operation []).Data frame}
      {source : Item sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemEdit (Content.Cut.operation []) frame data
        source) :
      SupportCutWrapScope frame data (Region.singleton source) edit.run := by
    cases edit with
    | atom head ports =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro signature wire
          have headEq :
              (frame.sourceKeep head).index.val =
                (frame.sourceKeep wire).index.val ↔
              (frame.targetKeep head).index.val =
                (frame.targetKeep wire).index.val := by
            rw [headInvariant.2.1 head, headInvariant.2.1 wire]
          have reflects : ∀ {leftSignature rightSignature}
              (left : Var common leftSignature)
              (right : Var common rightSignature),
              (frame.sourceKeep left).index.val =
                  (frame.sourceKeep right).index.val ↔
                (frame.targetKeep left).index.val =
                  (frame.targetKeep right).index.val := by
            intro leftSignature rightSignature left right
            rw [headInvariant.2.1 left, headInvariant.2.1 right]
          have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
            frame.sourceKeep frame.targetKeep reflects wire
          have pathsEq :
              (Region.singleton (.atom (frame.sourceKeep head)
                (ports.map fun port => frame.sourceKeep port))).incidencePaths
                  (frame.sourceKeep wire).index.val =
              (Region.singleton (.atom (frame.targetKeep head)
                (ports.map fun port => frame.targetKeep port))).incidencePaths
                  (frame.targetKeep wire).index.val := by
            simp only [Region.singleton, Region.ofItems,
              Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
              ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
              Var.index_appendLeft, Vars.countIndex_map_appendLeft_nil]
            simp only [headEq, portsEq]
          rw [pathsEq]
          exact SupportParallelIncidenceScope.refl _
        · have sourceHeadFresh := retainedInvariant.selectedFresh head
          have targetHeadFresh : data.index.val ≠
              (frame.targetKeep head).index.val := by
            rw [← headInvariant.2.2, ← headInvariant.2.1 head]
            exact sourceHeadFresh
          have sourcePortsZero :=
            Vars.countIndex_map_eq_zero_of_no_preimage ports frame.sourceKeep
              frame.selected.index.val
              (fun wire => Ne.symm (retainedInvariant.selectedFresh wire))
          have targetPortsZero :=
            Vars.countIndex_map_eq_zero_of_no_preimage ports frame.targetKeep
              data.index.val (fun wire => by
                rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
                exact Ne.symm (retainedInvariant.selectedFresh wire))
          have sourceEmpty :
              (Region.singleton (.atom (frame.sourceKeep head)
                (ports.map fun port => frame.sourceKeep port))).incidencePaths
                  frame.selected.index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              Ne.symm sourceHeadFresh,
              sourcePortsZero]
          have targetEmpty :
              (Region.singleton (.atom (frame.targetKeep head)
                (ports.map fun port => frame.targetKeep port))).incidencePaths
                  data.index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              Ne.symm targetHeadFresh,
              targetPortsZero]
          simp only [Transform.ItemEdit.run]
          rw [sourceEmpty, targetEmpty]
          exact SupportParallelIncidenceScope.refl []
    | selectedAtom ports siteData =>
        cases ports
        cases siteData
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index,
            ⟨⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩,
              True.intro⟩⟩
        · intro signature wire
          have sourceFresh := retainedInvariant.selectedFresh wire
          have targetFresh : data.index.val ≠
              (frame.targetKeep wire).index.val := by
            rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
            exact sourceFresh
          have sourceEmpty :
              (Region.singleton (.atom frame.selected .nil)).incidencePaths
                (frame.sourceKeep wire).index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex,
              sourceFresh]
          have targetEmpty :
              (Region.singleton (.cut
                (Region.singleton (.atom data .nil)))).incidencePaths
                  (frame.targetKeep wire).index.val = [] := by
            rw [Region.incidencePaths_singleton_cut]
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex,
              targetFresh]
          simp only [Transform.ItemEdit.run, Content.Cut.operation]
          have sourceEmpty' :
              (Region.singleton
                (.atom frame.selected
                  (Vars.nil.map fun port => frame.sourceKeep port))).incidencePaths
                    (frame.sourceKeep wire).index.val = [] := by
            simpa only [Vars.map] using sourceEmpty
          have targetEmpty' :
              (Region.singleton (.cut
                (Region.singleton
                  (.atom data
                    (Vars.nil.map fun port => frame.targetKeep port))))).incidencePaths
                      (frame.targetKeep wire).index.val = [] := by
            simpa only [Vars.map] using targetEmpty
          rw [sourceEmpty', targetEmpty']
          exact SupportParallelIncidenceScope.refl []
        · constructor
          · simp [Transform.ItemEdit.run, Content.Cut.operation,
              Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths]
          · intro rooted
            have impossible : ¬ RegionPath.RootedTwo
                ([[]] : List RegionPath) := by
              simp [RegionPath.RootedTwo]
            exact False.elim (impossible (by
              simpa [Region.singleton, Region.incidencePaths_ofItems,
                ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex]
                using rooted))
    | selectedPin ports selected =>
        have sourceIndex : (ports 0).index.val = data.index.val := by
          rw [selected, headInvariant.2.2]
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro signature wire
          have sourceFresh := retainedInvariant.selectedFresh wire
          have targetFresh : data.index.val ≠
              (frame.targetKeep wire).index.val := by
            rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
            exact sourceFresh
          have sourceCount :
              [frame.selected.index.val].count
                (frame.sourceKeep wire).index.val = 0 := by
            simp [sourceFresh]
          have targetCount :
              [data.index.val].count
                (frame.targetKeep wire).index.val = 0 := by
            simp [targetFresh]
          have sourceEmpty :
              (Region.singleton (.identity (.rel []) 1 ports)).incidencePaths
                (frame.sourceKeep wire).index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, selected,
              sourceCount]
          have targetEmpty :
              (Transform.unaryPin data).incidencePaths
                (frame.targetKeep wire).index.val = [] := by
            simp [Transform.unaryPin, Region.singleton,
              Region.incidencePaths_ofItems, ItemSeq.incidencePaths,
              Item.incidencePaths, targetCount]
          simp only [Transform.ItemEdit.run, Content.Cut.operation]
          rw [sourceEmpty, targetEmpty]
          exact SupportParallelIncidenceScope.refl []
        · have sourcePaths :
              (Region.singleton (.identity (.rel []) 1 ports)).incidencePaths
                frame.selected.index.val = [[]] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, selected]
          have targetPaths :
              (Transform.unaryPin data).incidencePaths data.index.val = [[]] := by
            simp [Transform.unaryPin, Region.singleton,
              Region.incidencePaths_ofItems, ItemSeq.incidencePaths,
              Item.incidencePaths]
          simp only [Transform.ItemEdit.run, Content.Cut.operation]
          rw [sourcePaths, targetPaths]
          exact SupportParallelIncidenceScope.refl [[]]
    | identity signature arity ports =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro wireSignature wire
          have portsEq := Transform.countPorts_map_eq_of_reflection arity ports
            frame.sourceKeep frame.targetKeep (fun left right => by
              rw [headInvariant.2.1 left, headInvariant.2.1 right]) wire
          simp only [Transform.ItemEdit.run, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft]
          rw [portsEq]
          exact SupportParallelIncidenceScope.refl _
        · have sourcePortsZero :=
            countPorts_map_eq_zero_of_no_preimage arity ports frame.sourceKeep
              frame.selected.index.val
              (fun wire => Ne.symm (retainedInvariant.selectedFresh wire))
          have targetPortsZero :=
            countPorts_map_eq_zero_of_no_preimage arity ports frame.targetKeep
              data.index.val (fun wire => by
                rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
                exact Ne.symm (retainedInvariant.selectedFresh wire))
          simp only [Transform.ItemEdit.run, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft]
          rw [sourcePortsZero, targetPortsZero]
          exact SupportParallelIncidenceScope.refl _
    | cut childEdit =>
        exact SupportCutWrapScope.cut
          (cutRegionEditScope retainedInvariant headInvariant childEdit)
  termination_by sizeOf source
end

/-- Root-level scope preservation for the exact nullary Cut endpoint. -/
theorem cutRootScope
    (outer before after : List Sig)
    {pattern : OpenDiagram []}
    {source : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern (Content.Cut.rootFrame outer before after []).sourceKeep
        (Content.Cut.rootFrame outer before after []).selected source result)
    (sites : ItemsSites (Content.Cut.operation [])
      (Content.Cut.targetHead outer before after []) evidence) :
    ScopePreservation
      (.mk (before ++ .rel [] :: after) source)
      (Region.adjoinAt (before ++ .rel [] :: after) .nil
        (itemsEdit (operation := Content.Cut.operation [])
          (Content.Cut.targetHead outer before after []) evidence sites).endpoint) := by
  let frame := Content.Cut.rootFrame outer before after []
  let data := Content.Cut.targetHead outer before after []
  let locals := before ++ .rel [] :: after
  let output := itemsEdit (operation := Content.Cut.operation []) data
    evidence sites
  have retainedInvariant : Transform.RetainedIndexInvariant frame := by
    exact Transform.RetainedIndexInvariant.replace outer before after
      [.rel []] []
  have headInvariant : Transform.IndexedHeadInvariant frame data := by
    exact ⟨rfl, (fun _ => rfl), rfl⟩
  have materialScope := cutItemsEditScope retainedInvariant headInvariant
    output.edit
  have outerScope : ∀ {signature} (wire : Var outer signature),
      SupportParallelIncidenceScope
        ((.mk locals source : Region outer).incidencePaths wire.index.val)
        ((Region.adjoinAt locals .nil output.endpoint).incidencePaths
          wire.index.val) := by
    intro signature wire
    let commonWire : Var (outer ++ (before ++ after)) signature :=
      wire.appendLeft (before ++ after)
    have materialIncidence : SupportParallelIncidenceScope
        ((Region.ofItems source).incidencePaths wire.index.val)
        (output.edit.run.incidencePaths wire.index.val) := by
      simpa [frame, commonWire, Content.Cut.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using
          materialScope.retained commonWire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems source) (wire.appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil
      output.edit.run (wire.appendLeft locals)
    have adjoinedIncidence : SupportParallelIncidenceScope
        ((Region.adjoinAt locals .nil
          (Region.ofItems source)).incidencePaths wire.index.val)
        ((Region.adjoinAt locals .nil output.edit.run).incidencePaths
          wire.index.val) := by
      rw [show wire.index.val = (wire.appendLeft locals).index.val by simp,
        sourcePaths, targetPaths]
      simpa using materialIncidence
    exact SupportParallelIncidenceScope.iso
      (RegionIso.adjoinAtOfItems locals source).symm
      (RegionIso.adjoinAt locals .nil (RegionIso.ofEq output.run_eq))
      wire wire adjoinedIncidence
  constructor
  · intro sourceCanonical
    have sourceAdjoinedCanonical :
        (Region.adjoinAt locals .nil (Region.ofItems source)).Canonical :=
      (RegionIso.adjoinAtOfItems locals source).canonical_iff.mpr
        sourceCanonical
    have sourceMaterialCanonical : (Region.ofItems source).Canonical :=
      Region.Canonical.material_of_adjoinAt locals .nil
        (Region.ofItems source) sourceAdjoinedCanonical
    have rawTargetCanonical :=
      materialScope.canonical sourceMaterialCanonical
    have targetMaterialCanonical : output.endpoint.Canonical := by
      rw [← output.run_eq]
      exact rawTargetCanonical
    apply Region.Canonical.adjoinAt_of_material_roots locals .nil
      output.endpoint True.intro targetMaterialCanonical
    intro localIndex
    let localWire := Var.ofIndex localIndex
    have targetRoot : RegionPath.RootedTwo
        (output.edit.run.incidencePaths
          (outer.length + localWire.index.val)) := by
      refine Var.appendCases (left := before) (right := .rel [] :: after)
        (motive := fun localWire => RegionPath.RootedTwo
          (output.edit.run.incidencePaths
            (outer.length + localWire.index.val))) ?_ ?_ localWire
      · intro signature beforeWire
        let sourceLocal : Var locals signature :=
          beforeWire.appendLeft (.rel [] :: after)
        let commonWire : Var (outer ++ (before ++ after)) signature :=
          Var.appendRight outer (beforeWire.appendLeft after)
        have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
        have sourceRoot : RegionPath.RootedTwo
            ((Region.ofItems source).incidencePaths
              (frame.sourceKeep commonWire).index.val) := by
          rw [Region.incidencePaths_ofItems]
          simpa [frame, locals, sourceLocal, commonWire,
            Content.Cut.rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight, Var.index] using
                sourceLocalRoot
        have transferred :=
          (materialScope.retained commonWire).rooted sourceRoot
        simpa [frame, commonWire, Content.Cut.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendRight, Var.index] using
            transferred
      · intro signature remaining
        cases remaining with
        | here =>
            let sourceLocal : Var locals (.rel []) :=
              Var.appendRight before .here
            have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
            have sourceRoot : RegionPath.RootedTwo
                ((Region.ofItems source).incidencePaths
                  frame.selected.index.val) := by
              rw [Region.incidencePaths_ofItems]
              simpa [frame, data, locals, sourceLocal,
                Content.Cut.rootFrame,
                Content.Cut.targetHead, Transform.Frame.replace,
                Transform.Frame.insertedHead, Var.appendRight, Var.index]
                using sourceLocalRoot
            have transferred := materialScope.selected.rooted sourceRoot
            simpa [frame, data, Content.Cut.rootFrame,
              Content.Cut.targetHead, Transform.Frame.replace,
              Transform.Frame.insertedHead, Var.appendRight, Var.index]
              using transferred
        | there afterWire =>
            let sourceLocal : Var locals signature :=
              Var.appendRight before (Var.there afterWire)
            let commonWire : Var (outer ++ (before ++ after)) signature :=
              Var.appendRight outer (Var.appendRight before afterWire)
            have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
            have sourceRoot : RegionPath.RootedTwo
                ((Region.ofItems source).incidencePaths
                  (frame.sourceKeep commonWire).index.val) := by
              rw [Region.incidencePaths_ofItems]
              simpa [frame, locals, sourceLocal, commonWire,
                Content.Cut.rootFrame,
                Transform.Frame.replace, Transform.Frame.keep,
                Transform.Frame.localKeep, Var.appendRight, Var.index]
                using sourceLocalRoot
            have transferred :=
              (materialScope.retained commonWire).rooted sourceRoot
            simpa [frame, commonWire, Content.Cut.rootFrame,
              Transform.Frame.replace, Transform.Frame.keep,
              Transform.Frame.localKeep, Var.appendRight, Var.index]
              using transferred
    rw [output.run_eq] at targetRoot
    simpa [localWire] using targetRoot
  · intro signature wire
    exact (outerScope wire).nonempty
  · intro signature wire rooted
    exact (outerScope wire).rooted rooted

def cutDataNaturality (arguments : List Sig) :
    DataNaturality (Content.Cut.operation arguments) where
  Coherent := fun _ _ data mappedData _ targetRename =>
    targetRename data = mappedData
  append := by
    intro common mappedCommon sourceWires mappedSourceWires targetWires
      mappedTargetWires frame mappedFrame data mappedData commonRename
      targetRename coherent locals
    simpa [Content.Cut.operation, WireRenaming.appendRight] using
      congrArg (fun wire => wire.appendLeft locals) coherent
  appendAssoc := by
    intro common sourceWires targetWires frame data first second
    simp [Content.Cut.operation, Region.adjoinMaterialWire]
  conjoinLeft := by
    intro common sourceWires targetWires frame data first second
    simp [Content.Cut.operation, Region.conjoinLeftWire]
  conjoinRight := by
    intro common sourceWires targetWires frame data first second
    simp [Content.Cut.operation, Region.conjoinRightWire]
  appendNil := by
    intro common sourceWires targetWires frame data
    exact WireEquiv.appendNil_symm_apply targetWires data
  site := by
    intro common mappedCommon sourceWires mappedSourceWires targetWires
      mappedTargetWires frame mappedFrame data mappedData commonRename
      targetRename coherent targetKeepCommutes ports siteData
    cases siteData
    refine ⟨PUnit.unit, ⟨RegionIso.ofEq ?_⟩⟩
    have targetMaps : WireRenaming.comp targetRename frame.targetKeep =
        WireRenaming.comp mappedFrame.targetKeep commonRename := by
      apply WireRenaming.ext
      intro signature wire
      exact targetKeepCommutes wire
    simp only [Content.Cut.operation, Region.singleton_renameWires,
      Item.renameWires, coherent]
    apply congrArg Region.singleton
    apply congrArg Item.cut
    apply congrArg Region.singleton
    apply congrArg (Item.atom mappedData)
    exact (Diagram.vars_map_comp ports frame.targetKeep targetRename).trans
      ((congrArg (fun rename : WireRenaming common mappedTargetWires =>
        ports.map fun wire => rename wire) targetMaps).trans
        (Diagram.vars_map_comp ports commonRename mappedFrame.targetKeep).symm)

def cutDataSelects
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    (data : (Content.Cut.operation []).Data frame)
    (head : Var targetWires (.rel [])) : Prop :=
  head = data

theorem cutDataSelects_append
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    (data : (Content.Cut.operation []).Data frame)
    (head : Var targetWires (.rel []))
    (selects : cutDataSelects data head)
    (locals : List Sig) :
    cutDataSelects
      ((Content.Cut.operation []).appendData frame data locals)
      (head.appendLeft locals) := by
  exact congrArg (fun wire => wire.appendLeft locals) selects

def cutDataAligned
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame [] common localSourceWires localTargetWires}
    {formalFrame : Transform.Frame [] common formalSourceWires formalTargetWires}
    (localData : (Content.Cut.operation []).Data localFrame)
    (formalData : (Content.Cut.operation []).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires) : Prop :=
  ambient.toRenaming localData = formalData

theorem cutDataAligned_append
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame [] common localSourceWires localTargetWires}
    {formalFrame : Transform.Frame [] common formalSourceWires formalTargetWires}
    (localData : (Content.Cut.operation []).Data localFrame)
    (formalData : (Content.Cut.operation []).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires)
    (aligned : cutDataAligned localData formalData ambient)
    (locals : List Sig) :
    cutDataAligned
      ((Content.Cut.operation []).appendData localFrame localData locals)
      ((Content.Cut.operation []).appendData formalFrame formalData locals)
      (ambient.append (WireEquiv.refl locals)) := by
  simpa only [cutDataAligned, Content.Cut.operation,
    WireEquiv.append_apply_left] using
      congrArg (fun wire => wire.appendLeft locals) aligned

theorem cutSelectedTargetItem
    (body : Region []) (bodyCanonical : body.Canonical)
    {itemCommon itemSourceWires itemTargetWires : List Sig}
    {fullPattern : OpenDiagram []}
    {itemFrame : Transform.Frame [] itemCommon itemSourceWires itemTargetWires}
    {itemData : (Content.Cut.operation []).Data itemFrame}
    (fullPatternEq : fullPattern = Erasure.Exposure.supportPattern
      (Region.singleton (.cut body))
      ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
    (application : Vars itemCommon [])
    (siteData : (Content.Cut.operation []).SiteData itemFrame itemData
      application)
    {formalSourceWires formalTargetWires : List Sig}
    (formalFrame : Transform.Frame [] itemCommon formalSourceWires
      formalTargetWires)
    (formalData : (Content.Cut.operation []).Data formalFrame) :
    TargetItem
      (targetExternal := [])
      (targetPattern := Erasure.Exposure.supportPattern body bodyCanonical)
      (targetOperation := Content.Cut.operation [])
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := Content.Cut.operation [])
        (pattern := fullPattern) (frame := itemFrame) application siteData)
      (Vars.nil : Vars [] []) formalFrame formalData
      (fun retained formalSource formalResult _formalEvidence _formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                fullPattern application) staged ∧
              ScopePreservation
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  fullPattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
              ∀ (bridge : TargetFrameBridge formalFrame cutDataSelects
                    formalData)
                (alignment : TargetAmbientBridge itemFrame formalFrame
                  cutDataAligned itemData formalData),
                Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                  ((itemEdit itemData
                    (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                      (pattern := fullPattern) (retain := itemFrame.sourceKeep)
                      (selected := itemFrame.selected) application)
                    (ItemSites.selectedAtom (operation := Content.Cut.operation [])
                      (pattern := fullPattern) (frame := itemFrame)
                      application siteData)).endpoint.renameWires
                        alignment.ambient.toRenaming)
                  (.mk retained (formalSource.renameWires
                    (bridge.sourceToTarget.appendRight retained))))) := by
  subst fullPattern
  unfold TargetItem
  let childPattern := Erasure.Exposure.supportPattern body bodyCanonical
  let rootFrame := formalFrame.append []
  let rootData := (Content.Cut.operation []).appendData formalFrame formalData []
  let childFrame := rootFrame.append []
  let childData := (Content.Cut.operation []).appendData rootFrame rootData []
  let rootApplication : Vars (itemCommon ++ []) [] :=
    application.map fun wire => wire.appendLeft []
  let childApplication : Vars ((itemCommon ++ []) ++ []) [] :=
    rootApplication.map fun wire => wire.appendLeft []
  let childItemEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected) childApplication
  let childTailEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected)
  let childItemsEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      childItemEvidence childTailEvidence
  let childRegionEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
      childItemsEvidence
  let cutItemEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
      childRegionEvidence
  let cutTailEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      (pattern := childPattern) (retain := rootFrame.sourceKeep)
      (selected := rootFrame.selected)
  let formalEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      cutItemEvidence cutTailEvidence
  let recordedCut := recordingOperation (Content.Cut.operation []) []
  let childItemSites : ItemSites recordedCut childData childItemEvidence :=
    .selectedAtom (pattern := childPattern) childApplication
      ⟨PUnit.unit, childApplication⟩
  let childTailSites : ItemsSites recordedCut childData
      childTailEvidence := .nil childTailEvidence
  let childItemsSites : ItemsSites recordedCut childData
      childItemsEvidence := .cons childItemSites childTailSites
  let childRegionSites : RegionSites recordedCut rootData
      childRegionEvidence := .mk childItemsSites
  let cutItemSites : ItemSites recordedCut rootData
      cutItemEvidence := .cut childRegionSites
  let cutTailSites : ItemsSites recordedCut rootData
      cutTailEvidence := .nil cutTailEvidence
  let formalSites : ItemsSites recordedCut rootData
      formalEvidence := .cons cutItemSites cutTailSites
  refine ⟨[], _, _, formalEvidence, formalSites, ?_, ?_⟩
  · cases application
    rfl
  · let staged := Region.singleton (.cut
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern application))
    refine ⟨staged, ?_, ?_, ?_⟩
    · exact supportCutInstantiatedHosted body bodyCanonical application
    · have stagedCanonical : staged.Canonical := by
        exact (Region.singleton_cut_canonical_iff _).mpr
          (VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
            childPattern application)
      have sourceEmpty : ∀ {signature} (wire : Var itemCommon signature),
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern (Region.singleton (.cut body))
              ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
            application).incidencePaths wire.index.val = [] := by
        intro signature wire
        apply List.eq_nil_of_length_eq_zero
        rw [EqualityNormalization.instantiate_incidencePaths_length]
        cases application
        rfl
      have stagedEmpty : ∀ {signature} (wire : Var itemCommon signature),
          staged.incidencePaths wire.index.val = [] := by
        intro signature wire
        have childEmpty :
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              childPattern application).incidencePaths wire.index.val = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [EqualityNormalization.instantiate_incidencePaths_length]
          cases application
          rfl
        dsimp only [staged]
        rw [Region.incidencePaths_singleton_cut, childEmpty]
        rfl
      exact ScopePreservation.of_incidence_empty stagedCanonical sourceEmpty
        stagedEmpty
    · let commonEquiv := WireEquiv.appendNil itemCommon
      let commonRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let childBase :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern application
      let rootResult :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern rootApplication
      let childResult :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern childApplication
      let childEquiv := WireEquiv.appendNil (itemCommon ++ [])
      let childRename : WireRenaming (itemCommon ++ [])
          ((itemCommon ++ []) ++ []) := childEquiv.symm.toRenaming
      let rootMapped : RegionIso (WireEquiv.refl (itemCommon ++ []))
          (childBase.renameWires commonRename) rootResult := by
        have applicationEq :
            application.map (fun wire => commonRename wire) =
              rootApplication := by
          apply Vars.map_congr
          intro signature wire
          exact WireEquiv.appendNil_symm_apply itemCommon wire
        simpa only [childBase, rootResult, applicationEq] using
          EqualityNormalization.instantiateRenameIso childPattern
            application commonRename
      let directToCollapsed := RegionIso.renameWires rootResult
        WireRenaming.id
        (WireRenaming.comp childEquiv.toRenaming childRename)
        (WireEquiv.refl (itemCommon ++ [])) (by
          intro signature wire
          exact (childEquiv.right_inv wire).symm)
      let collapsedFromHosted :=
        (RegionIso.renameWiresComp rootResult childRename
          childEquiv.toRenaming).symm
      let rootHostedRaw := (directToCollapsed.trans collapsedFromHosted).trans
        (RegionIso.adjoinAtNil (rootResult.renameWires childRename))
      have rootHostedAmbient :
          (((WireEquiv.refl (itemCommon ++ [])).trans
            (WireEquiv.refl (itemCommon ++ [])).symm).trans
              (WireEquiv.refl (itemCommon ++ []))) =
            WireEquiv.refl (itemCommon ++ []) := by
        apply WireEquiv.ext
        intro signature wire
        rfl
      let rootHosted : RegionIso (WireEquiv.refl (itemCommon ++ []))
          rootResult
          (Region.adjoinAt [] .nil
            (rootResult.renameWires childRename)) := by
        simpa only [Region.renameWires_id] using
          rootHostedRaw.castAmbient rootHostedAmbient
      let childMapped : RegionIso (WireEquiv.refl ((itemCommon ++ []) ++ []))
          (rootResult.renameWires childRename) childResult := by
        have applicationEq :
            rootApplication.map (fun wire => childRename wire) =
              childApplication := by
          apply Vars.map_congr
          intro signature wire
          exact WireEquiv.appendNil_symm_apply (itemCommon ++ []) wire
        simpa only [rootResult, childResult, applicationEq] using
          EqualityNormalization.instantiateRenameIso childPattern
            rootApplication childRename
      let childWithBlank : RegionIso
          (WireEquiv.refl ((itemCommon ++ []) ++ []))
          (rootResult.renameWires childRename)
          (childResult.conjoin (Region.blank ((itemCommon ++ []) ++ []))) :=
        childMapped.trans (RegionIso.conjoinBlank childResult).symm
      let childIntoFormal : RegionIso (WireEquiv.refl (itemCommon ++ []))
          (childBase.renameWires commonRename)
          (Region.adjoinAt [] .nil
            (childResult.conjoin (Region.blank ((itemCommon ++ []) ++ [])))) :=
        rootMapped.trans (rootHosted.trans
          (RegionIso.adjoinAt [] .nil childWithBlank))
      let formalItemResult := Region.singleton (.cut
        (Region.adjoinAt [] .nil
          (childResult.conjoin (Region.blank ((itemCommon ++ []) ++ [])))))
      let itemIntoFormal : RegionIso (WireEquiv.refl (itemCommon ++ []))
          (Region.singleton (.cut (childBase.renameWires commonRename)))
          formalItemResult := RegionIso.singletonCutCongr childIntoFormal
      let stagedIntoFormal : RegionIso commonEquiv.symm staged
          formalItemResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonRename commonEquiv.symm (by
            intro signature wire
            rfl)
        rw [Region.renameWires_id] at renamed
        have targetEq : staged.renameWires commonRename =
            Region.singleton (.cut (childBase.renameWires commonRename)) := by
          simp only [staged, childBase, Region.singleton_renameWires,
            Item.renameWires]
        rw [targetEq] at renamed
        exact renamed.trans itemIntoFormal
      let formalResult := formalItemResult.conjoin
        (Region.blank (itemCommon ++ []))
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        stagedIntoFormal.trans (RegionIso.conjoinBlank formalItemResult).symm
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      exact ⟨⟨closed.castAmbient ambientEq⟩, by
        intro bridge alignment
        cases application
        let formalSource : ItemSeq (formalSourceWires ++ []) :=
          .cons (.cut (.mk [] (.cons
            (.atom childFrame.selected
              (childApplication.map fun wire =>
                childFrame.sourceKeep wire)) .nil))) .nil
        let renamedFormalSource := formalSource.renameWires
          (bridge.sourceToTarget.appendRight [])
        let material := Region.ofItems renamedFormalSource
        let directAtom : Region formalTargetWires :=
          Region.singleton (.atom formalData .nil)
        have sourceEq :
            (itemEdit itemData
              (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                (pattern := Erasure.Exposure.supportPattern
                  (Region.singleton (.cut body))
                  ((Region.singleton_cut_canonical_iff body).mpr
                    bodyCanonical))
                (retain := itemFrame.sourceKeep)
                (selected := itemFrame.selected) Vars.nil)
              (ItemSites.selectedAtom
                (operation := Content.Cut.operation [])
                (pattern := Erasure.Exposure.supportPattern
                  (Region.singleton (.cut body))
                  ((Region.singleton_cut_canonical_iff body).mpr
                    bodyCanonical))
                (frame := itemFrame) Vars.nil siteData)).endpoint.renameWires
                  alignment.ambient.toRenaming =
              Region.singleton (.cut directAtom) := by
          have dataEq := alignment.data_aligned
          unfold cutDataAligned at dataEq
          simp only [itemEdit, ExactEdit.refl, Content.Cut.operation,
            Transform.ItemEdit.run, Region.singleton_renameWires,
            Item.renameWires, Vars.map, directAtom]
          rw [dataEq]
        have targetEq : Region.singleton (.cut directAtom) =
            material.renameWires
              (WireEquiv.appendNil formalTargetWires).toRenaming := by
          unfold material renamedFormalSource formalSource directAtom
          simp only [Region.singleton, Region.ofItems, Region.renameWires,
            ItemSeq.renameWires, Item.renameWires, WireRenaming.appendRight,
            Transform.Frame.append, childFrame, rootFrame,
            childApplication, rootApplication]
          simp [Vars.map, Var.appendMap_left,
            WireEquiv.appendNil_apply]
          have headEq := bridge.data_selects
          unfold cutDataSelects at headEq
          rw [bridge.selected_commutes, headEq]
        refine ⟨?_⟩
        change RegionIso (WireEquiv.refl formalTargetWires)
          ((itemEdit itemData
            (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
              (pattern := Erasure.Exposure.supportPattern
                (Region.singleton (.cut body))
                ((Region.singleton_cut_canonical_iff body).mpr
                  bodyCanonical))
              (retain := itemFrame.sourceKeep)
              (selected := itemFrame.selected) Vars.nil)
            (ItemSites.selectedAtom
              (operation := Content.Cut.operation [])
              (pattern := Erasure.Exposure.supportPattern
                (Region.singleton (.cut body))
                ((Region.singleton_cut_canonical_iff body).mpr
                  bodyCanonical))
              (frame := itemFrame) Vars.nil siteData)).endpoint.renameWires
                alignment.ambient.toRenaming)
          (.mk [] renamedFormalSource)
        simpa only [WireEquiv.trans_refl] using
          ((RegionIso.ofEq sourceEq).trans (RegionIso.ofEq targetEq)).trans
            ((RegionIso.adjoinAtNil material).trans
              (RegionIso.adjoinAtOfItems [] renamedFormalSource))⟩

/-- The cut constructor is derivable from the recursively derived body. -/
theorem supportCutDerives
    {wires : List Sig} (body : Region wires)
    (bodyIH : SupportDerives body) :
    SupportDerives (Region.singleton (.cut body)) := by
  sorry
end Structural

end VisualProof.Rule.Completeness.Comprehension
