import VisualProof.Rule.Completeness.Comprehension.Structural.Boundary
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

structure SupportArityShiftScope
    {common sourceWires targetWires : List Sig}
    {added : Sig}
    (frame : Transform.Frame [] common sourceWires targetWires)
    (data : (Arity.operation [] added).Data frame)
    (source : Region sourceWires) (target : Region targetWires) : Prop where
  canonical : source.Canonical → target.Canonical
  retained : ∀ {signature} (wire : Var common signature),
    SupportParallelIncidenceScope
      (source.incidencePaths (frame.sourceKeep wire).index.val)
      (target.incidencePaths (frame.targetKeep wire).index.val)
  selected : SupportParallelIncidenceScope
    (source.incidencePaths frame.selected.index.val)
    (target.incidencePaths data.index.val)

theorem SupportArityShiftScope.iso
    {added : Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Arity.operation [] added).Data frame}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (scope : SupportArityShiftScope frame data sourceAfter targetBefore) :
    SupportArityShiftScope frame data sourceBefore targetAfter := by
  constructor
  · intro sourceCanonical
    exact targetIso.canonical_iff.mp
      (scope.canonical (sourceIso.canonical_iff.mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.iso sourceIso targetIso
      (frame.sourceKeep wire) (frame.targetKeep wire) (scope.retained wire)
  · change Var targetWires (.rel [added]) at data
    exact SupportParallelIncidenceScope.iso sourceIso targetIso
      frame.selected data scope.selected

theorem SupportArityShiftScope.conjoin
    {added : Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Arity.operation [] added).Data frame}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : SupportArityShiftScope frame data sourceFirst targetFirst)
    (second : SupportArityShiftScope frame data sourceSecond targetSecond) :
    SupportArityShiftScope frame data (sourceFirst.conjoin sourceSecond)
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
  · change Var targetWires (.rel [added]) at data
    exact SupportParallelIncidenceScope.conjoin frame.selected data
      first.selected second.selected

theorem SupportArityShiftScope.cut
    {added : Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Arity.operation [] added).Data frame}
    {source : Region sourceWires} {target : Region targetWires}
    (scope : SupportArityShiftScope frame data source target) :
    SupportArityShiftScope frame data
      (Region.singleton (.cut source)) (Region.singleton (.cut target)) := by
  constructor
  · intro sourceCanonical
    exact (Region.singleton_cut_canonical_iff target).mpr
      (scope.canonical
        ((Region.singleton_cut_canonical_iff source).mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.cut
      (frame.sourceKeep wire) (frame.targetKeep wire) (scope.retained wire)
  · change Var targetWires (.rel [added]) at data
    exact SupportParallelIncidenceScope.cut frame.selected data scope.selected

theorem SupportArityShiftScope.adjoin
    {added : Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Arity.operation [] added).Data frame}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (scope : SupportArityShiftScope (frame.append locals)
      ((Arity.operation [] added).appendData frame data locals) source target) :
    SupportArityShiftScope frame data
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
    simpa [Transform.Frame.append, Arity.operation] using scope.selected

mutual
  theorem arityRegionSites_nonempty
      {added : Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {pattern : OpenDiagram []}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Arity.operation [] added) data evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := arityItemsSites_nonempty
          (frame := frame.append _)
          (data := (Arity.operation [] added).appendData frame data _)
          childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem arityItemsSites_nonempty
      {added : Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {pattern : OpenDiagram []}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (Arity.operation [] added) data evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := arityItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := arityItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem arityItemSites_nonempty
      {added : Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {pattern : OpenDiagram []}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Arity.operation [] added) data evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := arityRegionSites_nonempty childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

theorem aritySelectedAtomScope
    {added : Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {data : (Arity.operation [] added).Data frame}
    (retainedInvariant : Transform.RetainedIndexInvariant frame)
    (headInvariant : Transform.IndexedHeadInvariant frame data)
    (ports : Vars common [])
    (siteData : (Arity.operation [] added).SiteData frame data ports) :
    SupportArityShiftScope frame data
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((Arity.operation [] added).site frame data ports siteData) := by
  cases ports
  cases siteData
  change Var targetWires (.rel [added]) at data
  change SupportArityShiftScope frame data
    (Region.singleton (.atom frame.selected .nil))
    (Region.mk [added]
      (.cons
        (.atom (data.appendLeft [added])
          (.cons (Var.appendRight targetWires .here) .nil))
        (.cons (.identity added 1 (fun _ =>
          Var.appendRight targetWires .here)) .nil)))
  constructor
  · intro _
    have dataLt : data.index.val < targetWires.length := data.index.isLt
    constructor
    · intro localIndex
      cases localIndex using Fin.cases with
      | zero =>
        simp [Region.incidencePaths,
        ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex,
        RegionPath.RootedTwo, Nat.ne_of_lt dataLt]
      | succ index => exact Fin.elim0 index
    · exact ⟨True.intro, ⟨True.intro, True.intro⟩⟩
  · intro signature wire
    have sourceFresh := retainedInvariant.selectedFresh wire
    have targetFresh : data.index.val ≠
        (frame.targetKeep wire).index.val := by
      intro equality
      apply sourceFresh
      rw [headInvariant.2.2, headInvariant.2.1 wire]
      exact equality
    have targetBound := (frame.targetKeep wire).index.isLt
    have targetNotLocal : (frame.targetKeep wire).index.val ≠
        targetWires.length := Nat.ne_of_lt targetBound
    have sourcePaths :
        (Region.singleton (.atom frame.selected .nil)).incidencePaths
          (frame.sourceKeep wire).index.val = [] := by
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex,
        sourceFresh]
    have targetPaths :
        (Region.mk [added]
          (.cons
            (.atom (data.appendLeft [added])
              (.cons (Var.appendRight targetWires .here) .nil))
            (.cons (.identity added 1 (fun _ =>
              Var.appendRight targetWires .here)) .nil))).incidencePaths
            (frame.targetKeep wire).index.val = [] := by
      simp [Region.incidencePaths, ItemSeq.incidencePaths,
        Item.incidencePaths, Vars.countIndex, targetFresh,
        targetNotLocal, Ne.symm targetFresh, Ne.symm targetNotLocal]
    simpa only [sourcePaths, targetPaths] using
      (SupportParallelIncidenceScope.refl [])
  · have dataLt : data.index.val < targetWires.length := data.index.isLt
    have dataNotLocal : data.index.val ≠ targetWires.length :=
      Nat.ne_of_lt dataLt
    have sourcePaths :
        (Region.singleton (.atom frame.selected .nil)).incidencePaths
          frame.selected.index.val = [[]] := by
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex]
    have targetPaths :
        (Region.mk [added]
          (.cons
            (.atom (data.appendLeft [added])
              (.cons (Var.appendRight targetWires .here) .nil))
            (.cons (.identity added 1 (fun _ =>
              Var.appendRight targetWires .here)) .nil))).incidencePaths
            data.index.val = [[]] := by
      simp [Region.incidencePaths, ItemSeq.incidencePaths,
        Item.incidencePaths, Vars.countIndex, dataNotLocal,
        Ne.symm dataNotLocal]
    have pairEq :
        ((Region.singleton (.atom frame.selected .nil)).incidencePaths
            frame.selected.index.val,
          (Region.mk [added]
            (.cons
              (.atom (data.appendLeft [added])
                (.cons (Var.appendRight targetWires .here) .nil))
              (.cons (.identity added 1 (fun _ =>
                Var.appendRight targetWires .here)) .nil))).incidencePaths
              data.index.val) =
          (([[]] : List RegionPath), ([[]] : List RegionPath)) :=
      Prod.ext sourcePaths targetPaths
    have typeEq := congrArg
      (fun paths : List RegionPath × List RegionPath =>
        SupportParallelIncidenceScope paths.1 paths.2) pairEq
    exact Eq.mp typeEq.symm (SupportParallelIncidenceScope.refl [[]])

mutual
  theorem arityRegionEditScope
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {source : Region sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.RegionEdit (Arity.operation [] added) frame data
        source) :
      SupportArityShiftScope frame data source edit.run := by
    cases edit with
    | mk childEdit =>
        exact SupportArityShiftScope.iso
          (RegionIso.adjoinAtOfItems _ _).symm
          (RegionIso.refl _)
          (SupportArityShiftScope.adjoin _
          (arityItemsEditScope
            (Transform.RetainedIndexInvariant.append retainedInvariant _)
            (Transform.IndexedHeadInvariant.append headInvariant _)
            childEdit))
  termination_by sizeOf source

  theorem arityItemsEditScope
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {source : ItemSeq sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemsEdit (Arity.operation [] added) frame data
        source) :
      SupportArityShiftScope frame data (Region.ofItems source) edit.run := by
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
        exact SupportArityShiftScope.conjoin
          (arityItemEditScope retainedInvariant headInvariant headEdit)
          (arityItemsEditScope retainedInvariant headInvariant tailEdit)
  termination_by sizeOf source

  theorem arityItemEditScope
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {data : (Arity.operation [] added).Data frame}
      {source : Item sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemEdit (Arity.operation [] added) frame data
        source) :
      SupportArityShiftScope frame data (Region.singleton source) edit.run := by
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
              targetHeadFresh, targetPortsZero, beq_iff_eq]
            exact ⟨Ne.symm targetHeadFresh, targetPortsZero⟩
          simp only [Transform.ItemEdit.run]
          rw [sourceEmpty, targetEmpty]
          exact SupportParallelIncidenceScope.refl []
    | selectedAtom ports siteData =>
        exact aritySelectedAtomScope retainedInvariant headInvariant ports siteData
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
            simp [List.count_cons, List.count_nil, targetFresh, beq_iff_eq]
            exact targetFresh
          have sourceEmpty :
              (Region.singleton (.identity (.rel []) 1 ports)).incidencePaths
                (frame.sourceKeep wire).index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, selected,
              sourceCount]
          have targetEmpty :
              (Transform.unaryPin data).incidencePaths
                (frame.targetKeep wire).index.val = [] := by
            simp only [Transform.unaryPin, Region.singleton,
              Region.incidencePaths_ofItems, ItemSeq.incidencePaths,
              Item.incidencePaths, List.replicate, List.map,
              List.cons_append, List.nil_append]
            simpa [List.ofFn_succ, List.ofFn_zero] using targetCount
          simp only [Transform.ItemEdit.run]
          rw [sourceEmpty]
          change SupportParallelIncidenceScope []
            ((Transform.unaryPin data).incidencePaths
              (frame.targetKeep wire).index.val)
          rw [targetEmpty]
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
          simp only [Transform.ItemEdit.run]
          rw [sourcePaths]
          change SupportParallelIncidenceScope [[]]
            ((Transform.unaryPin data).incidencePaths data.index.val)
          rw [targetPaths]
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
        exact SupportArityShiftScope.cut
          (arityRegionEditScope retainedInvariant headInvariant childEdit)
  termination_by sizeOf source
end


/-- Root-level scope preservation for the exact nullary Arity endpoint. -/
theorem arityRootScope
    (outer before after : List Sig) (added : Sig)
    {pattern : OpenDiagram []}
    {source : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern (Arity.rootFrame outer before after [] added).sourceKeep
        (Arity.rootFrame outer before after [] added).selected source result)
    (sites : ItemsSites (Arity.operation [] added)
      (Arity.targetHead outer before after [] added) evidence) :
    ScopePreservation
      (.mk (before ++ .rel [] :: after) source)
      (Region.adjoinAt (before ++ .rel [added] :: after) .nil
        (itemsEdit (operation := Arity.operation [] added)
          (Arity.targetHead outer before after [] added) evidence sites).endpoint) := by
  let frame := Arity.rootFrame outer before after [] added
  let data := Arity.targetHead outer before after [] added
  let sourceLocals := before ++ .rel [] :: after
  let targetLocals := before ++ .rel [added] :: after
  let output := itemsEdit (operation := Arity.operation [] added) data
    evidence sites
  have retainedInvariant : Transform.RetainedIndexInvariant frame := by
    exact Transform.RetainedIndexInvariant.replace outer before after
      [.rel [added]] []
  have headInvariant : Transform.IndexedHeadInvariant frame data := by
    refine ⟨by simp [frame, Arity.rootFrame], ?_, ?_⟩
    · intro signature wire
      refine Var.appendCases (left := outer) (right := before ++ after)
        (motive := fun wire =>
          (frame.sourceKeep wire).index.val =
            (frame.targetKeep wire).index.val) ?_ ?_ wire
      · intro outerSignature outerWire
        simp [frame, Arity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep]
      · intro localSignature localWire
        refine Var.appendCases (left := before) (right := after)
          (motive := fun wire =>
            (frame.sourceKeep (Var.appendRight outer wire)).index.val =
              (frame.targetKeep (Var.appendRight outer wire)).index.val)
          ?_ ?_ localWire
        · intro beforeSignature beforeWire
          simp [frame, Arity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Var.appendRight, Var.index]
        · intro afterSignature afterWire
          simp [frame, Arity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Var.appendRight, Var.index]
    · simp [frame, data, Arity.rootFrame, Arity.targetHead,
        Transform.Frame.replace, Transform.Frame.insertedHead,
        Var.appendRight, Var.index]
  have materialScope := arityItemsEditScope retainedInvariant headInvariant
    output.edit
  have outerScope : ∀ {signature} (wire : Var outer signature),
      SupportParallelIncidenceScope
        ((.mk sourceLocals source : Region outer).incidencePaths wire.index.val)
        ((Region.adjoinAt targetLocals .nil output.endpoint).incidencePaths
          wire.index.val) := by
    intro signature wire
    let commonWire : Var (outer ++ (before ++ after)) signature :=
      wire.appendLeft (before ++ after)
    have materialIncidence : SupportParallelIncidenceScope
        ((Region.ofItems source).incidencePaths wire.index.val)
        (output.edit.run.incidencePaths wire.index.val) := by
      simpa [frame, commonWire, Arity.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using
          materialScope.retained commonWire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems source) (wire.appendLeft sourceLocals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil
      output.edit.run (wire.appendLeft targetLocals)
    have sourcePaths' :
        (Region.adjoinAt sourceLocals .nil
          (Region.ofItems source)).incidencePaths wire.index.val =
        (Region.ofItems source).incidencePaths wire.index.val := by
      simpa using sourcePaths
    have targetPaths' :
        (Region.adjoinAt targetLocals .nil output.edit.run).incidencePaths
            wire.index.val =
          output.edit.run.incidencePaths wire.index.val := by
      simpa using targetPaths
    have adjoinedIncidence : SupportParallelIncidenceScope
        ((Region.adjoinAt sourceLocals .nil
          (Region.ofItems source)).incidencePaths wire.index.val)
        ((Region.adjoinAt targetLocals .nil output.edit.run).incidencePaths
          wire.index.val) := by
      rw [sourcePaths', targetPaths']
      simpa using materialIncidence
    exact SupportParallelIncidenceScope.iso
      (RegionIso.adjoinAtOfItems sourceLocals source).symm
      (RegionIso.adjoinAt targetLocals .nil (RegionIso.ofEq output.run_eq))
      wire wire adjoinedIncidence
  constructor
  · intro sourceCanonical
    have sourceAdjoinedCanonical :
        (Region.adjoinAt sourceLocals .nil (Region.ofItems source)).Canonical :=
      (RegionIso.adjoinAtOfItems sourceLocals source).canonical_iff.mpr
        sourceCanonical
    have sourceMaterialCanonical : (Region.ofItems source).Canonical :=
      Region.Canonical.material_of_adjoinAt sourceLocals .nil
        (Region.ofItems source) sourceAdjoinedCanonical
    have rawTargetCanonical :=
      materialScope.canonical sourceMaterialCanonical
    have targetMaterialCanonical : output.endpoint.Canonical := by
      rw [← output.run_eq]
      exact rawTargetCanonical
    apply Region.Canonical.adjoinAt_of_material_roots targetLocals .nil
      output.endpoint True.intro targetMaterialCanonical
    intro localIndex
    let localWire := Var.ofIndex localIndex
    have targetRoot : RegionPath.RootedTwo
        (output.edit.run.incidencePaths
          (outer.length + localWire.index.val)) := by
      refine Var.appendCases (left := before) (right := .rel [added] :: after)
        (motive := fun localWire => RegionPath.RootedTwo
          (output.edit.run.incidencePaths
            (outer.length + localWire.index.val))) ?_ ?_ localWire
      · intro signature beforeWire
        let sourceLocal : Var sourceLocals signature :=
          beforeWire.appendLeft (.rel [] :: after)
        let commonWire : Var (outer ++ (before ++ after)) signature :=
          Var.appendRight outer (beforeWire.appendLeft after)
        have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
        have sourceRoot : RegionPath.RootedTwo
            ((Region.ofItems source).incidencePaths
              (frame.sourceKeep commonWire).index.val) := by
          rw [Region.incidencePaths_ofItems]
          simpa [frame, sourceLocals, sourceLocal, commonWire,
            Arity.rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight, Var.index] using
                sourceLocalRoot
        have transferred :=
          (materialScope.retained commonWire).rooted sourceRoot
        simpa [frame, commonWire, Arity.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendRight, Var.index] using
            transferred
      · intro signature remaining
        cases remaining with
        | here =>
            let sourceLocal : Var sourceLocals (.rel []) :=
              Var.appendRight before .here
            have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
            have sourceRoot : RegionPath.RootedTwo
                ((Region.ofItems source).incidencePaths
                  frame.selected.index.val) := by
              rw [Region.incidencePaths_ofItems]
              simpa [frame, data, sourceLocals, sourceLocal,
                Arity.rootFrame,
                Arity.targetHead, Transform.Frame.replace,
                Transform.Frame.insertedHead, Var.appendRight, Var.index]
                using sourceLocalRoot
            have transferred := materialScope.selected.rooted sourceRoot
            simpa [frame, data, Arity.rootFrame,
              Arity.targetHead, Transform.Frame.replace,
              Transform.Frame.insertedHead, Var.appendRight, Var.index]
              using transferred
        | there afterWire =>
            let sourceLocal : Var sourceLocals signature :=
              Var.appendRight before (Var.there afterWire)
            let commonWire : Var (outer ++ (before ++ after)) signature :=
              Var.appendRight outer (Var.appendRight before afterWire)
            have sourceLocalRoot := sourceCanonical.1 sourceLocal.index
            have sourceRoot : RegionPath.RootedTwo
                ((Region.ofItems source).incidencePaths
                  (frame.sourceKeep commonWire).index.val) := by
              rw [Region.incidencePaths_ofItems]
              simpa [frame, sourceLocals, sourceLocal, commonWire,
                Arity.rootFrame,
                Transform.Frame.replace, Transform.Frame.keep,
                Transform.Frame.localKeep, Var.appendRight, Var.index]
                using sourceLocalRoot
            have transferred :=
              (materialScope.retained commonWire).rooted sourceRoot
            simpa [frame, commonWire, Arity.rootFrame,
              Transform.Frame.replace, Transform.Frame.keep,
              Transform.Frame.localKeep, Var.appendRight, Var.index]
              using transferred
    rw [output.run_eq] at targetRoot
    simpa [localWire] using targetRoot
  · intro signature wire
    exact (outerScope wire).nonempty
  · intro signature wire rooted
    exact (outerScope wire).rooted rooted


/-- Reinterpret the leading local wire as an inherited boundary wire.  The
item carrier is definitionally unchanged; canonicality only forgets the root
obligation for that one wire. -/
theorem arityExposedMaterial_canonical
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems : Region []).Canonical) :
    (Region.mk locals materialItems : Region [firstLocal]).Canonical := by
  simp only [Region.Canonical] at materialCanonical ⊢
  constructor
  · intro localIndex
    rw [show [firstLocal].length + localIndex.val =
      localIndex.succ.val by simp [Fin.val_succ, Nat.add_comm]]
    simpa only [List.length_nil, Nat.zero_add] using
      materialCanonical.1 localIndex.succ
  · exact materialCanonical.2

/-- Every material wire already has a genuine incidence before the leading
local is exposed, so support completion adds no pins to the exposed material. -/
theorem arityExposedMaterial_supportPins_eq_nil
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems : Region []).Canonical) :
    Erasure.Exposure.supportPins
        (Region.mk locals materialItems : Region [firstLocal])
        [firstLocal]
        (Erasure.Exposure.identityBoundary [firstLocal]) = .nil := by
  apply EqualityNormalization.supportPins_eq_nil
  intro position
  exact Fin.cases (by
    have rooted := materialCanonical.1 (0 : Fin (firstLocal :: locals).length)
    simpa only [Region.incidencePaths, Vars.get,
      Erasure.Exposure.identityBoundary] using rooted.nonempty)
    (fun impossible => Fin.elim0 impossible) position

def arityTargetOperation (firstLocal : Sig) :
    Transform.Operation [firstLocal] where
  Data := fun {_ _ targetWires} _ => Var targetWires (.rel [firstLocal])
  appendData := fun _ head locals => head.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun {_ _ targetWires} _ _ _ _ => Region.blank targetWires
  pin := fun {_ _ targetWires} _ _ => Region.blank targetWires

def arityTargetNaturality (firstLocal : Sig) :
    DataNaturality (arityTargetOperation firstLocal) where
  Coherent := fun _ _ data mappedData _ targetRename =>
    targetRename data = mappedData
  append := by
    intro common mappedCommon sourceWires mappedSourceWires targetWires
      mappedTargetWires frame mappedFrame data mappedData commonRename
      targetRename coherent locals
    simpa [arityTargetOperation, WireRenaming.appendRight] using
      congrArg (fun wire => wire.appendLeft locals) coherent
  appendAssoc := by intros; simp [arityTargetOperation, Region.adjoinMaterialWire]
  conjoinLeft := by intros; simp [arityTargetOperation, Region.conjoinLeftWire]
  conjoinRight := by intros; simp [arityTargetOperation, Region.conjoinRightWire]
  appendNil := by
    intro common sourceWires targetWires frame data
    exact WireEquiv.appendNil_symm_apply targetWires data
  site := by
    intro common mappedCommon sourceWires mappedSourceWires targetWires
      mappedTargetWires frame mappedFrame data mappedData commonRename
      targetRename coherent targetKeepCommutes ports siteData
    refine ⟨PUnit.unit, ⟨RegionIso.ofEq ?_⟩⟩
    change Region.blank mappedTargetWires = Region.blank mappedTargetWires
    rfl

def arityDataSelects
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [firstLocal] common sourceWires targetWires}
    (data : (arityTargetOperation firstLocal).Data frame)
    (head : Var targetWires (.rel [firstLocal])) : Prop :=
  head = data

theorem arityDataSelects_append
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [firstLocal] common sourceWires targetWires}
    (data : (arityTargetOperation firstLocal).Data frame)
    (head : Var targetWires (.rel [firstLocal]))
    (selects : arityDataSelects data head)
    (locals : List Sig) :
    arityDataSelects
      ((arityTargetOperation firstLocal).appendData frame data locals)
      (head.appendLeft locals) := by
  exact congrArg (fun wire => wire.appendLeft locals) selects

def arityDataAligned
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame [] common localSourceWires localTargetWires}
    {formalFrame : Transform.Frame [firstLocal] common formalSourceWires
      formalTargetWires}
    (localData : (Arity.operation [] firstLocal).Data localFrame)
    (formalData : (arityTargetOperation firstLocal).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires) : Prop :=
  ambient.toRenaming localData = formalData

theorem arityDataAligned_append
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame [] common localSourceWires localTargetWires}
    {formalFrame : Transform.Frame [firstLocal] common formalSourceWires
      formalTargetWires}
    (localData : (Arity.operation [] firstLocal).Data localFrame)
    (formalData : (arityTargetOperation firstLocal).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires)
    (aligned : arityDataAligned localData formalData ambient)
    (locals : List Sig) :
    arityDataAligned
      ((Arity.operation [] firstLocal).appendData localFrame localData locals)
      ((arityTargetOperation firstLocal).appendData formalFrame formalData locals)
      (ambient.append (WireEquiv.refl locals)) := by
  simpa only [arityDataAligned, Arity.operation, arityTargetOperation,
    WireEquiv.append_apply_left] using
      congrArg (fun wire => wire.appendLeft locals) aligned

/-- Exposing the leading local changes only the region's presentation. -/
noncomputable def arityExposedMaterialIso
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals)) :
    RegionIso (WireEquiv.refl [])
      (Region.mk (firstLocal :: locals) materialItems : Region [])
      (Region.adjoinAt [firstLocal] .nil
        (Region.mk locals materialItems : Region [firstLocal])) := by
  let targetRename := Region.adjoinMaterialWire [] [firstLocal] locals
  let ambient := (WireEquiv.refl []).append
    (WireEquiv.refl (firstLocal :: locals))
  have commutes : ∀ {signature}
      (wire : Var (firstLocal :: locals) signature),
      ambient (WireRenaming.id wire) = targetRename wire := by
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [show ambient = WireEquiv.refl (firstLocal :: locals) by
      simpa only [List.nil_append] using
        WireEquiv.append_refl [] (firstLocal :: locals)]
    exact (Region.adjoinMaterialWire_index_val
      (outer := []) (hostLocals := [firstLocal])
      (addedLocals := locals) wire).symm
  let itemsIso := ItemSeqIso.renameWires materialItems WireRenaming.id
    targetRename ambient commutes
  refine .mk (WireEquiv.refl (firstLocal :: locals)) ?_
  simpa only [Region.adjoinAt, Region.locals, Region.items,
    ItemSeq.renameWires, ItemSeq.renameWires_id, ItemSeq.nil_append,
    targetRename] using itemsIso

theorem arityExposedSubstitution_eq_id (firstLocal : Sig) :
    EqualityNormalization.formalSubstitution
      (Erasure.Exposure.identityBoundary [firstLocal]) =
        WireRenaming.id := by
  apply WireRenaming.ext
  intro signature wire
  cases wire with
  | here => rfl
  | there tail => exact Fin.elim0 tail.index

theorem aritySelectedTargetItem
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems : Region []).Canonical)
    {itemCommon itemSourceWires itemTargetWires : List Sig}
    {fullPattern : OpenDiagram []}
    {itemFrame : Transform.Frame [] itemCommon itemSourceWires itemTargetWires}
    {itemData : (Arity.operation [] firstLocal).Data itemFrame}
    (fullPatternEq : fullPattern = Erasure.Exposure.supportPattern
      (Region.mk (firstLocal :: locals) materialItems : Region [])
      materialCanonical)
    (application : Vars itemCommon [])
    (siteData : (Arity.operation [] firstLocal).SiteData itemFrame itemData
      application)
    {formalSourceWires formalTargetWires : List Sig}
    (formalFrame : Transform.Frame [firstLocal] itemCommon formalSourceWires
      formalTargetWires)
    (formalData : (arityTargetOperation firstLocal).Data formalFrame) :
    TargetItem
      (targetExternal := [firstLocal])
      (targetPattern := Erasure.Exposure.supportPattern
        (Region.mk locals materialItems : Region [firstLocal])
        (arityExposedMaterial_canonical materialItems materialCanonical))
      (targetOperation := arityTargetOperation firstLocal)
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := Arity.operation [] firstLocal)
        (pattern := fullPattern) (frame := itemFrame) application siteData)
      (Erasure.Exposure.identityBoundary [firstLocal]) formalFrame formalData
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
            ∀ (bridge : TargetFrameBridge formalFrame arityDataSelects
                  formalData)
              (alignment : TargetAmbientBridge itemFrame formalFrame
                arityDataAligned itemData formalData),
              Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                ((itemEdit itemData
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                    (pattern := fullPattern) (retain := itemFrame.sourceKeep)
                    (selected := itemFrame.selected) application)
                  (ItemSites.selectedAtom
                    (operation := Arity.operation [] firstLocal)
                    (pattern := fullPattern) (frame := itemFrame)
                    application siteData)).endpoint.renameWires
                      alignment.ambient.toRenaming)
                (.mk retained (formalSource.renameWires
                  (bridge.sourceToTarget.appendRight retained))))) := by
  subst fullPattern
  cases application
  let childMaterial : Region [firstLocal] := .mk locals materialItems
  let childCanonical := arityExposedMaterial_canonical materialItems
    materialCanonical
  let childPattern := Erasure.Exposure.supportPattern childMaterial
    childCanonical
  let retained := [firstLocal]
  let childApplication : Vars (itemCommon ++ retained) [firstLocal] :=
    .cons (Var.appendRight itemCommon Var.here) .nil
  let childFrame := formalFrame.append retained
  let childData := (arityTargetOperation firstLocal).appendData formalFrame
    formalData retained
  let selectedEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected) childApplication
  let pinEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected) firstLocal 1
      (fun _ => Var.appendRight itemCommon Var.here)
  let nilEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected)
  let formalEvidence :=
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      selectedEvidence
      (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        pinEvidence nilEvidence)
  let recorded := recordingOperation (arityTargetOperation firstLocal)
    [firstLocal]
  let selectedSites : ItemSites recorded childData selectedEvidence :=
    .selectedAtom (pattern := childPattern) childApplication
      ⟨PUnit.unit, childApplication⟩
  let pinSites : ItemSites recorded childData pinEvidence :=
    .identity (pattern := childPattern) firstLocal 1
      (fun _ => Var.appendRight itemCommon Var.here)
  let nilSites : ItemsSites recorded childData nilEvidence := .nil nilEvidence
  let formalSites : ItemsSites recorded childData formalEvidence :=
    .cons selectedSites (.cons pinSites nilSites)
  refine ⟨retained, _, _, formalEvidence, formalSites, ?_, ?_⟩
  · rfl
  · let formalResult :=
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        childPattern childApplication).conjoin
        ((Region.singleton (.identity firstLocal 1
          (fun _ => Var.appendRight itemCommon Var.here))).conjoin
          (Region.blank (itemCommon ++ retained)))
    let staged := Region.adjoinAt retained .nil formalResult
    refine ⟨staged, ?_, ?_, ⟨RegionIso.refl staged⟩, ?_⟩
    · let fullMaterial : Region [] :=
        .mk (firstLocal :: locals) materialItems
      let fullPattern := Erasure.Exposure.supportPattern fullMaterial
        materialCanonical
      let oldHosted := supportInstantiationHosted fullMaterial
        materialCanonical (Vars.nil : Vars itemCommon [])
      let childInst :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern childApplication
      have childSubstitution :
          EqualityNormalization.formalSubstitution childApplication =
            (⟨fun wire => Var.appendRight itemCommon wire⟩ :
              WireRenaming [firstLocal] (itemCommon ++ retained)) := by
        apply WireRenaming.ext
        intro signature wire
        cases wire with
        | here => rfl
        | there tail => exact Fin.elim0 tail.index
      let childHostedRaw := supportInstantiationHosted childMaterial
        childCanonical childApplication
      let childHosted : HostedStrict childInst
          (childMaterial.renameWires
            (⟨fun wire => Var.appendRight itemCommon wire⟩ :
              WireRenaming [firstLocal] (itemCommon ++ retained))) := by
        simpa only [childSubstitution] using childHostedRaw
      let pinRename : WireRenaming [firstLocal] (itemCommon ++ retained) :=
        ⟨fun wire => Var.appendRight itemCommon wire⟩
      let pinTarget : Region (itemCommon ++ retained) :=
        Region.singleton (.identity firstLocal 1
          (fun _ => Var.appendRight itemCommon Var.here))
      let pinHosted : HostedStrict (Region.blank (itemCommon ++ retained))
          pinTarget := HostedStrict.specialize
        (HostedStrict.unaryPin firstLocal) pinRename
        (by rfl) (by rfl)
      let blank := Region.blank (itemCommon ++ retained)
      let withPin := HostedStrict.conjoin
        (childMaterial.renameWires
          (⟨fun wire => Var.appendRight itemCommon wire⟩ :
            WireRenaming [firstLocal] (itemCommon ++ retained)))
        blank childInst pinTarget childHosted.symm pinHosted
      let childToPinned : HostedStrict
          (childMaterial.renameWires
            (⟨fun wire => Var.appendRight itemCommon wire⟩ :
              WireRenaming [firstLocal] (itemCommon ++ retained)))
          formalResult := by
        exact HostedStrict.iso
          (RegionIso.conjoinBlank _).symm
          (RegionIso.conjoinCongr (RegionIso.refl childInst)
            (RegionIso.conjoinBlank pinTarget).symm) withPin
      let lifted := HostedStrict.adjoinAt retained _ _ childToPinned
      let emptyRename : WireRenaming [] itemCommon :=
        ⟨fun wire => nomatch wire⟩
      have oldSubstitution :
          EqualityNormalization.formalSubstitution
              (Vars.nil : Vars itemCommon []) = emptyRename := by
        apply WireRenaming.ext
        intro signature wire
        exact nomatch wire
      rw [oldSubstitution] at oldHosted
      let exposedBase := arityExposedMaterialIso materialItems
      let exposedMapped := RegionIso.renameExisting exposedBase emptyRename
        emptyRename (WireEquiv.refl itemCommon) (fun wire => nomatch wire)
      let exposedTargetEq := Region.renameWires_adjoinAt .nil childMaterial
        emptyRename
      let exposedIso : RegionIso (WireEquiv.refl itemCommon)
          (fullMaterial.renameWires emptyRename)
          (Region.adjoinAt retained .nil
            (childMaterial.renameWires
              (emptyRename.appendRight retained))) :=
        exposedMapped.trans (RegionIso.ofEq exposedTargetEq)
      have renameEq : emptyRename.appendRight retained =
          (⟨fun wire => Var.appendRight itemCommon wire⟩ :
            WireRenaming [firstLocal] (itemCommon ++ retained)) := by
        apply WireRenaming.ext
        intro signature wire
        cases wire with
        | here => rfl
        | there tail => exact Fin.elim0 tail.index
      rw [renameEq] at exposedIso
      let exposed := Region.adjoinAt retained .nil
        (childMaterial.renameWires pinRename)
      have exposedCanonical : exposed.Canonical := by
        apply exposedIso.canonical_iff.mp
        exact (Region.Canonical.renameWires_iff fullMaterial
          emptyRename).mpr materialCanonical
      have stagedToExposed : HostedScope staged exposed := by
        intro target rename
        apply ScopePreservation.of_incidence_empty
        · exact (Region.Canonical.renameWires_iff exposed rename).mpr
            exposedCanonical
        · intro signature wire
          rw [show staged.renameWires rename =
              Region.adjoinAt retained .nil
                (formalResult.renameWires (rename.appendRight retained)) by
            exact Region.renameWires_adjoinAt_nil formalResult rename]
          rw [← Var.index_appendLeft wire retained,
            Region.incidencePaths_adjoinAt_nil]
          rw [Region.renameWires_conjoin, Region.renameWires_conjoin,
            Region.incidencePaths_conjoin, Region.incidencePaths_conjoin]
          have pinPortNe :
              ((rename.appendRight retained)
                (Var.appendRight itemCommon Var.here :
                  Var (itemCommon ++ retained) firstLocal)).index.val ≠
                wire.index.val := by
            simp only [retained, WireRenaming.appendRight,
              Var.appendMap_right, Var.index_appendRight]
            exact Nat.ne_of_gt wire.index.isLt
          have childEmpty :
              (childInst.renameWires (rename.appendRight retained)).incidencePaths
                (wire.appendLeft retained).index.val = [] := by
            rw [EqualityNormalization.instantiate_renameWires]
            apply List.eq_nil_of_length_eq_zero
            rw [EqualityNormalization.instantiate_incidencePaths_length]
            simp only [childApplication, Vars.map, Vars.countIndex,
              Var.index_appendLeft]
            simp [pinPortNe]
          have pinEmpty :
              (pinTarget.renameWires (rename.appendRight retained)).incidencePaths
                (wire.appendLeft retained).index.val = [] := by
            simp only [pinTarget, Region.singleton, Region.ofItems,
              Region.renameWires,
              Region.incidencePaths, ItemSeq.renameWires,
              Item.renameWires, ItemSeq.incidencePaths,
              Item.incidencePaths, List.replicate_succ,
              List.replicate_zero, List.map_cons, List.map_nil,
              Vars.map, Vars.countIndex, Var.index_appendLeft]
            simp [Nat.ne_of_lt wire.index.isLt,
              Ne.symm (Nat.ne_of_lt wire.index.isLt),
              WireRenaming.appendRight,
              retained]
          have blankEmpty :
              ((Region.blank (itemCommon ++ retained)).renameWires
                (rename.appendRight retained)).incidencePaths
                  (wire.appendLeft retained).index.val = [] := by
            rfl
          rw [childEmpty, pinEmpty, blankEmpty]
          simp
        · intro signature wire
          rw [show exposed.renameWires rename =
              Region.adjoinAt retained .nil
                ((childMaterial.renameWires pinRename).renameWires
                  (rename.appendRight retained)) by
            exact Region.renameWires_adjoinAt_nil
              (childMaterial.renameWires pinRename) rename]
          rw [← Var.index_appendLeft wire retained,
            Region.incidencePaths_adjoinAt_nil]
          rw [Region.renameWires_comp]
          simp only [childMaterial, Region.renameWires,
            Region.incidencePaths]
          apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
          · simpa only [List.length_append, Var.index_appendLeft,
              Nat.add_assoc] using
              Nat.lt_of_lt_of_le wire.index.isLt
                (Nat.le_add_right target.length (retained ++ locals).length)
          · intro sourceSignature sourceWire
            apply Var.appendCases (left := [firstLocal]) (right := locals)
              (motive := fun sourceWire =>
                (((WireRenaming.comp (rename.appendRight retained)
                  pinRename).appendRight locals) sourceWire).index.val ≠
                    (wire.appendLeft retained).index.val)
            · intro inheritedSignature inherited
              cases inherited with
              | here =>
                  simp [pinRename, retained, WireRenaming.comp,
                    WireRenaming.appendRight]
                  omega
              | there tail => exact nomatch tail
            · intro localSignature localWire
              simp [pinRename, retained, WireRenaming.comp,
                WireRenaming.appendRight]
              omega
      let exposedToStaged := HostedStrict.trans
        (HostedStrict.ofIso exposedIso) lifted
        (fun outer hostLocals rename hostItems =>
          HostedScope.adjoinHost stagedToExposed outer hostLocals rename
            hostItems)
      have stagedToFull : HostedScope staged
          (fullMaterial.renameWires emptyRename) := by
        intro target rename
        exact (stagedToExposed rename).trans
          (HostedScope.ofIso exposedIso.symm rename)
      exact HostedStrict.trans oldHosted exposedToStaged
        (fun outer hostLocals rename hostItems =>
          HostedScope.adjoinHost stagedToFull outer hostLocals rename
            hostItems)
    · have stagedCanonical : staged.Canonical := by
        have childInstCanonical :
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              childPattern childApplication).Canonical :=
          VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
            childPattern childApplication
        have pinCanonical :
            (Region.singleton (.identity firstLocal 1
              (fun _ => Var.appendRight itemCommon Var.here)) :
                Region (itemCommon ++ retained)).Canonical := by
          simp only [Region.singleton, Region.ofItems, Region.Canonical,
            List.length_nil]
          constructor
          · intro localIndex
            exact Fin.elim0 localIndex
          · apply (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
            simp [ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
        have blankCanonical : (Region.blank
            (itemCommon ++ retained)).Canonical := by
          simp [Region.blank, Region.Canonical, ItemSeq.ChildrenCanonical]
        have formalResultCanonical : formalResult.Canonical := by
          exact EqualityNormalization.canonical_conjoin childInstCanonical
            (EqualityNormalization.canonical_conjoin pinCanonical
              blankCanonical)
        apply Region.Canonical.adjoinAt_of_material_roots retained .nil
          formalResult True.intro formalResultCanonical
        intro hostIndex
        have hostIndexEq : hostIndex = 0 := by
          apply Fin.eq_of_val_eq
          simpa [retained] using Fin.eq_zero hostIndex
        subst hostIndex
        let rootWire : Var (itemCommon ++ retained) firstLocal :=
          Var.appendRight itemCommon Var.here
        simp only [Fin.val_zero, Nat.add_zero]
        have rootIndex : rootWire.index.val = itemCommon.length := by
          simp [rootWire, retained]
        dsimp only [formalResult]
        rw [show itemCommon.length = rootWire.index.val from rootIndex.symm,
          Region.incidencePaths_conjoin _ _ rootWire,
          Region.incidencePaths_conjoin _ _ rootWire]
        have pinLength :
            ((Region.singleton (.identity firstLocal 1
              (fun _ => Var.appendRight itemCommon Var.here)) :
                Region (itemCommon ++ retained)).incidencePaths
                  rootWire.index.val).length = 1 := by
          simp [Region.singleton, Region.ofItems, Region.incidencePaths,
            ItemSeq.renameWires, Item.renameWires,
            ItemSeq.incidencePaths, Item.incidencePaths, List.ofFn_succ,
            List.ofFn_zero, rootWire, retained, Var.index_appendLeft]
        have blankLength :
            ((Region.blank (itemCommon ++ retained)).incidencePaths
              rootWire.index.val).length = 0 := by
          rfl
        constructor
        · simp only [List.length_append, List.length_map]
          rw [EqualityNormalization.instantiate_incidencePaths_length]
          rw [pinLength, blankLength]
          simp [childApplication, rootWire, retained, Vars.countIndex]
        · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
          apply List.mem_append_left
          apply EqualityNormalization.instantiate_incidence_mem_nil_of_nonempty
          apply (EqualityNormalization.instantiate_incidence_nonempty_iff
            childPattern childApplication rootWire).mpr
          simp [childApplication, rootWire, retained, Vars.countIndex]
      have sourceEmpty : ∀ {signature} (wire : Var itemCommon signature),
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern
              (Region.mk (firstLocal :: locals) materialItems : Region [])
              materialCanonical)
            (Vars.nil : Vars itemCommon [])).incidencePaths
              wire.index.val = [] := by
        intro signature wire
        apply List.eq_nil_of_length_eq_zero
        rw [EqualityNormalization.instantiate_incidencePaths_length]
        rfl
      have stagedEmpty : ∀ {signature} (wire : Var itemCommon signature),
          staged.incidencePaths wire.index.val = [] := by
        intro signature wire
        have childEmpty :
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              childPattern childApplication).incidencePaths
            (wire.appendLeft retained).index.val = [] := by
          apply List.eq_nil_of_length_eq_zero
          rw [EqualityNormalization.instantiate_incidencePaths_length]
          simp [childApplication, retained, Vars.countIndex,
            Nat.ne_of_lt wire.index.isLt,
            Ne.symm (Nat.ne_of_lt wire.index.isLt)]
        change (Region.adjoinAt retained .nil formalResult).incidencePaths
          wire.index.val = []
        rw [← Var.index_appendLeft wire retained,
          Region.incidencePaths_adjoinAt_nil]
        dsimp only [formalResult]
        rw [Region.incidencePaths_conjoin, Region.incidencePaths_conjoin,
          childEmpty]
        simp [Region.blank, Region.singleton, Region.ofItems,
          Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
          ItemSeq.incidencePaths, Item.incidencePaths, List.ofFn_succ,
          List.ofFn_zero, retained,
          Nat.ne_of_lt wire.index.isLt,
          Ne.symm (Nat.ne_of_lt wire.index.isLt)]
      exact ScopePreservation.of_incidence_empty stagedCanonical sourceEmpty
        stagedEmpty
    · intro bridge alignment
      cases siteData
      have dataEq := alignment.data_aligned
      unfold arityDataAligned at dataEq
      have headEq := bridge.data_selects
      unfold arityDataSelects at headEq
      refine ⟨RegionIso.ofEq ?_⟩
      simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
        Arity.operation, arityTargetOperation, retained, formalSites,
        selectedSites, pinSites, nilSites, formalEvidence,
        selectedEvidence, pinEvidence, nilEvidence, childApplication,
        childFrame, Transform.Frame.append, argumentItemsEdit,
        argumentItemEdit, Erasure.Exposure.identityBoundary,
        normalizationOperation, Region.renameWires, ItemSeq.renameWires,
        Item.renameWires, WireRenaming.appendRight, Vars.map]
      simp only [Var.appendMap_left, Var.appendMap_right]
      rw [dataEq, bridge.selected_commutes, headEq]
      simp [Arity.Vars.append, Vars.map, Var.appendMap_right]

/-- The local-wire constructor is the remaining Arity completeness obligation. -/
theorem supportArityDerives
    {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems : Region []).Canonical)
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel [] :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (Region.mk (firstLocal :: locals) materialItems : Region [])
          materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter [])
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter [])
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel [] :: structuralAfter)
        items)) :
    request.Result := by
let structuralRequest := request
let childMaterial : Region [firstLocal] := .mk locals materialItems
let childCanonical := arityExposedMaterial_canonical materialItems
  materialCanonical
let childPattern := Erasure.Exposure.supportPattern childMaterial
  childCanonical
let arityData := Arity.targetHead structuralOuter structuralBefore
  structuralAfter [] firstLocal
obtain ⟨aritySites⟩ := arityItemsSites_nonempty
  (pattern := Erasure.Exposure.supportPattern
    (Region.mk (firstLocal :: locals) materialItems : Region [])
    materialCanonical)
  (frame := Arity.rootFrame structuralOuter structuralBefore
    structuralAfter [] firstLocal) (data := arityData) evidence
have rootArityScope := arityRootScope structuralOuter structuralBefore
  structuralAfter firstLocal evidence aritySites
obtain ⟨retained, formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, semantic⟩ :=
  accumulateHostedTargetWith (targetArguments := [firstLocal])
    (targetExternal := [firstLocal])
    (targetInserted := [.rel [firstLocal]])
    (targetPattern := childPattern)
    (targetBaseOperation := arityTargetOperation firstLocal)
    evidence aritySites
    (Erasure.Exposure.identityBoundary [firstLocal])
    arityData ScopePreservation ScopePreservation.refl
    (fun locals before after scope =>
      adjoinAt_preserves_scope locals .nil before after scope)
    ScopePreservation.conjoin
    ScopePreservation.cut arityDataSelects arityDataSelects_append
    arityDataAligned arityDataAligned_append
    (arityTargetNaturality firstLocal)
    (aritySelectedTargetItem materialItems materialCanonical rfl)
obtain ⟨staged, resultHosted, resultScope, stagedPresentation,
    endpointSemantic⟩ := semantic
obtain ⟨stagedIso⟩ := stagedPresentation
let localRootFrame := Arity.rootFrame structuralOuter structuralBefore
  structuralAfter [] firstLocal
let formalRootFrame := Transform.Frame.replace structuralOuter
  structuralBefore structuralAfter [.rel [firstLocal]] [firstLocal]
let rootBridge : TargetFrameBridge formalRootFrame arityDataSelects
    arityData := {
  sourceToTarget := WireRenaming.id
  targetHead := arityData
  keep_commutes := by intro signature wire; rfl
  selected_commutes := rfl
  data_selects := rfl
}
let rootAlignment : TargetAmbientBridge localRootFrame formalRootFrame
    arityDataAligned arityData arityData := {
  ambient := WireEquiv.refl _
  keep_commutes := by intro signature wire; rfl
  data_aligned := rfl
}
obtain ⟨rootEndpointIso⟩ := endpointSemantic rootBridge rootAlignment
have commonWiresEq :
    (structuralOuter ++ (structuralBefore ++ structuralAfter)) ++ retained =
      structuralOuter ++ (structuralBefore ++ (structuralAfter ++ retained)) := by
  simp only [List.append_assoc]
let commonEquiv := WireEquiv.ofEq commonWiresEq
let commonRename := commonEquiv.toRenaming
have commonRename_index {signature}
    (wire : Var
      ((structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
        retained) signature) :
    (commonRename wire).index.val = wire.index.val := by
  exact WireEquiv.ofEq_index_val commonWiresEq wire
have sourceWiresEq :
    (structuralOuter ++ (structuralBefore ++ .rel [firstLocal] :: structuralAfter)) ++ retained =
      structuralOuter ++
        (structuralBefore ++ .rel [firstLocal] :: (structuralAfter ++ retained)) := by
  simp only [List.append_assoc, List.cons_append]
let sourceEquiv := WireEquiv.ofEq sourceWiresEq
let sourceRename := sourceEquiv.toRenaming
have sourceRename_index {signature}
    (wire : Var
      ((structuralOuter ++
          (structuralBefore ++ .rel [firstLocal] :: structuralAfter)) ++ retained)
        signature) :
    (sourceRename wire).index.val = wire.index.val := by
  exact WireEquiv.ofEq_index_val sourceWiresEq wire
let recursiveFrame := Transform.Frame.replace structuralOuter
  structuralBefore (structuralAfter ++ retained)
  [.rel [firstLocal]] [firstLocal]
let recursiveData := Transform.Frame.insertedHead structuralOuter
  structuralBefore (structuralAfter ++ retained) (.rel [firstLocal])
have keepCommutes : ∀ {signature}
    (wire : Var
      ((structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
        retained) signature),
    sourceRename
        ((formalRootFrame.append retained).sourceKeep wire) =
      recursiveFrame.sourceKeep (commonRename wire) := by
  intro signature wire
  refine Var.appendCases
    (left := structuralOuter ++ (structuralBefore ++ structuralAfter))
    (right := retained)
    (motive := fun wire =>
      sourceRename
          ((formalRootFrame.append retained).sourceKeep wire) =
        recursiveFrame.sourceKeep (commonRename wire)) ?_ ?_ wire
  · intro inheritedSignature inherited
    refine Var.appendCases (left := structuralOuter)
      (right := structuralBefore ++ structuralAfter)
      (motive := fun inherited =>
        sourceRename
            ((formalRootFrame.append retained).sourceKeep
                (inherited.appendLeft retained)) =
          recursiveFrame.sourceKeep
            (commonRename (inherited.appendLeft retained))) ?_ ?_ inherited
    · intro outerSignature outerWire
      have commonStep :
          commonRename
              ((outerWire.appendLeft
                (structuralBefore ++ structuralAfter)).appendLeft
                  retained) =
            outerWire.appendLeft
              (structuralBefore ++ (structuralAfter ++ retained)) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [commonRename_index]
        simp
      rw [commonStep]
      apply Var.eq_of_index_eq
      apply Fin.ext
      rw [sourceRename_index]
      simp [recursiveFrame, formalRootFrame,
        Transform.Frame.replace, Transform.Frame.append,
        Transform.Frame.keep, Transform.Frame.localKeep,
        WireRenaming.appendRight]
    · intro contextSignature contextWire
      refine Var.appendCases (left := structuralBefore)
        (right := structuralAfter)
        (motive := fun contextWire =>
          sourceRename
              ((formalRootFrame.append retained).sourceKeep
                  ((Var.appendRight structuralOuter contextWire).appendLeft
                    retained)) =
            recursiveFrame.sourceKeep
              (commonRename
                ((Var.appendRight structuralOuter contextWire).appendLeft
                  retained))) ?_ ?_ contextWire
      · intro beforeSignature beforeWire
        have commonStep :
            commonRename
                ((Var.appendRight structuralOuter
                  (beforeWire.appendLeft structuralAfter)).appendLeft
                    retained) =
              Var.appendRight structuralOuter
                (beforeWire.appendLeft (structuralAfter ++ retained)) := by
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [commonRename_index]
          simp
        rw [commonStep]
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [sourceRename_index]
        simp [recursiveFrame, formalRootFrame,
          Transform.Frame.replace, Transform.Frame.append,
          Transform.Frame.keep, Transform.Frame.localKeep,
          WireRenaming.appendRight]
      · intro afterSignature afterWire
        have commonStep :
            commonRename
                ((Var.appendRight structuralOuter
                  (Var.appendRight structuralBefore afterWire)).appendLeft
                    retained) =
              Var.appendRight structuralOuter
                (Var.appendRight structuralBefore
                  (afterWire.appendLeft retained)) := by
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [commonRename_index]
          simp
        rw [commonStep]
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [sourceRename_index]
        simp [recursiveFrame, formalRootFrame,
          Transform.Frame.replace, Transform.Frame.append,
          Transform.Frame.keep, Transform.Frame.localKeep,
          WireRenaming.appendRight, Var.appendRight,
          Var.index]
  · intro localSignature localWire
    have commonStep :
        commonRename
            (Var.appendRight
              (structuralOuter ++
                (structuralBefore ++ structuralAfter)) localWire) =
          Var.appendRight structuralOuter
            (Var.appendRight structuralBefore
              (Var.appendRight structuralAfter localWire)) := by
      apply Var.eq_of_index_eq
      apply Fin.ext
      rw [commonRename_index]
      simp
      omega
    rw [commonStep]
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [sourceRename_index]
    simp [recursiveFrame, formalRootFrame,
      Transform.Frame.replace, Transform.Frame.append,
      Transform.Frame.keep, Transform.Frame.localKeep,
      WireRenaming.appendRight, Var.appendRight, Var.index]
    omega
have targetKeepCommutes : ∀ {signature}
    (wire : Var
      ((structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
        retained) signature),
    sourceRename
        ((formalRootFrame.append retained).targetKeep wire) =
      recursiveFrame.targetKeep (commonRename wire) := by
  intro signature wire
  exact keepCommutes wire
have selectedCommutes :
    sourceRename
        (formalRootFrame.append retained).selected =
      recursiveFrame.selected := by
  apply Var.eq_of_index_eq
  apply Fin.ext
  rw [sourceRename_index]
  simp [recursiveFrame, formalRootFrame,
    Transform.Frame.replace, Transform.Frame.append,
    Transform.Frame.insertedHead, Var.index]
have dataCoherent : (arityTargetNaturality firstLocal).Coherent
    (formalRootFrame.append retained)
    recursiveFrame
    ((arityTargetOperation firstLocal).appendData
      formalRootFrame arityData retained)
    recursiveData commonRename sourceRename := by
  exact selectedCommutes
obtain ⟨recursiveSource, recursiveResult, recursiveEvidence,
    recursiveSites, recursiveSourceEq, recursiveArgumentEq,
    ⟨recursiveResultIso⟩, ⟨recursiveEndpointIso⟩⟩ :=
  targetItemsReindex (baseOperation := arityTargetOperation firstLocal)
    (external := [firstLocal]) (mappedFrame := recursiveFrame)
    (mappedData := recursiveData) formalEvidence formalSites
    (Erasure.Exposure.identityBoundary [firstLocal])
    commonRename sourceRename sourceRename
    keepCommutes targetKeepCommutes selectedCommutes
    (arityTargetNaturality firstLocal) dataCoherent
let oldLocals := structuralBefore ++ structuralAfter
let newLocals := structuralBefore ++ (structuralAfter ++ retained)
let fullInstantiated := Region.adjoinAt oldLocals .nil result
let recursiveInstantiated := Region.adjoinAt newLocals .nil recursiveResult
let recursivePending : Region structuralOuter :=
  .mk (structuralBefore ++ .rel [firstLocal] ::
    (structuralAfter ++ retained))
    recursiveSource
let stagedAdjoined := Region.adjoinAt oldLocals .nil staged
let stagedPresentationRaw :=
  (RegionIso.adjoinAt oldLocals .nil stagedIso).trans
    ((RegionIso.adjoinAtAssoc oldLocals .nil retained .nil formalResult).symm)
let recursiveResultPresentation :=
  RegionIso.adjoinAt newLocals .nil recursiveResultIso
let flatResult := Region.adjoinAt (oldLocals ++ retained)
  (Region.extendHostItems oldLocals .nil (.mk retained .nil))
  (formalResult.renameWires
    (Region.adjoinMaterialWire structuralOuter oldLocals retained))
let flatPresentation : RegionIso (WireEquiv.refl structuralOuter)
    flatResult
    (Region.adjoinAt newLocals .nil
      (formalResult.renameWires commonRename)) := by
  let formalLocals := formalResult.locals
  let formalItems := formalResult.items
  cases formalResult
  let sourcePrefix := Region.adjoinMaterialWire structuralOuter
    (oldLocals ++ retained) formalLocals
  let sourceMaterial := WireRenaming.comp sourcePrefix
    ((Region.adjoinMaterialWire structuralOuter oldLocals retained).appendRight
      formalLocals)
  let targetMaterial := Region.adjoinMaterialWire structuralOuter
    newLocals formalLocals
  let targetMap := WireRenaming.comp targetMaterial
    (commonRename.appendRight formalLocals)
  have localEq : (oldLocals ++ retained) ++ formalLocals =
      newLocals ++ formalLocals := by
    simp [oldLocals, newLocals, List.append_assoc]
  let localsIso := WireEquiv.ofEq localEq
  let ambient := (WireEquiv.refl structuralOuter).append localsIso
  have commutes : ∀ {signature}
      (wire : Var
        ((structuralOuter ++ (structuralBefore ++ structuralAfter) ++
          retained) ++ formalLocals) signature),
      ambient (sourceMaterial wire) = targetMap wire := by
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    have ambientIndex : (ambient (sourceMaterial wire)).index.val =
        (sourceMaterial wire).index.val := by
      apply Var.appendCases (left := structuralOuter)
        (right := (oldLocals ++ retained) ++ formalLocals)
        (motive := fun mapped =>
          (ambient mapped).index.val = mapped.index.val)
      · intro inheritedSignature inherited
        simpa only [Var.index_appendLeft] using
          WireEquiv.refl_append_left_index_val localsIso inherited
      · intro localSignature localWire
        simp only [ambient, localsIso, WireEquiv.append_apply_right,
          Var.index_appendRight, WireEquiv.ofEq_index_val]
    rw [ambientIndex]
    apply Var.appendCases
      (left := (structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
        retained) (right := formalLocals)
      (motive := fun wire =>
        (sourceMaterial wire).index.val = (targetMap wire).index.val)
    · intro inheritedSignature inherited
      simp [sourceMaterial, sourcePrefix, targetMap, targetMaterial,
        WireRenaming.comp, WireRenaming.appendRight,
        Region.adjoinMaterialWire_index_val, commonRename_index]
    · intro localSignature localWire
      simp [sourceMaterial, sourcePrefix, targetMap, targetMaterial,
        WireRenaming.comp, WireRenaming.appendRight,
        Region.adjoinMaterialWire_index_val, Var.index_appendRight,
        oldLocals, newLocals, List.append_assoc]
  let itemsIso := ItemSeqIso.renameWires formalItems
    sourceMaterial targetMap ambient commutes
  simpa only [flatResult, Region.adjoinAt, Region.renameWires,
    Region.extendHostItems, Region.locals, Region.items,
    ItemSeq.renameWires, ItemSeq.nil_append,
    ItemSeq.renameWires_comp, sourcePrefix, sourceMaterial,
    targetMaterial, targetMap, ambient] using
      (RegionIso.mk localsIso itemsIso)
let stagedPresentation : RegionIso (WireEquiv.refl structuralOuter)
    stagedAdjoined recursiveInstantiated := by
  simpa only [oldLocals, newLocals, stagedAdjoined,
    recursiveInstantiated, commonRename, commonEquiv,
    Region.extendHostItems, ItemSeq.nil_append] using
      (stagedPresentationRaw.trans flatPresentation).trans
        recursiveResultPresentation
have resultBridgeScope : ScopePreservation fullInstantiated
    recursiveInstantiated :=
  (adjoinAt_preserves_scope oldLocals .nil result staged
    resultScope).trans (ScopePreservation.ofIso stagedPresentation)
have recursiveInstantiatedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context fullInstantiated
  recursiveInstantiated structuralRequest.instantiatedCanonical
  structuralRequest.instantiatedExternalTwoEnded resultBridgeScope
have polarityEq : structuralRequest.occurrence.context.polarity =
    structuralRequest.polarity := structuralRequest.continuation.1
have resultBridgeTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context fullInstantiated
    recursiveInstantiated structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    recursiveInstantiatedValidity.1 recursiveInstantiatedValidity.2 := by
  have stagedValidity := filledValidityOfScope
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context fullInstantiated stagedAdjoined
    structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    (adjoinAt_preserves_scope oldLocals .nil result staged resultScope)
  have raw : Telescope structuralRequest.polarity
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context fullInstantiated stagedAdjoined
      structuralRequest.instantiatedCanonical
      structuralRequest.instantiatedExternalTwoEnded stagedValidity.1
      stagedValidity.2 := by
    have renamedResultCanonical :
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt oldLocals .nil
            (result.renameWires WireRenaming.id))).Canonical := by
      simpa only [fullInstantiated, Region.renameWires_id] using
        structuralRequest.instantiatedCanonical
    have renamedResultExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt oldLocals .nil
            (result.renameWires WireRenaming.id))) := by
      intro signature wire
      simpa only [fullInstantiated, Region.renameWires_id] using
        structuralRequest.instantiatedExternalTwoEnded wire
    have renamedStagedCanonical :
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt oldLocals .nil
            (staged.renameWires WireRenaming.id))).Canonical := by
      simpa only [stagedAdjoined, Region.renameWires_id] using
        stagedValidity.1
    have renamedStagedExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt oldLocals .nil
            (staged.renameWires WireRenaming.id))) := by
      intro signature wire
      simpa only [stagedAdjoined, Region.renameWires_id] using
        stagedValidity.2 wire
    simpa only [fullInstantiated, stagedAdjoined, oldLocals,
      Region.renameWires_id] using
      telescopeOfHosted resultHosted WireRenaming.id .nil
        structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context
        renamedResultCanonical renamedResultExternal
        renamedStagedCanonical renamedStagedExternal polarityEq
  exact telescopeIso (RegionIso.refl fullInstantiated)
    stagedPresentation raw
let preparedLocals := structuralBefore ++ .rel [firstLocal] :: structuralAfter
let rawPrepared : Region structuralOuter :=
  Region.adjoinAt preparedLocals .nil
    (itemsEdit (operation := Arity.operation [] firstLocal) arityData
      evidence aritySites).endpoint
have rawPreparedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context
  (.mk (structuralBefore ++ .rel [] :: structuralAfter) items) rawPrepared
  structuralRequest.pendingCanonical
  structuralRequest.pendingExternalTwoEnded rootArityScope
let endpointNested : RegionIso (WireEquiv.refl structuralOuter)
    rawPrepared
    (Region.adjoinAt preparedLocals .nil (.mk retained formalSource)) := by
  have appendedId :
      (WireRenaming.id : WireRenaming
        (structuralOuter ++ preparedLocals)
        (structuralOuter ++ preparedLocals)).appendRight retained =
        WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    exact WireRenaming.appendRight_id_apply retained wire
  have normalizedEndpoint : RegionIso
      (WireEquiv.refl (structuralOuter ++ preparedLocals))
      (itemsEdit (operation := Arity.operation [] firstLocal) arityData
        evidence aritySites).endpoint
      (.mk retained formalSource) := by
    change RegionIso (WireEquiv.refl (structuralOuter ++ preparedLocals))
      (Region.renameWires
        (WireEquiv.refl
          (structuralOuter ++ preparedLocals)).toRenaming
        (itemsEdit (operation := Arity.operation [] firstLocal) arityData
          evidence aritySites).endpoint)
      (.mk retained
        (formalSource.renameWires
          ((WireRenaming.id : WireRenaming
            (structuralOuter ++ preparedLocals)
            (structuralOuter ++ preparedLocals)).appendRight retained)))
        at rootEndpointIso
    rw [show (WireEquiv.refl
        (structuralOuter ++ preparedLocals)).toRenaming =
          WireRenaming.id from rfl,
      Region.renameWires_id, appendedId, ItemSeq.renameWires_id]
      at rootEndpointIso
    exact rootEndpointIso
  exact RegionIso.adjoinAt preparedLocals .nil normalizedEndpoint
let nestedPresentation : RegionIso (WireEquiv.refl structuralOuter)
    (Region.adjoinAt preparedLocals .nil (.mk retained formalSource))
    (Region.adjoinAt preparedLocals .nil
      (Region.adjoinAt retained .nil (Region.ofItems formalSource))) :=
  RegionIso.adjoinAt preparedLocals .nil
    (RegionIso.adjoinAtOfItems retained formalSource).symm
let flatPending := Region.adjoinAt (preparedLocals ++ retained)
  (Region.extendHostItems preparedLocals .nil (.mk retained .nil))
  ((Region.ofItems formalSource).renameWires
    (Region.adjoinMaterialWire structuralOuter preparedLocals retained))
let nestedToFlat : RegionIso (WireEquiv.refl structuralOuter)
    (Region.adjoinAt preparedLocals .nil
      (Region.adjoinAt retained .nil (Region.ofItems formalSource)))
    flatPending := by
  exact (RegionIso.adjoinAtAssoc preparedLocals .nil retained .nil
    (Region.ofItems formalSource)).symm
let rawToFlat := endpointNested.trans
  (nestedPresentation.trans nestedToFlat)
have preparedLocalsEq : preparedLocals ++ retained =
    structuralBefore ++ .rel [firstLocal] ::
      (structuralAfter ++ retained) := by
  simp [preparedLocals, List.append_assoc]
let preparedLocalsIso := WireEquiv.ofEq preparedLocalsEq
let pendingSourceMap := Region.adjoinMaterialWire structuralOuter
  preparedLocals retained
let appendNil : WireRenaming
    ((structuralOuter ++ preparedLocals) ++ retained)
    (((structuralOuter ++ preparedLocals) ++ retained) ++ []) :=
  ⟨fun wire => wire.appendLeft []⟩
let flatMap := WireRenaming.comp
  (Region.adjoinMaterialWire structuralOuter
    (preparedLocals ++ retained) [])
  (WireRenaming.comp (pendingSourceMap.appendRight []) appendNil)
let flatLocalsIso := (WireEquiv.appendNil
  (preparedLocals ++ retained)).trans preparedLocalsIso
let flatAmbient := (WireEquiv.refl structuralOuter).append flatLocalsIso
have flatCommutes : ∀ {signature}
    (wire : Var
      ((structuralOuter ++ preparedLocals) ++ retained) signature),
    flatAmbient (flatMap wire) = sourceRename wire := by
  intro signature wire
  apply Var.eq_of_index_eq
  apply Fin.ext
  have ambientIndex : (flatAmbient (flatMap wire)).index.val =
      (flatMap wire).index.val := by
    apply Var.appendCases (left := structuralOuter)
      (right := (preparedLocals ++ retained) ++ [])
      (motive := fun mapped =>
        (flatAmbient mapped).index.val = mapped.index.val)
    · intro inheritedSignature inherited
      simpa only [Var.index_appendLeft] using
        WireEquiv.refl_append_left_index_val flatLocalsIso inherited
    · intro localSignature localWire
      refine Var.appendCases (left := preparedLocals ++ retained)
        (right := [])
        (motive := fun localWire =>
          (flatAmbient
            (Var.appendRight structuralOuter localWire)).index.val =
          (Var.appendRight structuralOuter localWire).index.val) ?_ ?_
            localWire
      · intro inheritedSignature inherited
        simp only [flatAmbient, WireEquiv.append_apply_right,
          Var.index_appendRight]
        have mappedIndex :
            (flatLocalsIso (inherited.appendLeft [])).index.val =
              inherited.index.val := by
          change ((preparedLocalsIso
            (WireEquiv.appendNil (preparedLocals ++ retained)
              (inherited.appendLeft []))).index.val) =
                inherited.index.val
          rw [WireEquiv.appendNil_apply]
          exact WireEquiv.ofEq_index_val preparedLocalsEq inherited
        rw [mappedIndex]
        simp
      · intro impossibleSignature impossible
        exact Fin.elim0 impossible.index
  rw [ambientIndex, sourceRename_index]
  simp only [flatMap, WireRenaming.comp,
    Region.adjoinMaterialWire_index_val, appendNil,
    WireRenaming.appendRight, Var.appendMap_left,
    Var.index_appendLeft]
  exact Region.adjoinMaterialWire_index_val wire
let flatItemsIso := ItemSeqIso.renameWires formalSource flatMap
  sourceRename flatAmbient flatCommutes
rw [recursiveSourceEq] at flatItemsIso
let flatToRecursive : RegionIso (WireEquiv.refl structuralOuter)
    flatPending recursivePending := by
  simpa only [flatPending, recursivePending, Region.adjoinAt,
    Region.extendHostItems, Region.ofItems, Region.renameWires,
    Region.locals, Region.items, ItemSeq.renameWires,
    ItemSeq.nil_append, ItemSeq.renameWires_comp, appendNil,
    flatMap, flatAmbient] using
      (RegionIso.mk flatLocalsIso flatItemsIso)
let rawToRecursive := rawToFlat.trans flatToRecursive
let filledPendingIso := DiagramContext.fillIso
  structuralRequest.occurrence.context rawToRecursive
have recursivePendingCanonical :
    (structuralRequest.occurrence.context.fill
      recursivePending).Canonical :=
  filledPendingIso.canonical_iff.mp rawPreparedValidity.1
have pendingNonemptyIff : ∀ {signature}
    (wire : Var structuralRequest.occurrence.interface.external signature),
    (structuralRequest.occurrence.context.fill rawPrepared).incidencePaths
        wire.index.val ≠ [] ↔
      (structuralRequest.occurrence.context.fill
        recursivePending).incidencePaths wire.index.val ≠ [] := by
  intro signature wire
  have lengthEq := filledPendingIso.incidencePaths_length_eq wire
  constructor <;> intro nonempty
  · rw [← List.length_pos_iff] at nonempty ⊢
    rwa [← lengthEq]
  · rw [← List.length_pos_iff] at nonempty ⊢
    rwa [lengthEq]
let rawEndpoint := structuralRequest.occurrence.interface.withBody
  (structuralRequest.occurrence.context.fill rawPrepared)
  rawPreparedValidity.1 rawPreparedValidity.2
have recursivePendingExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill recursivePending) :=
  rawEndpoint.externalTwoEnded_of_nonempty_iff
    (structuralRequest.occurrence.context.fill recursivePending)
    pendingNonemptyIff
have recursiveSourceCanonical :
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity recursiveInstantiated
        recursivePending)).Canonical :=
  polaritySource_property structuralRequest.polarity
    (fun region =>
      (structuralRequest.occurrence.context.fill region).Canonical)
    recursiveInstantiated recursivePending
    recursiveInstantiatedValidity.1 recursivePendingCanonical
have recursiveSourceExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity recursiveInstantiated
        recursivePending)) :=
  polaritySource_property structuralRequest.polarity
    (fun region => OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill region))
    recursiveInstantiated recursivePending
    recursiveInstantiatedValidity.2 recursivePendingExternal
let recursiveRequest : Telescope.Request recursiveInstantiated
    recursivePending := {
  boundary := structuralRequest.boundary
  source := structuralRequest.occurrence.interface.withBody
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity recursiveInstantiated
        recursivePending)) recursiveSourceCanonical
          recursiveSourceExternal
  endpoint := recursivePending
  polarity := structuralRequest.polarity
  occurrence := exactOccurrence structuralRequest.occurrence.interface
    structuralRequest.occurrence.context
    (polaritySource structuralRequest.polarity recursiveInstantiated
      recursivePending) recursiveSourceCanonical recursiveSourceExternal
  instantiatedCanonical := recursiveInstantiatedValidity.1
  instantiatedExternalTwoEnded := recursiveInstantiatedValidity.2
  pendingCanonical := recursivePendingCanonical
  pendingExternalTwoEnded := recursivePendingExternal
  endpointCanonical := recursivePendingCanonical
  endpointExternalTwoEnded := recursivePendingExternal
  continuation := Telescope.refl structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context recursivePendingCanonical
    recursivePendingExternal polarityEq
}
have childCompiled := supportBoundaryWireDerives childMaterial childCanonical
  recursiveEvidence
  recursiveRequest
have bodyTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context recursiveInstantiated
    recursivePending recursiveInstantiatedValidity.1
    recursiveInstantiatedValidity.2 recursivePendingCanonical
    recursivePendingExternal := by
  exact Telescope.StrictDerives.toTelescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context recursiveInstantiatedValidity.1
    recursiveInstantiatedValidity.2 recursivePendingCanonical
    recursivePendingExternal polarityEq
    (by simpa only [recursiveRequest, Telescope.Request.Result] using
      childCompiled)
have preparationTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context fullInstantiated
    recursivePending structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    recursivePendingCanonical recursivePendingExternal :=
  telescopeTrans resultBridgeTelescope bodyTelescope
let preparation : structuralRequest.Preparation rawPrepared := {
  prepared := recursivePending
  preparedCanonical := recursivePendingCanonical
  preparedExternalTwoEnded := recursivePendingExternal
  rawPreparedCanonical := rawPreparedValidity.1
  rawPreparedExternalTwoEnded := rawPreparedValidity.2
  preparedIso := rawToRecursive.symm
  telescope := by
    simpa only [fullInstantiated] using preparationTelescope
}
exact itemsArity evidence aritySites structuralRequest preparation
end Structural

end VisualProof.Rule.Completeness.Comprehension
