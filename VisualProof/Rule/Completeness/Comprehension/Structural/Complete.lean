import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete
import VisualProof.Rule.Completeness.Comprehension.Structural.Blank
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

mutual
  theorem parallelRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (RegionSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := parallelItemsSites_nonempty childEvidence
          ((Content.Parallel.operation arguments).appendData frame data _)
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem parallelItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemsSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := parallelItemSites_nonempty itemEvidence data
        obtain ⟨tailSites⟩ := parallelItemsSites_nonempty tailEvidence data
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem parallelItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := parallelRegionSites_nonempty childEvidence data
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

/-- Exact nullary IdentityLeaf sites exist for every authoritative item
sequence result of the positional nullary identity pattern. The region and
item traversals are local implementation details of this production-consumed
result. -/
theorem identityZeroItemsSites_nonempty
    {signature : Sig}
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (positionalIdentityPattern signature 0)
        frame.sourceKeep frame.selected source result) :
    Nonempty (ItemsSites (Leaf.Identity.operation signature 0)
      PUnit.unit evidence) := by
  cases evidence with
  | nil => exact ⟨.nil _⟩
  | cons itemEvidence tailEvidence =>
      obtain ⟨itemSites⟩ := itemSites
        (signature := signature) (frame := frame) itemEvidence
      obtain ⟨tailSites⟩ := identityZeroItemsSites_nonempty
        (signature := signature) (frame := frame) tailEvidence
      exact ⟨.cons itemSites tailSites⟩
termination_by sizeOf source
where
  regionSites
      {signature : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (positionalIdentityPattern signature 0)
          frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Leaf.Identity.operation signature 0)
        PUnit.unit evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := identityZeroItemsSites_nonempty
          (signature := signature) (frame := frame.append _) childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  itemSites
      {signature : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (positionalIdentityPattern signature 0)
          frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Leaf.Identity.operation signature 0)
        PUnit.unit evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨.atom (pattern := positionalIdentityPattern signature 0)
          head ports⟩
    | selectedAtom application =>
        let identityPorts : Fin 0 → Var common signature :=
          fun position => Fin.elim0 position
        have applicationEq : application =
            Leaf.Identity.Vars.fromFn identityPorts := by
          cases application
          rfl
        exact ⟨ItemSites.selectedAtom
          (operation := Leaf.Identity.operation signature 0)
          (pattern := positionalIdentityPattern signature 0)
          (frame := frame) application ⟨identityPorts, applicationEq⟩⟩
    | identity itemSignature itemArity ports =>
        exact ⟨ItemSites.identity
          (operation := Leaf.Identity.operation signature 0)
          (pattern := positionalIdentityPattern signature 0)
          (frame := frame) itemSignature itemArity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := regionSites
          (signature := signature) (frame := frame) childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source

/-- Scope information preserved by the nullary cut-wrap edit.  The nullary
specialization is essential: a selected application has no retained ports, so
wrapping it cannot move a retained wire beneath a new cut. -/
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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

theorem filledValidityOfScope
    {boundary wires : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external wires)
    (before after : Region wires)
    (beforeCanonical : (context.fill before).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (scope : ScopePreservation before after) :
    (context.fill after).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill after) := by
  have afterCanonical : after.Canonical := scope.canonical
    (context.holeCanonical before beforeCanonical)
  have replacement := context.replaceCanonical before after beforeCanonical
    afterCanonical scope.incidenceNonempty
  let beforeEndpoint := interface.withBody (context.fill before)
    beforeCanonical beforeExternalTwoEnded
  exact ⟨replacement.1,
    beforeEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2⟩

theorem telescopeTrans
    {boundary wires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {first middle last : Region wires}
    {firstCanonical : (context.fill first).Canonical}
    {firstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill first)}
    {middleCanonical : (context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill middle)}
    {lastCanonical : (context.fill last).Canonical}
    {lastExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill last)}
    (head : Telescope polarity interface context first middle
      firstCanonical firstExternalTwoEnded middleCanonical
      middleExternalTwoEnded)
    (tail : Telescope polarity interface context middle last
      middleCanonical middleExternalTwoEnded lastCanonical
      lastExternalTwoEnded) :
    Telescope polarity interface context first last firstCanonical
      firstExternalTwoEnded lastCanonical lastExternalTwoEnded := by
  cases polarity with
  | positive => exact ⟨head.1, head.2.trans tail.2⟩
  | negative => exact ⟨head.1, tail.2.trans head.2⟩

theorem polaritySource_property
    (polarity : Polarity) (property : α → Prop) (before after : α)
    (beforeProperty : property before) (afterProperty : property after) :
    property (polaritySource polarity before after) := by
  cases polarity
  · exact beforeProperty
  · exact afterProperty

theorem telescopeIso
    {boundary wires : List Sig} {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {before before' after after' : Region wires}
    {beforeCanonical : (context.fill before).Canonical}
    {beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before)}
    {beforeCanonical' : (context.fill before').Canonical}
    {beforeExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before')}
    {afterCanonical : (context.fill after).Canonical}
    {afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)}
    {afterCanonical' : (context.fill after').Canonical}
    {afterExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after')}
    (beforeIso : RegionIso (WireEquiv.refl wires) before before')
    (afterIso : RegionIso (WireEquiv.refl wires) after after')
    (telescope : Telescope polarity interface context before after
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded) :
    Telescope polarity interface context before' after'
      beforeCanonical' beforeExternalTwoEnded' afterCanonical'
      afterExternalTwoEnded' := by
  let beforeOpenIso := OpenDiagram.withBody_iso beforeCanonical
    beforeCanonical' beforeExternalTwoEnded beforeExternalTwoEnded'
    (DiagramContext.fillIso context beforeIso)
  let afterOpenIso := OpenDiagram.withBody_iso afterCanonical
    afterCanonical' afterExternalTwoEnded afterExternalTwoEnded'
    (DiagramContext.fillIso context afterIso)
  cases polarity with
  | positive =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        beforeOpenIso telescope.2 afterOpenIso⟩
  | negative =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        afterOpenIso telescope.2 beforeOpenIso⟩

theorem telescopeOfHosted
    {common outer hostLocals boundary : List Sig}
    {before after : Region common}
    (transformation : HostedStrict before after)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (beforeCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))))
    (afterCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))).Canonical)
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))))
    (polarityEq : context.polarity = polarity) :
    Telescope polarity interface context
      (Region.adjoinAt hostLocals hostItems (before.renameWires rename))
      (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded := by
  let beforeHosted := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  let afterHosted := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  let occurrence := exactOccurrence interface context beforeHosted
    beforeCanonical beforeExternalTwoEnded
  have strict := transformation outer hostLocals rename hostItems occurrence
    afterCanonical afterExternalTwoEnded
  have equates := strict.toEquates
  cases polarity with
  | positive => exact ⟨polarityEq, equates.1⟩
  | negative => exact ⟨polarityEq, equates.2⟩

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
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := Content.Cut.operation [])
        (pattern := fullPattern) (frame := itemFrame) application siteData)
      (Vars.nil : Vars [] []) formalFrame formalData
      (fun retained formalSource formalResult _formalEvidence _formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                fullPattern application) staged ∧
              ScopePreservation
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  fullPattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
              ∀ (bridge : TargetFrameBridge formalFrame cutDataSelects
                    formalData)
                (alignment : TargetAmbientBridge itemFrame formalFrame
                  cutDataAligned itemData formalData),
                Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                  ((itemEdit itemData
                    (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
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
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected) childApplication
  let childTailEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      (pattern := childPattern) (retain := childFrame.sourceKeep)
      (selected := childFrame.selected)
  let childItemsEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      childItemEvidence childTailEvidence
  let childRegionEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
      childItemsEvidence
  let cutItemEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
      childRegionEvidence
  let cutTailEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      (pattern := childPattern) (retain := rootFrame.sourceKeep)
      (selected := rootFrame.selected)
  let formalEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern application))
    refine ⟨staged, ?_, ?_, ?_⟩
    · exact supportCutInstantiatedHosted body bodyCanonical application
    · have stagedCanonical : staged.Canonical := by
        exact (Region.singleton_cut_canonical_iff _).mpr
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
            childPattern application)
      have sourceEmpty : ∀ {signature} (wire : Var itemCommon signature),
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern application
      let rootResult :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern rootApplication
      let childResult :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
              (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
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

/-- Derive the exact support-completed material pattern selected by
comprehension evidence. The material syntax and its canonicality determine
the structural recursion; the caller contributes only the authoritative
instantiation evidence and the actual telescope request. -/
theorem supportPatternDerives
    {materialWires structuralOuter structuralBefore structuralAfter :
        List Sig}
    (material : Region materialWires)
    (materialCanonical : material.Canonical)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel materialWires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter materialWires)
        (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter materialWires)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
        items)) :
    request.Result := by
  let DerivesMaterial : {materialWires : List Sig} →
      Region materialWires → Prop := fun {materialWires} material =>
    ∀ (materialCanonical : material.Canonical)
      {structuralOuter structuralBefore structuralAfter : List Sig}
      {items : ItemSeq
        (structuralOuter ++
          (structuralBefore ++ .rel materialWires :: structuralAfter))}
      {result : Region
        (structuralOuter ++ (structuralBefore ++ structuralAfter))}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (Erasure.Exposure.supportPattern material materialCanonical)
          (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
            structuralBefore structuralAfter materialWires)
          (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
            structuralBefore structuralAfter materialWires)
          items result)
      (request : Telescope.Request
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
        (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
          items)),
      request.Result
  refine (Region.rec
    (motive_1 := fun _ region => DerivesMaterial region)
    (motive_2 := fun wires item =>
      wires = [] → DerivesMaterial (Region.singleton item))
    (motive_3 := fun wires materialItems =>
      wires = [] → DerivesMaterial (Region.ofItems materialItems))
    ?_ ?_ ?_ ?_ ?_ ?_ material) materialCanonical evidence request
  · intro outer locals materialItems materialItemsIH materialCanonical
      structuralOuter structuralBefore structuralAfter items result evidence
      structuralRequest
    cases outer with
    | nil =>
        cases locals with
        | nil =>
            have materialEq : Region.ofItems materialItems =
                Region.mk [] materialItems := by
              simp only [Region.ofItems]
              congr 1
              let appendNil : WireRenaming [] ([] ++ []) :=
                ⟨fun wire => wire.appendLeft []⟩
              change materialItems.renameWires appendNil = materialItems
              have renameEq : appendNil = WireRenaming.id := by
                apply WireRenaming.ext
                intro signature wire
                cases wire
              rw [renameEq]
              exact ItemSeq.renameWires_id materialItems
            have materialItemsCanonical :
                (Region.ofItems materialItems).Canonical := by
              rw [materialEq]
              exact materialCanonical
            have patternEq :
                Erasure.Exposure.supportPattern
                    (Region.mk [] materialItems) materialCanonical =
                  Erasure.Exposure.supportPattern
                    (Region.ofItems materialItems)
                    materialItemsCanonical := by
              apply EqualityNormalization.OpenDiagram.eq_of_data
              · rfl
              · rfl
              · change (HEq
                  (Erasure.Exposure.supportBody
                    (Region.mk [] materialItems))
                  (Erasure.Exposure.supportBody
                    (Region.ofItems materialItems)))
                have sourceBodyEq :
                    Erasure.Exposure.supportBody
                        (Region.mk [] materialItems) =
                      Region.mk [] materialItems :=
                  EqualityNormalization.supportBody_eq_of_supportPins_nil
                    (Region.mk [] materialItems) rfl
                have targetBodyEq :
                    Erasure.Exposure.supportBody
                        (Region.ofItems materialItems) =
                      Region.ofItems materialItems :=
                  EqualityNormalization.supportBody_eq_of_supportPins_nil
                    (Region.ofItems materialItems) rfl
                have bodyEq := sourceBodyEq.trans
                  (materialEq.symm.trans targetBodyEq.symm)
                exact heq_of_eq bodyEq
            rw [patternEq] at evidence
            exact materialItemsIH rfl materialItemsCanonical evidence
              structuralRequest
        | cons firstLocal locals => sorry
    | cons wire wires => sorry
  · intro wires arguments head ports wiresEq
    subst wires
    sorry
  · intro wires signature arity ports wiresEq
    subst wires
    have arityEq : arity = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro positive
      exact nomatch ports ⟨0, positive⟩
    subst arity
    intro materialCanonical structuralOuter structuralBefore structuralAfter
      items result evidence structuralRequest
    have materialEq :
        Region.singleton (.identity signature 0 ports) =
          positionalIdentityMaterial signature 0 := by
      apply congrArg Region.singleton
      apply congrArg (Item.identity signature 0)
      funext position
      exact Fin.elim0 position
    have patternEq :
        Erasure.Exposure.supportPattern
            (Region.singleton (.identity signature 0 ports))
            materialCanonical =
          positionalIdentityPattern signature 0 := by
      unfold positionalIdentityPattern
      apply EqualityNormalization.OpenDiagram.eq_of_data
      · rfl
      · rfl
      · exact heq_of_eq (congrArg Erasure.Exposure.supportBody materialEq)
    rw [patternEq] at evidence
    obtain ⟨identitySites⟩ := identityZeroItemsSites_nonempty
      (signature := signature)
      (frame := Leaf.Identity.rootFrame structuralOuter structuralBefore
        structuralAfter signature 0) evidence
    let output := itemsEdit
      (operation := Leaf.Identity.operation signature 0)
      PUnit.unit evidence identitySites
    have targetKeepEq :
        (Leaf.Identity.rootFrame structuralOuter structuralBefore
          structuralAfter signature 0).targetKeep = WireRenaming.id := by
      apply WireRenaming.ext
      intro wireSignature wire
      apply Var.appendCases (left := structuralOuter)
        (right := structuralBefore ++ structuralAfter)
        (motive := fun wire =>
          (Leaf.Identity.rootFrame structuralOuter structuralBefore
            structuralAfter signature 0).targetKeep wire =
              WireRenaming.id wire)
      · intro inheritedSignature inherited
        simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro localSignature localWire
        apply Var.appendCases (left := structuralBefore)
          (right := structuralAfter)
          (motive := fun localWire =>
            (Leaf.Identity.rootFrame structuralOuter structuralBefore
              structuralAfter signature 0).targetKeep
                (Var.appendRight structuralOuter localWire) =
              WireRenaming.id (Var.appendRight structuralOuter localWire))
        · intro beforeSignature beforeWire
          simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
        · intro afterSignature afterWire
          apply Var.eq_of_index_eq
          apply Fin.ext
          simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
            Var.index_appendRight, Var.appendRight]
    obtain ⟨preparationHosted, preparationScope⟩ :=
      leafItemsEndpoint evidence identitySites targetKeepEq
        (fun siteTargetKeepEq application site => by
          let recordedSite :
              (recordingOperation
                (Leaf.Identity.operation signature 0) []).SiteData
                  _ PUnit.unit application :=
            (site, Vars.nil)
          simpa only [recordingOperation] using
            (positionalIdentityLeafEndpoint signature 0
              siteTargetKeepEq application recordedSite))
    let instantiated := Region.adjoinAt
      (structuralBefore ++ structuralAfter) .nil result
    let rawPrepared := Region.adjoinAt
      (structuralBefore ++ structuralAfter) .nil output.endpoint
    have rawPreparedScope : ScopePreservation instantiated rawPrepared := by
      exact adjoinAt_preserves_scope
        (structuralBefore ++ structuralAfter) .nil result output.endpoint
        preparationScope
    have rawPreparedValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context instantiated rawPrepared
      structuralRequest.instantiatedCanonical
      structuralRequest.instantiatedExternalTwoEnded rawPreparedScope
    have polarityEq : structuralRequest.occurrence.context.polarity =
        structuralRequest.polarity := structuralRequest.continuation.1
    have renamedInstantiatedCanonical :
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
            (result.renameWires WireRenaming.id))).Canonical := by
      simpa only [Region.renameWires_id] using
        structuralRequest.instantiatedCanonical
    have renamedInstantiatedExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
            (result.renameWires WireRenaming.id))) := by
      intro wireSignature wire
      simpa only [Region.renameWires_id] using
        structuralRequest.instantiatedExternalTwoEnded wire
    have renamedPreparedCanonical :
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
            (output.endpoint.renameWires WireRenaming.id))).Canonical := by
      simpa only [Region.renameWires_id] using rawPreparedValidity.1
    have renamedPreparedExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
            (output.endpoint.renameWires WireRenaming.id))) := by
      intro wireSignature wire
      simpa only [Region.renameWires_id] using rawPreparedValidity.2 wire
    have preparationTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context instantiated rawPrepared
        structuralRequest.instantiatedCanonical
        structuralRequest.instantiatedExternalTwoEnded
        rawPreparedValidity.1 rawPreparedValidity.2 := by
      simpa only [instantiated, rawPrepared, Region.renameWires_id] using
        telescopeOfHosted preparationHosted WireRenaming.id .nil
          structuralRequest.polarity
          structuralRequest.occurrence.interface
          structuralRequest.occurrence.context
          renamedInstantiatedCanonical renamedInstantiatedExternal
          renamedPreparedCanonical renamedPreparedExternal polarityEq
    let preparation : structuralRequest.Preparation rawPrepared := {
      prepared := rawPrepared
      preparedCanonical := rawPreparedValidity.1
      preparedExternalTwoEnded := rawPreparedValidity.2
      rawPreparedCanonical := rawPreparedValidity.1
      rawPreparedExternalTwoEnded := rawPreparedValidity.2
      preparedIso := RegionIso.refl rawPrepared
      telescope := by
        simpa only [instantiated] using preparationTelescope
    }
    exact itemsIdentity (signature := signature) (arity := 0)
      (localBefore := structuralBefore) (localAfter := structuralAfter)
      evidence identitySites structuralRequest (by
        simpa only [rawPrepared, output, List.nil_append] using preparation)
  · intro wires body bodyIH wiresEq
    subst wires
    intro materialCanonical structuralOuter structuralBefore structuralAfter
      items result evidence structuralRequest
    have bodyCanonical : body.Canonical :=
      (Region.singleton_cut_canonical_iff body).mp materialCanonical
    let cutData := Content.Cut.targetHead structuralOuter structuralBefore
      structuralAfter []
    obtain ⟨cutSites⟩ := cutItemsSites_nonempty
      (pattern := Erasure.Exposure.supportPattern
        (Region.singleton (.cut body)) materialCanonical)
      (frame := Content.Cut.rootFrame structuralOuter structuralBefore
        structuralAfter []) (data := cutData) evidence
    have rootCutScope := cutRootScope structuralOuter structuralBefore
      structuralAfter evidence cutSites
    obtain ⟨retained, formalSource, formalResult, formalEvidence,
        formalSites, formalCoherence, semantic⟩ :=
      accumulateHostedTargetWith (targetInserted := [.rel []]) evidence
        cutSites (Vars.nil : Vars [] [])
        cutData ScopePreservation ScopePreservation.refl
        (fun locals before after scope =>
          adjoinAt_preserves_scope locals .nil before after scope)
        ScopePreservation.conjoin
        ScopePreservation.cut cutDataSelects cutDataSelects_append
        cutDataAligned cutDataAligned_append (cutDataNaturality [])
        (cutSelectedTargetItem body bodyCanonical rfl)
    obtain ⟨staged, resultHosted, resultScope, stagedPresentation,
        endpointSemantic⟩ := semantic
    obtain ⟨stagedIso⟩ := stagedPresentation
    let rootFrame := Content.Cut.rootFrame structuralOuter structuralBefore
      structuralAfter []
    let rootBridge : TargetFrameBridge rootFrame cutDataSelects cutData := {
      sourceToTarget := WireRenaming.id
      targetHead := cutData
      keep_commutes := by intro signature wire; rfl
      selected_commutes := rfl
      data_selects := rfl
    }
    let rootAlignment : TargetAmbientBridge rootFrame rootFrame
        cutDataAligned cutData cutData := {
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
        (structuralOuter ++ (structuralBefore ++ .rel [] :: structuralAfter)) ++ retained =
          structuralOuter ++
            (structuralBefore ++ .rel [] :: (structuralAfter ++ retained)) := by
      simp only [List.append_assoc, List.cons_append]
    let sourceEquiv := WireEquiv.ofEq sourceWiresEq
    let sourceRename := sourceEquiv.toRenaming
    have sourceRename_index {signature}
        (wire : Var
          ((structuralOuter ++
              (structuralBefore ++ .rel [] :: structuralAfter)) ++ retained)
            signature) :
        (sourceRename wire).index.val = wire.index.val := by
      exact WireEquiv.ofEq_index_val sourceWiresEq wire
    let recursiveFrame := Content.Cut.rootFrame structuralOuter
      structuralBefore (structuralAfter ++ retained) []
    let recursiveData := Content.Cut.targetHead structuralOuter
      structuralBefore (structuralAfter ++ retained) []
    have keepCommutes : ∀ {signature}
        (wire : Var
          ((structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
            retained) signature),
        sourceRename
            (((Content.Cut.rootFrame structuralOuter structuralBefore
              structuralAfter []).append retained).sourceKeep wire) =
          recursiveFrame.sourceKeep (commonRename wire) := by
      intro signature wire
      refine Var.appendCases
        (left := structuralOuter ++ (structuralBefore ++ structuralAfter))
        (right := retained)
        (motive := fun wire =>
          sourceRename
              (((Content.Cut.rootFrame structuralOuter structuralBefore
                structuralAfter []).append retained).sourceKeep wire) =
            recursiveFrame.sourceKeep (commonRename wire)) ?_ ?_ wire
      · intro inheritedSignature inherited
        refine Var.appendCases (left := structuralOuter)
          (right := structuralBefore ++ structuralAfter)
          (motive := fun inherited =>
            sourceRename
                (((Content.Cut.rootFrame structuralOuter structuralBefore
                  structuralAfter []).append retained).sourceKeep
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
          simp [recursiveFrame, Content.Cut.rootFrame,
            Transform.Frame.replace, Transform.Frame.append,
            Transform.Frame.keep, Transform.Frame.localKeep,
            WireRenaming.appendRight]
        · intro contextSignature contextWire
          refine Var.appendCases (left := structuralBefore)
            (right := structuralAfter)
            (motive := fun contextWire =>
              sourceRename
                  (((Content.Cut.rootFrame structuralOuter structuralBefore
                    structuralAfter []).append retained).sourceKeep
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
            simp [recursiveFrame, Content.Cut.rootFrame,
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
            simp [recursiveFrame, Content.Cut.rootFrame,
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
        simp [recursiveFrame, Content.Cut.rootFrame,
          Transform.Frame.replace, Transform.Frame.append,
          Transform.Frame.keep, Transform.Frame.localKeep,
          WireRenaming.appendRight, Var.appendRight, Var.index]
        omega
    have targetKeepCommutes : ∀ {signature}
        (wire : Var
          ((structuralOuter ++ (structuralBefore ++ structuralAfter)) ++
            retained) signature),
        sourceRename
            (((Content.Cut.rootFrame structuralOuter structuralBefore
              structuralAfter []).append retained).targetKeep wire) =
          recursiveFrame.targetKeep (commonRename wire) := by
      intro signature wire
      exact keepCommutes wire
    have selectedCommutes :
        sourceRename
            ((Content.Cut.rootFrame structuralOuter structuralBefore
              structuralAfter []).append retained).selected =
          recursiveFrame.selected := by
      apply Var.eq_of_index_eq
      apply Fin.ext
      rw [sourceRename_index]
      simp [recursiveFrame, Content.Cut.rootFrame,
        Transform.Frame.replace, Transform.Frame.append,
        Transform.Frame.insertedHead, Var.index]
    have dataCoherent : (cutDataNaturality []).Coherent
        ((Content.Cut.rootFrame structuralOuter structuralBefore
          structuralAfter []).append retained)
        recursiveFrame
        ((Content.Cut.operation []).appendData
          (Content.Cut.rootFrame structuralOuter structuralBefore
            structuralAfter []) cutData retained)
        recursiveData commonRename sourceRename := by
      exact selectedCommutes
    obtain ⟨recursiveSource, recursiveResult, recursiveEvidence,
        recursiveSites, recursiveSourceEq, recursiveArgumentEq,
        ⟨recursiveResultIso⟩, ⟨recursiveEndpointIso⟩⟩ :=
      targetItemsReindex (baseOperation := Content.Cut.operation [])
        (external := []) (mappedFrame := recursiveFrame)
        (mappedData := recursiveData) formalEvidence formalSites
        (Vars.nil : Vars [] []) commonRename sourceRename sourceRename
        keepCommutes targetKeepCommutes selectedCommutes
        (cutDataNaturality []) dataCoherent
    let oldLocals := structuralBefore ++ structuralAfter
    let newLocals := structuralBefore ++ (structuralAfter ++ retained)
    let fullInstantiated := Region.adjoinAt oldLocals .nil result
    let recursiveInstantiated := Region.adjoinAt newLocals .nil recursiveResult
    let recursivePending : Region structuralOuter :=
      .mk (structuralBefore ++ .rel [] :: (structuralAfter ++ retained))
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
    let pendingLocals := structuralBefore ++ .rel [] :: structuralAfter
    let rawPrepared : Region structuralOuter :=
      Region.adjoinAt pendingLocals .nil
        (itemsEdit (operation := Content.Cut.operation []) cutData evidence
          cutSites).endpoint
    have rawPreparedValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context
      (.mk pendingLocals items) rawPrepared
      structuralRequest.pendingCanonical
      structuralRequest.pendingExternalTwoEnded rootCutScope
    let endpointNested : RegionIso (WireEquiv.refl structuralOuter)
        rawPrepared
        (Region.adjoinAt pendingLocals .nil (.mk retained formalSource)) := by
      have appendedId :
          (WireRenaming.id : WireRenaming
            (structuralOuter ++ pendingLocals)
            (structuralOuter ++ pendingLocals)).appendRight retained =
            WireRenaming.id := by
        apply WireRenaming.ext
        intro signature wire
        exact WireRenaming.appendRight_id_apply retained wire
      have normalizedEndpoint : RegionIso
          (WireEquiv.refl (structuralOuter ++ pendingLocals))
          (itemsEdit (operation := Content.Cut.operation []) cutData evidence
            cutSites).endpoint
          (.mk retained formalSource) := by
        change RegionIso (WireEquiv.refl (structuralOuter ++ pendingLocals))
          (Region.renameWires
            (WireEquiv.refl
              (structuralOuter ++ pendingLocals)).toRenaming
            (itemsEdit (operation := Content.Cut.operation []) cutData evidence
              cutSites).endpoint)
          (.mk retained
            (formalSource.renameWires
              ((WireRenaming.id : WireRenaming
                (structuralOuter ++ pendingLocals)
                (structuralOuter ++ pendingLocals)).appendRight retained)))
            at rootEndpointIso
        rw [show (WireEquiv.refl
            (structuralOuter ++ pendingLocals)).toRenaming =
              WireRenaming.id from rfl,
          Region.renameWires_id, appendedId, ItemSeq.renameWires_id]
          at rootEndpointIso
        exact rootEndpointIso
      exact RegionIso.adjoinAt pendingLocals .nil normalizedEndpoint
    let nestedPresentation : RegionIso (WireEquiv.refl structuralOuter)
        (Region.adjoinAt pendingLocals .nil (.mk retained formalSource))
        (Region.adjoinAt pendingLocals .nil
          (Region.adjoinAt retained .nil (Region.ofItems formalSource))) :=
      RegionIso.adjoinAt pendingLocals .nil
        (RegionIso.adjoinAtOfItems retained formalSource).symm
    let flatPending := Region.adjoinAt (pendingLocals ++ retained)
      (Region.extendHostItems pendingLocals .nil (.mk retained .nil))
      ((Region.ofItems formalSource).renameWires
        (Region.adjoinMaterialWire structuralOuter pendingLocals retained))
    let nestedToFlat : RegionIso (WireEquiv.refl structuralOuter)
        (Region.adjoinAt pendingLocals .nil
          (Region.adjoinAt retained .nil (Region.ofItems formalSource)))
        flatPending := by
      exact (RegionIso.adjoinAtAssoc pendingLocals .nil retained .nil
        (Region.ofItems formalSource)).symm
    let rawToFlat := endpointNested.trans
      (nestedPresentation.trans nestedToFlat)
    have pendingLocalsEq : pendingLocals ++ retained =
        structuralBefore ++ .rel [] :: (structuralAfter ++ retained) := by
      simp [pendingLocals, List.append_assoc]
    let pendingLocalsIso := WireEquiv.ofEq pendingLocalsEq
    let pendingSourceMap := Region.adjoinMaterialWire structuralOuter
      pendingLocals retained
    let appendNil : WireRenaming
        ((structuralOuter ++ pendingLocals) ++ retained)
        (((structuralOuter ++ pendingLocals) ++ retained) ++ []) :=
      ⟨fun wire => wire.appendLeft []⟩
    let flatMap := WireRenaming.comp
      (Region.adjoinMaterialWire structuralOuter
        (pendingLocals ++ retained) [])
      (WireRenaming.comp (pendingSourceMap.appendRight []) appendNil)
    let flatLocalsIso := (WireEquiv.appendNil
      (pendingLocals ++ retained)).trans pendingLocalsIso
    let flatAmbient := (WireEquiv.refl structuralOuter).append flatLocalsIso
    have flatCommutes : ∀ {signature}
        (wire : Var
          ((structuralOuter ++ pendingLocals) ++ retained) signature),
        flatAmbient (flatMap wire) = sourceRename wire := by
      intro signature wire
      apply Var.eq_of_index_eq
      apply Fin.ext
      have ambientIndex : (flatAmbient (flatMap wire)).index.val =
          (flatMap wire).index.val := by
        apply Var.appendCases (left := structuralOuter)
          (right := (pendingLocals ++ retained) ++ [])
          (motive := fun mapped =>
            (flatAmbient mapped).index.val = mapped.index.val)
        · intro inheritedSignature inherited
          simpa only [Var.index_appendLeft] using
            WireEquiv.refl_append_left_index_val flatLocalsIso inherited
        · intro localSignature localWire
          refine Var.appendCases (left := pendingLocals ++ retained)
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
              change ((pendingLocalsIso
                (WireEquiv.appendNil (pendingLocals ++ retained)
                  (inherited.appendLeft []))).index.val) =
                    inherited.index.val
              rw [WireEquiv.appendNil_apply]
              exact WireEquiv.ofEq_index_val pendingLocalsEq inherited
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
    have bodyCompiled := bodyIH bodyCanonical recursiveEvidence
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
          bodyCompiled)
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
    exact itemsCut evidence cutSites structuralRequest preparation
  · intro wires wiresEq
    subst wires
    intro materialCanonical structuralOuter structuralBefore structuralAfter
      items result evidence structuralRequest
    have patternEq :
        Erasure.Exposure.supportPattern (Region.ofItems ItemSeq.nil)
            materialCanonical = Structural.Blank.blankPattern := by
      apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
    rw [patternEq] at evidence
    exact Structural.Blank.itemsEnds evidence structuralRequest
  · intro wires materialHead materialTail materialHeadIH materialTailIH wiresEq
    subst wires
    intro materialCanonical structuralOuter structuralBefore structuralAfter
      items result evidence structuralRequest
    let headMaterial := Region.singleton materialHead
    let tailMaterial := Region.ofItems materialTail
    have materialPresentation : headMaterial.conjoin tailMaterial =
        Region.ofItems (.cons materialHead materialTail) := by
      exact Region.singleton_conjoin_ofItems materialHead materialTail
    have combinedCanonical : (headMaterial.conjoin tailMaterial).Canonical := by
      rw [materialPresentation]
      exact materialCanonical
    have childCanonical :=
      (Region.Canonical.conjoin_iff headMaterial tailMaterial).mp
        combinedCanonical
    have headCanonical : headMaterial.Canonical := childCanonical.1
    have tailCanonical : tailMaterial.Canonical := childCanonical.2
    let parallelData :=
      (Content.Parallel.firstHead structuralOuter structuralBefore
          structuralAfter [],
        Content.Parallel.secondHead structuralOuter structuralBefore
          structuralAfter [])
    obtain ⟨parallelSites⟩ := parallelItemsSites_nonempty
      (frame := Content.Parallel.rootFrame structuralOuter structuralBefore
        structuralAfter []) evidence parallelData
    let headPattern := Erasure.Exposure.supportPattern headMaterial
      headCanonical
    let tailPattern := Erasure.Exposure.supportPattern tailMaterial
      tailCanonical
    let fullPattern := Erasure.Exposure.supportPattern
      (Region.ofItems (.cons materialHead materialTail)) materialCanonical
    have selectedCase : SupportParallelSelectedCase headPattern tailPattern
        fullPattern := by
      refine fun {common sourceWires splitWires} {parallel} {heads}
        {sitePattern} frames application siteData => ?_
      exact supportParallelSelectedFactors_nonempty frames materialHead
        materialTail headCanonical tailCanonical materialCanonical application
        siteData
    obtain ⟨factors⟩ := supportParallelItemsFactors_nonempty headPattern
      tailPattern fullPattern selectedCase
      (supportParallelFramesRoot structuralOuter structuralBefore
        structuralAfter) evidence parallelSites
    obtain ⟨splitIso⟩ := factors.splitIso
    let fullInstantiated := Region.adjoinAt
      (structuralBefore ++ structuralAfter) .nil result
    let tailInstantiated := Region.adjoinAt
      (structuralBefore ++ structuralAfter) .nil factors.tailResult
    let tailPending : Region structuralOuter :=
      .mk (structuralBefore ++ .rel [] :: structuralAfter)
        factors.tailSource
    let headInstantiated := Region.adjoinAt
      (structuralBefore ++ .rel [] :: structuralAfter) .nil
        factors.headResult
    let splitPending : Region structuralOuter :=
      .mk (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter)
        factors.splitSource
    have tailPendingScope : ScopePreservation
        (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
        tailPending := by
      exact supportParallelRootTailScope structuralOuter structuralBefore
        structuralAfter factors
    have splitPendingScope : ScopePreservation
        (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
        splitPending := by
      exact supportParallelRootSplitScope structuralOuter structuralBefore
        structuralAfter factors
    have resultHostedScope : ScopePreservation fullInstantiated
        tailInstantiated := by
      exact adjoinAt_preserves_scope
        (structuralBefore ++ structuralAfter) .nil result factors.tailResult
        factors.resultScope
    have tailInstantiatedValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context fullInstantiated tailInstantiated
      structuralRequest.instantiatedCanonical
      structuralRequest.instantiatedExternalTwoEnded resultHostedScope
    have tailPendingValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context
      (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
      tailPending structuralRequest.pendingCanonical
      structuralRequest.pendingExternalTwoEnded tailPendingScope
    let tailPresentation := RegionIso.adjoinAtOfItems
      (structuralBefore ++ .rel [] :: structuralAfter) factors.tailSource
    let adjoinedTail := Region.adjoinAt
      (structuralBefore ++ .rel [] :: structuralAfter) .nil
      (Region.ofItems factors.tailSource)
    have adjoinedTailValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context tailPending adjoinedTail
      tailPendingValidity.1 tailPendingValidity.2
      (ScopePreservation.ofIso tailPresentation.symm)
    have headHostedScope : ScopePreservation tailPending
        headInstantiated :=
      (ScopePreservation.ofIso tailPresentation.symm).trans
        (adjoinAt_preserves_scope
          (structuralBefore ++ .rel [] :: structuralAfter) .nil
          (Region.ofItems factors.tailSource) factors.headResult
          factors.headReverseScope)
    have headInstantiatedValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context tailPending headInstantiated
      tailPendingValidity.1 tailPendingValidity.2 headHostedScope
    have splitPendingValidity := filledValidityOfScope
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context
      (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
      splitPending structuralRequest.pendingCanonical
      structuralRequest.pendingExternalTwoEnded splitPendingScope
    have polarityEq : structuralRequest.occurrence.context.polarity =
        structuralRequest.polarity := structuralRequest.continuation.1
    have headSourceCanonical :
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity headInstantiated
            splitPending)).Canonical :=
      polaritySource_property structuralRequest.polarity
        (fun region =>
          (structuralRequest.occurrence.context.fill region).Canonical)
        headInstantiated splitPending headInstantiatedValidity.1
        splitPendingValidity.1
    have headSourceExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity headInstantiated
            splitPending)) :=
      polaritySource_property structuralRequest.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill region))
        headInstantiated splitPending headInstantiatedValidity.2
        splitPendingValidity.2
    let headRequest : Telescope.Request headInstantiated splitPending := {
      boundary := structuralRequest.boundary
      source := structuralRequest.occurrence.interface.withBody
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity headInstantiated
            splitPending)) headSourceCanonical headSourceExternal
      endpoint := splitPending
      polarity := structuralRequest.polarity
      occurrence := exactOccurrence structuralRequest.occurrence.interface
        structuralRequest.occurrence.context
        (polaritySource structuralRequest.polarity headInstantiated
          splitPending) headSourceCanonical headSourceExternal
      instantiatedCanonical := headInstantiatedValidity.1
      instantiatedExternalTwoEnded := headInstantiatedValidity.2
      pendingCanonical := splitPendingValidity.1
      pendingExternalTwoEnded := splitPendingValidity.2
      endpointCanonical := splitPendingValidity.1
      endpointExternalTwoEnded := splitPendingValidity.2
      continuation := Telescope.refl structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context splitPendingValidity.1
        splitPendingValidity.2 polarityEq
    }
    have headCompiled := materialHeadIH rfl headCanonical
      factors.headEvidence headRequest
    have headTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context headInstantiated splitPending
        headInstantiatedValidity.1 headInstantiatedValidity.2
        splitPendingValidity.1 splitPendingValidity.2 := by
      exact Telescope.StrictDerives.toTelescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context headInstantiatedValidity.1
        headInstantiatedValidity.2 splitPendingValidity.1
        splitPendingValidity.2 polarityEq
        (by simpa only [headRequest, Telescope.Request.Result] using
          headCompiled)
    have headBridgeTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context tailPending headInstantiated
        tailPendingValidity.1 tailPendingValidity.2
        headInstantiatedValidity.1 headInstantiatedValidity.2 := by
      have renamedHeadCanonical :
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt
              (structuralBefore ++ .rel [] :: structuralAfter) .nil
              (factors.headResult.renameWires WireRenaming.id))).Canonical := by
        simpa only [Region.renameWires_id] using headInstantiatedValidity.1
      have renamedHeadExternal : OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt
              (structuralBefore ++ .rel [] :: structuralAfter) .nil
              (factors.headResult.renameWires WireRenaming.id))) := by
        intro signature wire
        simpa only [Region.renameWires_id] using
          headInstantiatedValidity.2 wire
      have renamedAdjoinedTailCanonical :
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt
              (structuralBefore ++ .rel [] :: structuralAfter) .nil
              ((Region.ofItems factors.tailSource).renameWires
                WireRenaming.id))).Canonical := by
        simpa only [Region.renameWires_id] using adjoinedTailValidity.1
      have renamedAdjoinedTailExternal : OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt
              (structuralBefore ++ .rel [] :: structuralAfter) .nil
              ((Region.ofItems factors.tailSource).renameWires
                WireRenaming.id))) := by
        intro signature wire
        simpa only [Region.renameWires_id] using adjoinedTailValidity.2 wire
      have rawTelescope : Telescope structuralRequest.polarity
          structuralRequest.occurrence.interface
          structuralRequest.occurrence.context adjoinedTail headInstantiated
          adjoinedTailValidity.1 adjoinedTailValidity.2
          headInstantiatedValidity.1 headInstantiatedValidity.2 := by
        simpa only [Region.renameWires_id] using
          telescopeOfHosted factors.headBridge.symm WireRenaming.id .nil
            structuralRequest.polarity
            structuralRequest.occurrence.interface
            structuralRequest.occurrence.context
            renamedAdjoinedTailCanonical renamedAdjoinedTailExternal
            renamedHeadCanonical renamedHeadExternal polarityEq
      exact telescopeIso tailPresentation
        (RegionIso.refl headInstantiated) rawTelescope
    have tailContinuation : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context tailPending splitPending
        tailPendingValidity.1 tailPendingValidity.2
        splitPendingValidity.1 splitPendingValidity.2 :=
      telescopeTrans headBridgeTelescope headTelescope
    have tailSourceCanonical :
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity tailInstantiated
            splitPending)).Canonical :=
      polaritySource_property structuralRequest.polarity
        (fun region =>
          (structuralRequest.occurrence.context.fill region).Canonical)
        tailInstantiated splitPending tailInstantiatedValidity.1
        splitPendingValidity.1
    have tailSourceExternal : OpenDiagram.ExternalTwoEnded
        structuralRequest.occurrence.interface.boundaryWire
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity tailInstantiated
            splitPending)) :=
      polaritySource_property structuralRequest.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill region))
        tailInstantiated splitPending tailInstantiatedValidity.2
        splitPendingValidity.2
    let tailRequest : Telescope.Request tailInstantiated tailPending := {
      boundary := structuralRequest.boundary
      source := structuralRequest.occurrence.interface.withBody
        (structuralRequest.occurrence.context.fill
          (polaritySource structuralRequest.polarity tailInstantiated
            splitPending)) tailSourceCanonical tailSourceExternal
      endpoint := splitPending
      polarity := structuralRequest.polarity
      occurrence := exactOccurrence structuralRequest.occurrence.interface
        structuralRequest.occurrence.context
        (polaritySource structuralRequest.polarity tailInstantiated
          splitPending) tailSourceCanonical tailSourceExternal
      instantiatedCanonical := tailInstantiatedValidity.1
      instantiatedExternalTwoEnded := tailInstantiatedValidity.2
      pendingCanonical := tailPendingValidity.1
      pendingExternalTwoEnded := tailPendingValidity.2
      endpointCanonical := splitPendingValidity.1
      endpointExternalTwoEnded := splitPendingValidity.2
      continuation := tailContinuation
    }
    have tailCompiled := materialTailIH rfl tailCanonical
      factors.tailEvidence tailRequest
    have tailTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context tailInstantiated splitPending
        tailInstantiatedValidity.1 tailInstantiatedValidity.2
        splitPendingValidity.1 splitPendingValidity.2 := by
      exact Telescope.StrictDerives.toTelescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context tailInstantiatedValidity.1
        tailInstantiatedValidity.2 splitPendingValidity.1
        splitPendingValidity.2 polarityEq
        (by simpa only [tailRequest, Telescope.Request.Result] using
          tailCompiled)
    have resultBridgeTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context fullInstantiated
        tailInstantiated structuralRequest.instantiatedCanonical
        structuralRequest.instantiatedExternalTwoEnded
        tailInstantiatedValidity.1 tailInstantiatedValidity.2 := by
      have renamedResultCanonical :
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
              (result.renameWires WireRenaming.id))).Canonical := by
        simpa only [Region.renameWires_id] using
          structuralRequest.instantiatedCanonical
      have renamedResultExternal : OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
              (result.renameWires WireRenaming.id))) := by
        intro signature wire
        simpa only [Region.renameWires_id] using
          structuralRequest.instantiatedExternalTwoEnded wire
      have renamedTailResultCanonical :
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
              (factors.tailResult.renameWires WireRenaming.id))).Canonical := by
        simpa only [Region.renameWires_id] using tailInstantiatedValidity.1
      have renamedTailResultExternal : OpenDiagram.ExternalTwoEnded
          structuralRequest.occurrence.interface.boundaryWire
          (structuralRequest.occurrence.context.fill
            (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
              (factors.tailResult.renameWires WireRenaming.id))) := by
        intro signature wire
        simpa only [Region.renameWires_id] using
          tailInstantiatedValidity.2 wire
      simpa only [Region.renameWires_id] using
        telescopeOfHosted factors.resultBridge WireRenaming.id .nil
          structuralRequest.polarity structuralRequest.occurrence.interface
          structuralRequest.occurrence.context renamedResultCanonical
          renamedResultExternal renamedTailResultCanonical
          renamedTailResultExternal polarityEq
    have preparationTelescope : Telescope structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context fullInstantiated splitPending
        structuralRequest.instantiatedCanonical
        structuralRequest.instantiatedExternalTwoEnded
        splitPendingValidity.1 splitPendingValidity.2 :=
      telescopeTrans resultBridgeTelescope tailTelescope
    let basePreparation : structuralRequest.Preparation splitPending := {
      prepared := splitPending
      preparedCanonical := splitPendingValidity.1
      preparedExternalTwoEnded := splitPendingValidity.2
      rawPreparedCanonical := splitPendingValidity.1
      rawPreparedExternalTwoEnded := splitPendingValidity.2
      preparedIso := RegionIso.refl splitPending
      telescope := by
        simpa only [fullInstantiated] using preparationTelescope
    }
    let rawToSplit := (RegionIso.adjoinAt
      (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter) .nil
      splitIso).trans (RegionIso.adjoinAtOfItems
        (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter)
        factors.splitSource)
    exact itemsParallel evidence parallelSites structuralRequest
      (basePreparation.rawIso rawToSplit.symm)

end Structural

end VisualProof.Rule.Completeness.Comprehension
