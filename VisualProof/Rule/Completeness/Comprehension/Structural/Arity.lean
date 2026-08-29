import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

structure SupportArityShiftScope
    {common sourceWires targetWires : List Sig}
    {arguments : List Sig}
    {added : Sig}
    (frame : Transform.Frame arguments common sourceWires targetWires)
    (data : (Arity.operation arguments added).Data frame)
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
    {arguments : List Sig}
    {added : Sig}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Arity.operation arguments added).Data frame}
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
  · change Var targetWires (.rel (arguments ++ [added])) at data
    exact SupportParallelIncidenceScope.iso sourceIso targetIso
      frame.selected data scope.selected

theorem SupportArityShiftScope.conjoin
    {arguments : List Sig}
    {added : Sig}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Arity.operation arguments added).Data frame}
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
  · change Var targetWires (.rel (arguments ++ [added])) at data
    exact SupportParallelIncidenceScope.conjoin frame.selected data
      first.selected second.selected

theorem SupportArityShiftScope.cut
    {arguments : List Sig}
    {added : Sig}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Arity.operation arguments added).Data frame}
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
  · change Var targetWires (.rel (arguments ++ [added])) at data
    exact SupportParallelIncidenceScope.cut frame.selected data scope.selected

theorem SupportArityShiftScope.adjoin
    {arguments : List Sig}
    {added : Sig}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Arity.operation arguments added).Data frame}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (scope : SupportArityShiftScope (frame.append locals)
      ((Arity.operation arguments added).appendData frame data locals) source target) :
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
      {arguments : List Sig}
      {added : Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {pattern : OpenDiagram arguments}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Arity.operation arguments added) data evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := arityItemsSites_nonempty
          (frame := frame.append _)
          (data := (Arity.operation arguments added).appendData frame data _)
          childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem arityItemsSites_nonempty
      {arguments : List Sig}
      {added : Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {pattern : OpenDiagram arguments}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (Arity.operation arguments added) data evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := arityItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := arityItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem arityItemSites_nonempty
      {arguments : List Sig}
      {added : Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {pattern : OpenDiagram arguments}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Arity.operation arguments added) data evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | term output freeArity ports term =>
        exact ⟨.term (pattern := pattern) output freeArity ports term⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := arityRegionSites_nonempty childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

theorem aritySitePorts_countIndex_retained
    (ports : Vars targetWires arguments) (added : Sig)
    (index : Fin targetWires.length) :
    (Arity.Vars.append
      (ports.map fun wire => wire.appendLeft [added])
      (.cons (Var.appendRight targetWires .here) .nil)).countIndex index.val =
        ports.countIndex index.val := by
  induction ports with
  | nil =>
      simp only [Vars.map, Arity.Vars.append, Vars.countIndex,
        Var.index_appendRight]
      simp [Nat.ne_of_gt index.isLt]
  | cons head tail induction =>
      simp only [Vars.map, Arity.Vars.append, Vars.countIndex,
        Var.index_appendLeft, induction]

theorem aritySitePorts_countIndex_added
    (ports : Vars targetWires arguments) (added : Sig) :
    (Arity.Vars.append
      (ports.map fun wire => wire.appendLeft [added])
      (.cons (Var.appendRight targetWires .here) .nil)).countIndex
        targetWires.length = 1 := by
  induction ports with
  | nil =>
      simp only [Vars.map, Arity.Vars.append, Vars.countIndex,
        Var.index_appendRight]
      simp
  | cons head tail induction =>
      simp only [Vars.map, Arity.Vars.append, Vars.countIndex,
        Var.index_appendLeft, induction]
      simp [Nat.ne_of_lt head.index.isLt]

theorem arityApplication_substitution_left
    (application : Vars common arguments) (added : Sig)
    {signature : Sig} (wire : Var arguments signature) :
    EqualityNormalization.formalSubstitution
        (Arity.Vars.append
          (application.map fun selected => selected.appendLeft [added])
          (.cons (Var.appendRight common .here) .nil))
        (wire.appendLeft [added]) =
      (EqualityNormalization.formalSubstitution application wire).appendLeft
        [added] := by
  induction application with
  | nil => exact nomatch wire
  | cons head tail induction =>
      cases wire with
      | here => rfl
      | there rest => exact induction rest

theorem arityApplication_substitution_added
    (application : Vars common arguments) (added : Sig) :
    EqualityNormalization.formalSubstitution
        (Arity.Vars.append
          (application.map fun selected => selected.appendLeft [added])
          (.cons (Var.appendRight common .here) .nil))
        (Var.appendRight arguments (.here : Var [added] added)) =
      Var.appendRight common .here := by
  induction application with
  | nil => rfl
  | cons head tail induction => exact induction

theorem aritySelectedAtomScope
    {arguments : List Sig}
    {added : Sig}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Arity.operation arguments added).Data frame}
    (retainedInvariant : Transform.RetainedIndexInvariant frame)
    (headInvariant : Transform.IndexedHeadInvariant frame data)
    (ports : Vars common arguments)
    (siteData : (Arity.operation arguments added).SiteData frame data ports) :
    SupportArityShiftScope frame data
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((Arity.operation arguments added).site frame data ports siteData) := by
  cases siteData
  change Var targetWires (.rel (arguments ++ [added])) at data
  change SupportArityShiftScope frame data
    (Region.singleton (.atom frame.selected
      (ports.map fun wire => frame.sourceKeep wire)))
    (Region.mk [added]
      (.cons
        (.atom (data.appendLeft [added])
          (Arity.Vars.append
            ((ports.map fun wire => frame.targetKeep wire).map
              fun wire => wire.appendLeft [added])
            (.cons (Var.appendRight targetWires .here) .nil)))
        (.cons (.identity added 1 (fun _ =>
          Var.appendRight targetWires .here)) .nil)))
  constructor
  · intro _
    have dataLt : data.index.val < targetWires.length := data.index.isLt
    have dataNotLocal : data.index.val ≠ targetWires.length :=
      Nat.ne_of_lt dataLt
    constructor
    · intro localIndex
      cases localIndex using Fin.cases with
      | zero =>
        simp only [ItemSeq.incidencePaths, Item.incidencePaths,
          List.append_nil, Var.index_appendLeft, Fin.val_zero, Nat.add_zero,
          Var.index_appendRight]
        rw [aritySitePorts_countIndex_added
          (ports.map fun wire => frame.targetKeep wire) added]
        simp [RegionPath.RootedTwo, dataNotLocal]
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
    have reflects : ∀ {leftSignature rightSignature}
        (left : Var common leftSignature) (right : Var common rightSignature),
        (frame.sourceKeep left).index.val =
            (frame.sourceKeep right).index.val ↔
          (frame.targetKeep left).index.val =
            (frame.targetKeep right).index.val := by
      intro leftSignature rightSignature left right
      rw [headInvariant.2.1 left, headInvariant.2.1 right]
    have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
      frame.sourceKeep frame.targetKeep reflects wire
    have sourcePaths :
        (Region.singleton (.atom frame.selected
          (ports.map fun port => frame.sourceKeep port))).incidencePaths
            (frame.sourceKeep wire).index.val =
          List.replicate
            ((ports.map fun port => frame.sourceKeep port).countIndex
              (frame.sourceKeep wire).index.val) [] := by
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, sourceFresh]
    have targetPaths :
        (Region.mk [added]
          (.cons
            (.atom (data.appendLeft [added])
              (Arity.Vars.append
                ((ports.map fun port => frame.targetKeep port).map
                  fun port => port.appendLeft [added])
                (.cons (Var.appendRight targetWires .here) .nil)))
            (.cons (.identity added 1 (fun _ =>
              Var.appendRight targetWires .here)) .nil))).incidencePaths
            (frame.targetKeep wire).index.val =
          List.replicate
            ((ports.map fun port => frame.targetKeep port).countIndex
              (frame.targetKeep wire).index.val) [] := by
      simp only [Region.incidencePaths, ItemSeq.incidencePaths,
        Item.incidencePaths, List.append_nil, Var.index_appendLeft]
      rw [aritySitePorts_countIndex_retained
        (ports.map fun port => frame.targetKeep port) added
        (frame.targetKeep wire).index]
      simp [targetFresh, Ne.symm targetNotLocal]
    rw [sourcePaths, targetPaths, portsEq]
    exact SupportParallelIncidenceScope.refl _
  · have dataLt : data.index.val < targetWires.length := data.index.isLt
    have dataNotLocal : data.index.val ≠ targetWires.length :=
      Nat.ne_of_lt dataLt
    have sourcePaths :
        (Region.singleton (.atom frame.selected
          (ports.map fun port => frame.sourceKeep port))).incidencePaths
          frame.selected.index.val = [[]] := by
      have portsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports frame.sourceKeep
          frame.selected.index.val
          (fun wire => Ne.symm (retainedInvariant.selectedFresh wire))
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, portsZero]
    have targetPaths :
        (Region.mk [added]
          (.cons
            (.atom (data.appendLeft [added])
              (Arity.Vars.append
                ((ports.map fun port => frame.targetKeep port).map
                  fun port => port.appendLeft [added])
                (.cons (Var.appendRight targetWires .here) .nil)))
            (.cons (.identity added 1 (fun _ =>
              Var.appendRight targetWires .here)) .nil))).incidencePaths
            data.index.val = [[]] := by
      have portsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports frame.targetKeep
          data.index.val (fun wire => by
            rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
            exact Ne.symm (retainedInvariant.selectedFresh wire))
      simp only [Region.incidencePaths, ItemSeq.incidencePaths,
        Item.incidencePaths, List.append_nil, Var.index_appendLeft]
      rw [aritySitePorts_countIndex_retained
        (ports.map fun port => frame.targetKeep port) added data.index]
      simp [portsZero, Ne.symm dataNotLocal]
    have pairEq :
        ((Region.singleton (.atom frame.selected
            (ports.map fun port => frame.sourceKeep port))).incidencePaths
            frame.selected.index.val,
          (Region.mk [added]
            (.cons
              (.atom (data.appendLeft [added])
                (Arity.Vars.append
                  ((ports.map fun port => frame.targetKeep port).map
                    fun port => port.appendLeft [added])
                  (.cons (Var.appendRight targetWires .here) .nil)))
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
      {arguments : List Sig}
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {source : Region sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.RegionEdit (Arity.operation arguments added) frame data
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
      {arguments : List Sig}
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {source : ItemSeq sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemsEdit (Arity.operation arguments added) frame data
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
      {arguments : List Sig}
      {added : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : (Arity.operation arguments added).Data frame}
      {source : Item sourceWires}
      (retainedInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.IndexedHeadInvariant frame data)
      (edit : Transform.ItemEdit (Arity.operation arguments added) frame data
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
              targetPortsZero]
            exact Ne.symm targetHeadFresh
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
            simp [List.count_nil, targetFresh]
          have sourceEmpty :
              (Region.singleton (.identity (.rel arguments) 1 ports)).incidencePaths
                (frame.sourceKeep wire).index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths, selected,
              sourceCount]
          have targetEmpty :
              (Transform.unaryPin data).incidencePaths
                (frame.targetKeep wire).index.val = [] := by
            simp only [Transform.unaryPin, Region.singleton,
              Region.incidencePaths_ofItems, ItemSeq.incidencePaths,
              Item.incidencePaths]
            simpa [List.ofFn_succ, List.ofFn_zero] using targetCount
          simp only [Transform.ItemEdit.run]
          rw [sourceEmpty]
          change SupportParallelIncidenceScope []
            ((Transform.unaryPin data).incidencePaths
              (frame.targetKeep wire).index.val)
          rw [targetEmpty]
          exact SupportParallelIncidenceScope.refl []
        · have sourcePaths :
              (Region.singleton (.identity (.rel arguments) 1 ports)).incidencePaths
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
    | term output freeArity ports term =>
        constructor
        · intro _
          exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
        · intro wireSignature wire
          have outputEq :
              (frame.sourceKeep output).index.val =
                  (frame.sourceKeep wire).index.val ↔
                (frame.targetKeep output).index.val =
                  (frame.targetKeep wire).index.val := by
            rw [headInvariant.2.1 output, headInvariant.2.1 wire]
          have portsEq := Transform.countPorts_map_eq_of_reflection
            freeArity ports frame.sourceKeep frame.targetKeep
              (fun left right => by
                rw [headInvariant.2.1 left, headInvariant.2.1 right]) wire
          simp only [Transform.ItemEdit.run, Region.singleton,
            Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft]
          simp only [outputEq, portsEq]
          exact SupportParallelIncidenceScope.refl _
        · have sourceOutputFresh := retainedInvariant.selectedFresh output
          have targetOutputFresh : data.index.val ≠
              (frame.targetKeep output).index.val := by
            rw [← headInvariant.2.2, ← headInvariant.2.1 output]
            exact sourceOutputFresh
          have sourcePortsZero :=
            countPorts_map_eq_zero_of_no_preimage freeArity ports
              frame.sourceKeep frame.selected.index.val
              (fun wire => Ne.symm (retainedInvariant.selectedFresh wire))
          have targetPortsZero :=
            countPorts_map_eq_zero_of_no_preimage freeArity ports
              frame.targetKeep data.index.val (fun wire => by
                rw [← headInvariant.2.2, ← headInvariant.2.1 wire]
                exact Ne.symm (retainedInvariant.selectedFresh wire))
          have sourceEmpty :
              (Region.singleton (.term (frame.sourceKeep output) freeArity
                (fun port => frame.sourceKeep (ports port)) term)).incidencePaths
                  frame.selected.index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              Ne.symm sourceOutputFresh, sourcePortsZero]
          have targetEmpty :
              (Region.singleton (.term (frame.targetKeep output) freeArity
                (fun port => frame.targetKeep (ports port)) term)).incidencePaths
                  data.index.val = [] := by
            simp [Region.singleton, Region.incidencePaths_ofItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              Ne.symm targetOutputFresh, targetPortsZero]
          simp only [Transform.ItemEdit.run]
          rw [sourceEmpty, targetEmpty]
          exact SupportParallelIncidenceScope.refl []
    | cut childEdit =>
        exact SupportArityShiftScope.cut
          (arityRegionEditScope retainedInvariant headInvariant childEdit)
  termination_by sizeOf source
end


/-- Root-level scope preservation for the exact Arity endpoint. -/
theorem arityRootScope
    (outer before after arguments : List Sig) (added : Sig)
    {pattern : OpenDiagram arguments}
    {source : ItemSeq (outer ++ (before ++ .rel arguments :: after))}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern (Arity.rootFrame outer before after arguments added).sourceKeep
        (Arity.rootFrame outer before after arguments added).selected source result)
    (sites : ItemsSites (Arity.operation arguments added)
      (Arity.targetHead outer before after arguments added) evidence) :
    ScopePreservation
      (.mk (before ++ .rel arguments :: after) source)
      (Region.adjoinAt
        (before ++ .rel (arguments ++ [added]) :: after) .nil
        (itemsEdit (operation := Arity.operation arguments added)
          (Arity.targetHead outer before after arguments added) evidence
            sites).endpoint) := by
  let frame := Arity.rootFrame outer before after arguments added
  let data := Arity.targetHead outer before after arguments added
  let sourceLocals := before ++ .rel arguments :: after
  let targetLocals := before ++ .rel (arguments ++ [added]) :: after
  let output := itemsEdit (operation := Arity.operation arguments added) data
    evidence sites
  have retainedInvariant : Transform.RetainedIndexInvariant frame := by
    exact Transform.RetainedIndexInvariant.replace outer before after
      [.rel (arguments ++ [added])] arguments
  have headInvariant : Transform.IndexedHeadInvariant frame data := by
    refine ⟨by simp, ?_, ?_⟩
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
            Var.appendRight]
        · intro afterSignature afterWire
          simp [frame, Arity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Var.appendRight, Var.index]
    · simp [frame, data, Arity.rootFrame, Arity.targetHead,
        Transform.Frame.replace, Transform.Frame.insertedHead,
        Var.index]
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
      refine Var.appendCases (left := before)
        (right := .rel (arguments ++ [added]) :: after)
        (motive := fun localWire => RegionPath.RootedTwo
          (output.edit.run.incidencePaths
            (outer.length + localWire.index.val))) ?_ ?_ localWire
      · intro signature beforeWire
        let sourceLocal : Var sourceLocals signature :=
          beforeWire.appendLeft (.rel arguments :: after)
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
            let sourceLocal : Var sourceLocals (.rel arguments) :=
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


/-- Reassociate the item carrier after exposing the leading local as the
last inherited argument. -/
noncomputable def arityExposedItems
    (arguments : List Sig) (firstLocal : Sig) (locals : List Sig)
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals)) :
    ItemSeq ((arguments ++ [firstLocal]) ++ locals) :=
  materialItems.renameWires
    (WireEquiv.ofEq (by simp [List.append_assoc])).toRenaming

noncomputable def arityExposedMaterial
    (arguments : List Sig) (firstLocal : Sig) (locals : List Sig)
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals)) :
    Region (arguments ++ [firstLocal]) :=
  .mk locals (arityExposedItems arguments firstLocal locals materialItems)

/-- Exposing the leading local changes only the region's presentation. -/
noncomputable def arityExposedMaterialIso
    {arguments : List Sig} {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals)) :
    RegionIso (WireEquiv.refl arguments)
      (Region.mk (firstLocal :: locals) materialItems : Region arguments)
      (Region.adjoinAt [firstLocal] .nil
        (arityExposedMaterial arguments firstLocal locals materialItems)) := by
  let reassociate : WireEquiv
      (arguments ++ firstLocal :: locals)
      ((arguments ++ [firstLocal]) ++ locals) :=
    WireEquiv.ofEq (by simp [List.append_assoc])
  let targetRename := WireRenaming.comp
    (Region.adjoinMaterialWire arguments [firstLocal] locals)
    reassociate.toRenaming
  let ambient := (WireEquiv.refl arguments).append
    (WireEquiv.refl (firstLocal :: locals))
  have commutes : ∀ {signature}
      (wire : Var (arguments ++ firstLocal :: locals) signature),
      ambient (WireRenaming.id wire) = targetRename wire := by
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    have ambientIndex : (ambient (WireRenaming.id wire)).index.val =
        wire.index.val := by
      rw [show ambient = WireEquiv.refl _ by
        exact WireEquiv.append_refl arguments (firstLocal :: locals)]
      rfl
    rw [ambientIndex]
    change wire.index.val =
      (Region.adjoinMaterialWire arguments [firstLocal] locals
        (reassociate wire)).index.val
    rw [Region.adjoinMaterialWire_index_val,
      WireEquiv.ofEq_index_val]
  let itemsIso := ItemSeqIso.renameWires materialItems WireRenaming.id
    targetRename ambient commutes
  rw [ItemSeq.renameWires_id] at itemsIso
  refine .mk (WireEquiv.refl (firstLocal :: locals)) ?_
  simpa only [Region.adjoinAt, Region.locals, Region.items,
    arityExposedMaterial, arityExposedItems, ItemSeq.renameWires,
    ItemSeq.nil_append, ItemSeq.renameWires_comp, targetRename,
    reassociate] using itemsIso

theorem arityExposedMaterial_canonical
    {arguments : List Sig} {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems :
        Region arguments).Canonical) :
    (arityExposedMaterial arguments firstLocal locals
      materialItems).Canonical := by
  let presentation := arityExposedMaterialIso materialItems
  have adjoinedCanonical := presentation.canonical_iff.mp materialCanonical
  exact Region.Canonical.material_of_adjoinAt [firstLocal] .nil _
    adjoinedCanonical

def arityTargetOperation (arguments : List Sig) (firstLocal : Sig) :
    Transform.Operation (arguments ++ [firstLocal]) where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (arguments ++ [firstLocal]))
  appendData := fun _ head locals => head.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun {_ _ targetWires} _ _ _ _ => Region.blank targetWires
  pin := fun {_ _ targetWires} _ _ => Region.blank targetWires

def arityTargetNaturality (arguments : List Sig) (firstLocal : Sig) :
    DataNaturality (arityTargetOperation arguments firstLocal) where
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
    {frame : Transform.Frame (arguments ++ [firstLocal]) common sourceWires
      targetWires}
    (data : (arityTargetOperation arguments firstLocal).Data frame)
    (head : Var targetWires (.rel (arguments ++ [firstLocal]))) : Prop :=
  head = data

theorem arityDataSelects_append
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (arguments ++ [firstLocal]) common sourceWires
      targetWires}
    (data : (arityTargetOperation arguments firstLocal).Data frame)
    (head : Var targetWires (.rel (arguments ++ [firstLocal])))
    (selects : arityDataSelects data head)
    (locals : List Sig) :
    arityDataSelects
      ((arityTargetOperation arguments firstLocal).appendData frame data locals)
      (head.appendLeft locals) := by
  exact congrArg (fun wire => wire.appendLeft locals) selects

def arityDataAligned
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame arguments common localSourceWires
      localTargetWires}
    {formalFrame : Transform.Frame (arguments ++ [firstLocal]) common
      formalSourceWires formalTargetWires}
    (localData : (Arity.operation arguments firstLocal).Data localFrame)
    (formalData : (arityTargetOperation arguments firstLocal).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires) : Prop :=
  ambient.toRenaming localData = formalData

theorem arityDataAligned_append
    {common localSourceWires localTargetWires formalSourceWires
      formalTargetWires : List Sig}
    {localFrame : Transform.Frame arguments common localSourceWires
      localTargetWires}
    {formalFrame : Transform.Frame (arguments ++ [firstLocal]) common
      formalSourceWires formalTargetWires}
    (localData : (Arity.operation arguments firstLocal).Data localFrame)
    (formalData : (arityTargetOperation arguments firstLocal).Data formalFrame)
    (ambient : WireEquiv localTargetWires formalTargetWires)
    (aligned : arityDataAligned localData formalData ambient)
    (locals : List Sig) :
    arityDataAligned
      ((Arity.operation arguments firstLocal).appendData localFrame localData
        locals)
      ((arityTargetOperation arguments firstLocal).appendData formalFrame
        formalData locals)
      (ambient.append (WireEquiv.refl locals)) := by
  simpa only [arityDataAligned, Arity.operation, arityTargetOperation,
    WireEquiv.append_apply_left] using
      congrArg (fun wire => wire.appendLeft locals) aligned

theorem aritySelectedTargetItem
    {arguments : List Sig} {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems :
        Region arguments).Canonical)
    {itemCommon itemSourceWires itemTargetWires : List Sig}
    {fullPattern : OpenDiagram arguments}
    {itemFrame : Transform.Frame arguments itemCommon itemSourceWires
      itemTargetWires}
    {itemData : (Arity.operation arguments firstLocal).Data itemFrame}
    (fullPatternEq : fullPattern = Erasure.Exposure.supportPattern
      (Region.mk (firstLocal :: locals) materialItems : Region arguments)
      materialCanonical)
    (application : Vars itemCommon arguments)
    (siteData : (Arity.operation arguments firstLocal).SiteData itemFrame
      itemData application)
    {formalSourceWires formalTargetWires : List Sig}
    (formalFrame : Transform.Frame (arguments ++ [firstLocal]) itemCommon
      formalSourceWires formalTargetWires)
    (formalData : (arityTargetOperation arguments firstLocal).Data
      formalFrame) :
    TargetItem
      (targetExternal := arguments ++ [firstLocal])
      (targetPattern := Erasure.Exposure.supportPattern
        (arityExposedMaterial arguments firstLocal locals materialItems)
        (arityExposedMaterial_canonical materialItems materialCanonical))
      (targetOperation := arityTargetOperation arguments firstLocal)
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom
        (operation := Arity.operation arguments firstLocal)
        (pattern := fullPattern) (frame := itemFrame) application siteData)
      (Erasure.Exposure.identityBoundary (arguments ++ [firstLocal]))
      formalFrame formalData
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
                    (operation := Arity.operation arguments firstLocal)
                    (pattern := fullPattern) (frame := itemFrame)
                    application siteData)).endpoint.renameWires
                      alignment.ambient.toRenaming)
                (.mk retained (formalSource.renameWires
                  (bridge.sourceToTarget.appendRight retained))))) := by
  subst fullPattern
  let childMaterial : Region (arguments ++ [firstLocal]) :=
    arityExposedMaterial arguments firstLocal locals materialItems
  let childCanonical := arityExposedMaterial_canonical materialItems
    materialCanonical
  let childPattern := Erasure.Exposure.supportPattern childMaterial
    childCanonical
  let retained := [firstLocal]
  let childApplication : Vars (itemCommon ++ retained)
      (arguments ++ [firstLocal]) :=
    Arity.Vars.append
      (application.map fun wire => wire.appendLeft retained)
      (.cons (Var.appendRight itemCommon Var.here) .nil)
  let childFrame := formalFrame.append retained
  let childData := (arityTargetOperation arguments firstLocal).appendData
    formalFrame formalData retained
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
  let recorded := recordingOperation
    (arityTargetOperation arguments firstLocal) (arguments ++ [firstLocal])
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
  · rw [show Erasure.Exposure.identityBoundary
      (arguments ++ [firstLocal]) =
        EqualityNormalization.formalPorts (arguments ++ [firstLocal]) from rfl]
    dsimp only [formalSites, selectedSites, pinSites, nilSites]
    unfold argumentItemsEdit argumentItemEdit
    unfold argumentItemsEdit argumentItemEdit
    unfold argumentItemsEdit
    simp only [childApplication, childFrame, Transform.Frame.append,
      EqualityNormalization.formalPorts_map_substitution,
      WireRenaming.appendRight, Var.appendMap_right]
  · let formalResult :=
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        childPattern childApplication).conjoin
        ((Region.singleton (.identity firstLocal 1
          (fun _ => Var.appendRight itemCommon Var.here))).conjoin
          (Region.blank (itemCommon ++ retained)))
    let staged := Region.adjoinAt retained .nil formalResult
    refine ⟨staged, ?_, ?_, ⟨RegionIso.refl staged⟩, ?_⟩
    · let fullMaterial : Region arguments :=
        .mk (firstLocal :: locals) materialItems
      let fullPattern := Erasure.Exposure.supportPattern fullMaterial
        materialCanonical
      let oldHosted := supportInstantiationHosted fullMaterial
        materialCanonical application
      let oldSubstitution :=
        EqualityNormalization.formalSubstitution application
      let childInst :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          childPattern childApplication
      let childSubstitution :=
        EqualityNormalization.formalSubstitution childApplication
      have childSubstitutionEq : childSubstitution =
          oldSubstitution.appendRight retained := by
        apply WireRenaming.ext
        intro signature wire
        apply Var.appendCases (left := arguments) (right := [firstLocal])
          (motive := fun wire => childSubstitution wire =
            oldSubstitution.appendRight retained wire) ?_ ?_ wire
        · intro inheritedSignature inherited
          simpa only [childSubstitution, childApplication, retained,
            WireRenaming.appendRight, Var.appendMap_left] using
            arityApplication_substitution_left application firstLocal
              inherited
        · intro localSignature localWire
          cases localWire with
          | here =>
              simpa only [childSubstitution, childApplication, retained,
                WireRenaming.appendRight, Var.appendMap_right] using
                arityApplication_substitution_added application firstLocal
          | there tail => exact Fin.elim0 tail.index
      let childHostedRaw := supportInstantiationHosted childMaterial
        childCanonical childApplication
      let childHosted : HostedStrict childInst
          (childMaterial.renameWires
            (oldSubstitution.appendRight retained)) := by
        have childSubstitutionEqRaw :
            EqualityNormalization.formalSubstitution childApplication =
              oldSubstitution.appendRight retained := by
          simpa only [childSubstitution] using childSubstitutionEq
        rw [childSubstitutionEqRaw] at childHostedRaw
        exact childHostedRaw
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
          (oldSubstitution.appendRight retained))
        blank childInst pinTarget childHosted.symm pinHosted
      let childToPinned : HostedStrict
          (childMaterial.renameWires
            (oldSubstitution.appendRight retained))
          formalResult := by
        exact HostedStrict.iso
          (RegionIso.conjoinBlank _).symm
          (RegionIso.conjoinCongr (RegionIso.refl childInst)
            (RegionIso.conjoinBlank pinTarget).symm) withPin
      let lifted := HostedStrict.adjoinAt retained _ _ childToPinned
      let exposedBase := arityExposedMaterialIso materialItems
      let exposedMapped := RegionIso.renameExisting exposedBase oldSubstitution
        oldSubstitution (WireEquiv.refl itemCommon) (fun _ => rfl)
      let exposedTargetEq := Region.renameWires_adjoinAt .nil childMaterial
        oldSubstitution
      let exposedIso : RegionIso (WireEquiv.refl itemCommon)
          (fullMaterial.renameWires oldSubstitution)
          (Region.adjoinAt retained .nil
            (childMaterial.renameWires
              (oldSubstitution.appendRight retained))) :=
        exposedMapped.trans (RegionIso.ofEq exposedTargetEq)
      let exposed := Region.adjoinAt retained .nil
        (childMaterial.renameWires (oldSubstitution.appendRight retained))
      have exposedCanonical : exposed.Canonical :=
        exposedIso.canonical_iff.mp
          ((Region.Canonical.renameWires_iff fullMaterial oldSubstitution).mpr
            materialCanonical)
      let exposedToStaged := HostedStrict.transPinned
        (HostedStrict.ofIso exposedIso) lifted exposedCanonical
      have rawCanonical : (fullMaterial.renameWires oldSubstitution).Canonical :=
        (Region.Canonical.renameWires_iff fullMaterial oldSubstitution).mpr
          materialCanonical
      exact HostedStrict.transPinned oldHosted exposedToStaged rawCanonical
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
          simp [retained]
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
        have rootCount : childApplication.countIndex rootWire.index.val = 1 := by
          simpa only [childApplication, rootWire, retained,
            Var.index_appendRight] using
            aritySitePorts_countIndex_added application firstLocal
        constructor
        · simp only [List.length_append, List.length_map]
          rw [EqualityNormalization.instantiate_incidencePaths_length]
          rw [pinLength, blankLength]
          rw [rootCount]
          omega
        · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
          apply List.mem_append_left
          apply EqualityNormalization.instantiate_incidence_mem_nil_of_nonempty
          apply (EqualityNormalization.instantiate_incidence_nonempty_iff
            childPattern childApplication rootWire).mpr
          rw [rootCount]
          omega
      have stagedPaths : ∀ {signature} (wire : Var itemCommon signature),
          staged.incidencePaths wire.index.val =
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              childPattern childApplication).incidencePaths
                (wire.appendLeft retained).index.val := by
        intro signature wire
        change (Region.adjoinAt retained .nil formalResult).incidencePaths
          wire.index.val = _
        rw [← Var.index_appendLeft wire retained,
          Region.incidencePaths_adjoinAt_nil]
        dsimp only [formalResult]
        rw [Region.incidencePaths_conjoin, Region.incidencePaths_conjoin]
        simp [Region.blank, Region.singleton, Region.ofItems,
          Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
          ItemSeq.incidencePaths, Item.incidencePaths, List.ofFn_succ,
          List.ofFn_zero, retained,
          Ne.symm (Nat.ne_of_lt wire.index.isLt)]
      constructor
      · intro _
        exact stagedCanonical
      · intro signature wire
        have countEq : childApplication.countIndex
            (wire.appendLeft retained).index.val =
              application.countIndex wire.index.val := by
          simpa only [childApplication, retained, Var.index_appendLeft] using
            aritySitePorts_countIndex_retained application firstLocal
              wire.index
        rw [EqualityNormalization.instantiate_incidence_nonempty_iff,
          stagedPaths wire,
          EqualityNormalization.instantiate_incidence_nonempty_iff]
        rw [countEq]
      · intro signature wire sourceRooted
        have countEq : childApplication.countIndex
            (wire.appendLeft retained).index.val =
              application.countIndex wire.index.val := by
          simpa only [childApplication, retained, Var.index_appendLeft] using
            aritySitePorts_countIndex_retained application firstLocal
              wire.index
        rw [EqualityNormalization.instantiate_rootedTwo_iff] at sourceRooted
        rw [stagedPaths wire,
          EqualityNormalization.instantiate_rootedTwo_iff, countEq]
        exact sourceRooted
    · intro bridge alignment
      cases siteData
      have dataEq := alignment.data_aligned
      unfold arityDataAligned at dataEq
      have headEq := bridge.data_selects
      unfold arityDataSelects at headEq
      refine ⟨RegionIso.ofEq ?_⟩
      simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
        Arity.operation, arityTargetOperation, retained, childApplication,
        childFrame, Transform.Frame.append, Region.renameWires,
        ItemSeq.renameWires, Item.renameWires, WireRenaming.appendRight]
      simp only [Var.appendMap_left, Var.appendMap_right]
      rw [dataEq, bridge.selected_commutes, headEq]
      congr 3
      rw [Arity.Vars.append_map, Arity.Vars.append_map,
        Arity.Vars.append_map]
      congr 1
      · simp only [Erasure.Exposure.Vars.map_map]
        apply Erasure.Exposure.Vars.map_congr application
        intro signature wire
        simp only [Var.appendMap_left]
        exact congrArg (fun mapped => mapped.appendLeft retained)
          ((alignment.keep_commutes wire).trans
            (bridge.keep_commutes wire).symm)
      · simp [Vars.map, Var.appendMap_right]

/-- The local-wire constructor is the remaining Arity completeness obligation. -/
theorem supportArityDerives
    {arguments : List Sig} {firstLocal : Sig} {locals : List Sig}
    (materialItems : ItemSeq (arguments ++ firstLocal :: locals))
    (materialCanonical :
      (Region.mk (firstLocal :: locals) materialItems :
        Region arguments).Canonical)
    (childDerives : SupportDerives
      (arityExposedMaterial arguments firstLocal locals materialItems))
    {structuralOuter structuralBefore structuralAfter : List Sig}
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel arguments :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (Region.mk (firstLocal :: locals) materialItems : Region arguments)
          materialCanonical)
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter arguments)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter arguments)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel arguments :: structuralAfter)
        items)) :
    request.Result := by
let structuralRequest := request
let childMaterial : Region (arguments ++ [firstLocal]) :=
  arityExposedMaterial arguments firstLocal locals materialItems
let childCanonical := arityExposedMaterial_canonical
  (arguments := arguments) (firstLocal := firstLocal) (locals := locals)
  materialItems materialCanonical
let childPattern := Erasure.Exposure.supportPattern childMaterial
  childCanonical
let arityData := Arity.targetHead structuralOuter structuralBefore
  structuralAfter arguments firstLocal
obtain ⟨aritySites⟩ := arityItemsSites_nonempty
  (pattern := Erasure.Exposure.supportPattern
    (Region.mk (firstLocal :: locals) materialItems : Region arguments)
    materialCanonical)
  (frame := Arity.rootFrame structuralOuter structuralBefore
    structuralAfter arguments firstLocal) (data := arityData) evidence
have rootArityScope := arityRootScope structuralOuter structuralBefore
  structuralAfter arguments firstLocal evidence aritySites
obtain ⟨retained, formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, semantic⟩ :=
  accumulateHostedTargetWith (targetArguments := arguments ++ [firstLocal])
    (targetExternal := arguments ++ [firstLocal])
    (targetInserted := [.rel (arguments ++ [firstLocal])])
    (targetPattern := childPattern)
    (targetBaseOperation := arityTargetOperation arguments firstLocal)
    evidence aritySites
    (Erasure.Exposure.identityBoundary (arguments ++ [firstLocal]))
    arityData ((Erasure.Exposure.identityBoundary arguments).map
      fun wire => wire.appendLeft [firstLocal])
    ScopePreservation ScopePreservation.refl
    (fun locals before after scope =>
      adjoinAt_preserves_scope locals .nil before after scope)
    ScopePreservation.conjoin
    ScopePreservation.cut
    (fun _ _ => True) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    arityDataSelects arityDataSelects_append
    arityDataAligned arityDataAligned_append
    (arityTargetNaturality arguments firstLocal)
    (fun _ => True) True.intro (by intros; trivial)
    (by
      intro itemCommon itemSourceWires itemTargetWires itemFrame itemData
        application siteData formalSourceWires formalTargetWires formalFrame
        formalData
      obtain ⟨retained, formalSource, formalResult, formalEvidence,
          formalSites, coherence, staged, selectedHosted, selectedScope,
          selectedPresentation, endpointPresentation⟩ :=
        aritySelectedTargetItem materialItems materialCanonical rfl application
          siteData formalFrame formalData
      exact ⟨retained, formalSource, formalResult, formalEvidence,
        formalSites, coherence, staged, selectedHosted, selectedScope,
        selectedPresentation, endpointPresentation, True.intro, True.intro⟩)
obtain ⟨staged, resultHosted, resultScope, stagedPresentation,
    endpointSemantic, _sourceSide, _retained⟩ := semantic
obtain ⟨stagedIso⟩ := stagedPresentation
let localRootFrame := Arity.rootFrame structuralOuter structuralBefore
  structuralAfter arguments firstLocal
let formalRootFrame := Transform.Frame.replace structuralOuter
  structuralBefore structuralAfter
    [.rel (arguments ++ [firstLocal])] (arguments ++ [firstLocal])
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
    (structuralOuter ++
      (structuralBefore ++ .rel (arguments ++ [firstLocal]) :: structuralAfter)) ++ retained =
      structuralOuter ++
        (structuralBefore ++ .rel (arguments ++ [firstLocal]) ::
          (structuralAfter ++ retained)) := by
  simp only [List.append_assoc, List.cons_append]
let sourceEquiv := WireEquiv.ofEq sourceWiresEq
let sourceRename := sourceEquiv.toRenaming
have sourceRename_index {signature}
    (wire : Var
      ((structuralOuter ++
          (structuralBefore ++ .rel (arguments ++ [firstLocal]) ::
            structuralAfter)) ++ retained)
        signature) :
    (sourceRename wire).index.val = wire.index.val := by
  exact WireEquiv.ofEq_index_val sourceWiresEq wire
let recursiveFrame := Transform.Frame.replace structuralOuter
  structuralBefore (structuralAfter ++ retained)
  [.rel (arguments ++ [firstLocal])] (arguments ++ [firstLocal])
let recursiveData := Transform.Frame.insertedHead structuralOuter
  structuralBefore (structuralAfter ++ retained)
    (.rel (arguments ++ [firstLocal]))
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
have dataCoherent : (arityTargetNaturality arguments firstLocal).Coherent
    (formalRootFrame.append retained)
    recursiveFrame
    ((arityTargetOperation arguments firstLocal).appendData
      formalRootFrame arityData retained)
    recursiveData commonRename sourceRename := by
  exact selectedCommutes
obtain ⟨recursiveSource, recursiveResult, recursiveEvidence,
    recursiveSites, recursiveSourceEq, recursiveArgumentEq,
    _recursiveSourceArgumentEq,
    ⟨recursiveResultIso⟩, ⟨recursiveEndpointIso⟩⟩ :=
  targetItemsReindex
    (baseOperation := arityTargetOperation arguments firstLocal)
    (external := arguments ++ [firstLocal]) (mappedFrame := recursiveFrame)
    (mappedData := recursiveData) formalEvidence formalSites
    (Erasure.Exposure.identityBoundary (arguments ++ [firstLocal]))
    (Erasure.Exposure.identityBoundary (arguments ++ [firstLocal]))
    (formalRootFrame.append retained) recursiveFrame
    commonRename sourceRename sourceRename sourceRename
    keepCommutes targetKeepCommutes selectedCommutes keepCommutes
    selectedCommutes
    (arityTargetNaturality arguments firstLocal) dataCoherent
let oldLocals := structuralBefore ++ structuralAfter
let newLocals := structuralBefore ++ (structuralAfter ++ retained)
let fullInstantiated := Region.adjoinAt oldLocals .nil result
let recursiveInstantiated := Region.adjoinAt newLocals .nil recursiveResult
let recursivePending : Region structuralOuter :=
  .mk (structuralBefore ++ .rel (arguments ++ [firstLocal]) ::
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
let preparedLocals := structuralBefore ++
  .rel (arguments ++ [firstLocal]) :: structuralAfter
let rawPrepared : Region structuralOuter :=
  Region.adjoinAt preparedLocals .nil
    (itemsEdit (operation := Arity.operation arguments firstLocal) arityData
      evidence aritySites).endpoint
have rawPreparedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context
  (.mk (structuralBefore ++ .rel arguments :: structuralAfter) items)
    rawPrepared
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
      (itemsEdit (operation := Arity.operation arguments firstLocal) arityData
        evidence aritySites).endpoint
      (.mk retained formalSource) := by
    change RegionIso (WireEquiv.refl (structuralOuter ++ preparedLocals))
      (Region.renameWires
        (WireEquiv.refl
          (structuralOuter ++ preparedLocals)).toRenaming
        (itemsEdit (operation := Arity.operation arguments firstLocal) arityData
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
    structuralBefore ++ .rel (arguments ++ [firstLocal]) ::
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
have childCompiled := childDerives childCanonical
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
