import VisualProof.Refinement.Implementation.IterationExtractionCompiler
import VisualProof.Refinement.Implementation.CompilePartition
import VisualProof.Refinement.Implementation.IterationPartition

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition
open VisualProof.Refinement.Implementation.IterationExtractionOccurrence

theorem extractionTerminalDirectChild_cut
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (child : Fin layout.regionCount)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .cut layout.bodyContainer) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .cut selection.val.anchor := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some layout.bodyContainer := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := terminalChild_is_material input selection
    layout child childParent
  let original := selection.selectedRegions.get childIndex
  have selected : original ∈ selection.selectedRegions := List.get_mem _ _
  cases hostKind : input.val.regions original with
  | sheet =>
      exact False.elim (selectedRegion_ne_root input selection selected
        (input.property.only_root_is_sheet original hostKind))
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      have mapped : input.val.fragmentParent layout hostParent =
          layout.bodyContainer := CRegion.cut.inj kind
      have parentEq : (input.val.regions original).parent? = some hostParent := by
        rw [hostKind]
        rfl
      have parentAnchor := fragmentParent_body_of_selected_child_parent input
        selection layout selected parentEq mapped
      rw [extractionRegionOrigin_materialRegion, hostKind, parentAnchor]
  | bubble hostParent arity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent arity hostKind
      rw [fragmentKind] at kind
      contradiction

theorem extractionTerminalDirectChild_bubble
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (child : Fin layout.regionCount)
    (arity : Nat)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .bubble layout.bodyContainer arity) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .bubble selection.val.anchor arity := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some layout.bodyContainer := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := terminalChild_is_material input selection
    layout child childParent
  let original := selection.selectedRegions.get childIndex
  have selected : original ∈ selection.selectedRegions := List.get_mem _ _
  cases hostKind : input.val.regions original with
  | sheet =>
      exact False.elim (selectedRegion_ne_root input selection selected
        (input.property.only_root_is_sheet original hostKind))
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      contradiction
  | bubble hostParent hostArity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent hostArity hostKind
      rw [fragmentKind] at kind
      have equal := CRegion.bubble.inj kind
      have parentEq : (input.val.regions original).parent? = some hostParent := by
        rw [hostKind]
        rfl
      have parentAnchor := fragmentParent_body_of_selected_child_parent input
        selection layout selected parentEq equal.1
      rw [extractionRegionOrigin_materialRegion, hostKind, parentAnchor,
        equal.2]

noncomputable def extractionCompileSelectedItems_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {fragmentRels hostRels : RelCtx}
    (fragmentFuel hostFuel : Nat)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val hostBinders selection.val.anchor)
    (hostCover : hostBinders.Covers selection.val.anchor)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    (hostItems : ItemSeq hostContext.length hostRels)
    (fragmentCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (input.val.extractDiagramRaw selection layout)
      (Concrete.Elaboration.compileRegion?
        (input.val.extractDiagramRaw selection layout) fragmentFuel)
      fragmentContext fragmentBinders
      (Concrete.Elaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer) =
      some fragmentItems)
    (hostCompiled : Concrete.Elaboration.compileOccurrencesWith? input.val
      (Concrete.Elaboration.compileRegion? input.val hostFuel)
      hostContext hostBinders (selectedOccurrences input.val selection) =
      some hostItems) :
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      fragmentBinders fragmentEnumeration hostBinders hostCover
    ItemSeqIso (FiniteEquiv.refl (Fin hostContext.length)) hostRels hostItems
      ((fragmentItems.renameRelations binderWitness.relationMap).renameWires
        (extractionContextIndexMap input selection layout fragmentContext
          hostContext fragmentExact hostExact)) := by
  dsimp only
  let occurrenceMap := extractionHostOccurrenceMap input selection layout
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    fragmentBinders fragmentEnumeration hostBinders hostCover
  have membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext :=
    fragmentWireOrigin_mem_context_iff input selection layout fragmentContext
      hostContext fragmentExact hostExact
  let mappedOccurrences :=
    (Concrete.Elaboration.localOccurrences
      (input.val.extractDiagramRaw selection layout)
      layout.bodyContainer).map occurrenceMap
  have mappedEach : ∀ hostOccurrence, hostOccurrence ∈ mappedOccurrences →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val
        (Concrete.Elaboration.compileRegion? input.val hostFuel)
        hostContext hostBinders hostOccurrence = some item := by
    intro hostOccurrence hostMember
    apply CompilePartition.compileOccurrence_success_of_mem input.val
      (Concrete.Elaboration.compileRegion? input.val hostFuel)
      hostContext hostBinders hostCompiled
    exact (extractionHostOccurrenceMap_terminal_perm_selected input
      selection layout).mem_iff.mp (by
        simpa only [mappedOccurrences] using hostMember)
  let mappedResult := Concrete.Elaboration.compileOccurrencesWith? input.val
    (Concrete.Elaboration.compileRegion? input.val hostFuel)
    hostContext hostBinders mappedOccurrences
  have mappedPresent : mappedResult.isSome := by
    cases mappedResultEq : mappedResult with
    | none =>
        exfalso
        obtain ⟨items, compiled⟩ :=
          Concrete.Elaboration.compileOccurrencesWith?_complete
            (Concrete.Elaboration.compileRegion? input.val hostFuel)
            hostContext hostBinders mappedOccurrences mappedEach
        have resultEq : Concrete.Elaboration.compileOccurrencesWith? input.val
            (Concrete.Elaboration.compileRegion? input.val hostFuel)
            hostContext hostBinders mappedOccurrences = none := by
          simpa only [mappedResult] using mappedResultEq
        rw [resultEq] at compiled
        contradiction
    | some items => trivial
  let mappedHostItems := mappedResult.get mappedPresent
  have mappedHostCompiled : Concrete.Elaboration.compileOccurrencesWith?
      input.val (Concrete.Elaboration.compileRegion? input.val hostFuel)
      hostContext hostBinders mappedOccurrences = some mappedHostItems := by
    change mappedResult = some mappedHostItems
    exact Option.eq_some_of_isSome mappedPresent
  let preparedItems :=
    (fragmentItems.renameRelations binderWitness.relationMap).renameWires
      (extractionContextIndexMap input selection layout fragmentContext
        hostContext fragmentExact hostExact)
  have fragmentCount :=
    Concrete.Elaboration.compileOccurrencesWith?_length
      (Concrete.Elaboration.compileRegion?
        (input.val.extractDiagramRaw selection layout) fragmentFuel)
      fragmentContext fragmentBinders fragmentCompiled
  have mappedCount :=
    Concrete.Elaboration.compileOccurrencesWith?_length
      (Concrete.Elaboration.compileRegion? input.val hostFuel)
      hostContext hostBinders mappedHostCompiled
  have itemCount : mappedHostItems.length = preparedItems.length := by
    simp only [preparedItems, ItemSeq.renameWires_length,
      ItemSeq.renameRelations_length]
    rw [mappedCount, fragmentCount, List.length_map]
    rfl
  have alignedItems : ItemSeqIso
      (FiniteEquiv.refl (Fin hostContext.length)) hostRels
      mappedHostItems preparedItems := by
    refine ItemSeqIso.permute (FiniteEquiv.finCast itemCount) ?_
    intro hostIndex
    let hostOccurrenceIndex := Fin.cast mappedCount hostIndex
    let fragmentOccurrenceIndex : Fin
        (Concrete.Elaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout)
          layout.bodyContainer).length :=
      Fin.cast (List.length_map occurrenceMap) hostOccurrenceIndex
    have hostGet := Concrete.Elaboration.compileOccurrencesWith?_get
      (Concrete.Elaboration.compileRegion? input.val hostFuel)
      hostContext hostBinders mappedHostCompiled hostOccurrenceIndex
    have fragmentGet := Concrete.Elaboration.compileOccurrencesWith?_get
      (Concrete.Elaboration.compileRegion?
        (input.val.extractDiagramRaw selection layout) fragmentFuel)
      fragmentContext fragmentBinders fragmentCompiled
      fragmentOccurrenceIndex
    have occurrenceGet :
        ((Concrete.Elaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout)
          layout.bodyContainer).map occurrenceMap).get hostOccurrenceIndex =
        occurrenceMap ((Concrete.Elaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout)
          layout.bodyContainer).get fragmentOccurrenceIndex) := by
      rw [List.get_eq_getElem, List.getElem_map]
      congr 2
    rw [occurrenceGet] at hostGet
    have preparedGet : preparedItems.get
        (FiniteEquiv.finCast itemCount hostIndex) =
      (((fragmentItems.get
          (Fin.cast fragmentCount.symm fragmentOccurrenceIndex)
        ).renameRelations binderWitness.relationMap).renameWires
          (extractionContextIndexMap input selection layout fragmentContext
            hostContext fragmentExact hostExact)) := by
      let originalIndex := Fin.cast fragmentCount.symm fragmentOccurrenceIndex
      let relationIndex := Fin.cast
        (ItemSeq.renameRelations_length fragmentItems
          binderWitness.relationMap).symm originalIndex
      let wireIndex :=
        (fragmentItems.renameRelations binderWitness.relationMap
          |>.renameWiresPositionEquiv
            (extractionContextIndexMap input selection layout fragmentContext
              hostContext fragmentExact hostExact)) relationIndex
      have indexEq : FiniteEquiv.finCast itemCount hostIndex = wireIndex := by
        apply Fin.ext
        rfl
      rw [indexEq]
      unfold preparedItems wireIndex relationIndex
      rw [ItemSeq.get_renameWires, ItemSeq.get_renameRelations]
    rw [preparedGet]
    cases occurrenceEq :
        (Concrete.Elaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout)
          layout.bodyContainer).get fragmentOccurrenceIndex with
    | node node =>
        rw [occurrenceEq] at fragmentGet hostGet
        apply extractionCompileNode_iso input selection layout fragmentContext
          hostContext membership hostExact.nodup fragmentBinders hostBinders
          binderWitness.relationMap node
        · intro region binder arity relation nodeShape lookup
          have owner := fragmentEnumeration.lookup_owner relation lookup
          rw [← owner]
          exact binderWitness.lookup relation
        · exact fragmentGet
        · exact hostGet
    | child child =>
        rw [occurrenceEq] at fragmentGet hostGet
        have childMember : Concrete.Elaboration.LocalOccurrence.child child ∈
            Concrete.Elaboration.localOccurrences
              (input.val.extractDiagramRaw selection layout)
              layout.bodyContainer := by
          rw [← occurrenceEq]
          exact List.get_mem _ fragmentOccurrenceIndex
        have childParent :=
          (Concrete.Elaboration.mem_localOccurrences_child _ _ _).1 childMember
        obtain ⟨childMaterial, childEq⟩ := terminalChild input selection
          layout child childParent
        subst child
        have mappedChild := extractionHostOccurrenceMap_materialChild input
          selection layout childMaterial
        dsimp only [occurrenceMap] at hostGet
        have hostGet' : Concrete.Elaboration.compileOccurrenceWith? input.val
            (Concrete.Elaboration.compileRegion? input.val hostFuel)
            hostContext hostBinders
            (.child (selection.selectedRegions.get childMaterial)) =
          some (mappedHostItems.get (Fin.cast
            (Concrete.Elaboration.compileOccurrencesWith?_length
              (Concrete.Elaboration.compileRegion? input.val hostFuel)
              hostContext hostBinders mappedHostCompiled).symm
            hostOccurrenceIndex)) := by
          exact (congrArg (fun occurrence =>
            Concrete.Elaboration.compileOccurrenceWith? input.val
              (Concrete.Elaboration.compileRegion? input.val hostFuel)
              hostContext hostBinders occurrence) mappedChild).symm.trans hostGet
        cases fragmentKind :
            (input.val.extractDiagramRaw selection layout).regions
              (layout.materialRegion childMaterial) with
        | sheet =>
            simp [Concrete.Elaboration.compileOccurrenceWith?, fragmentKind]
              at fragmentGet
        | cut actualParent =>
            have actualParentEq : actualParent = layout.bodyContainer := by
              rw [fragmentKind] at childParent
              exact Option.some.inj childParent
            subst actualParent
            have hostKind := extractionTerminalDirectChild_cut input selection
              layout (layout.materialRegion childMaterial) fragmentKind
            have hostKind' : input.val.regions
                (selection.selectedRegions.get childMaterial) =
              .cut selection.val.anchor := by simpa using hostKind
            have hostKindElem := hostKind'
            simp only [List.get_eq_getElem] at hostKindElem
            cases fragmentResult : Concrete.Elaboration.compileRegion?
                (input.val.extractDiagramRaw selection layout) fragmentFuel
                (layout.materialRegion childMaterial) fragmentContext
                fragmentBinders with
            | none =>
                simp [Concrete.Elaboration.compileOccurrenceWith?, fragmentKind,
                  fragmentResult] at fragmentGet
            | some fragmentChild =>
                cases hostResult : Concrete.Elaboration.compileRegion?
                    input.val hostFuel
                    (selection.selectedRegions.get childMaterial)
                    hostContext hostBinders with
                | none =>
                    have hostResultElem := hostResult
                    simp only [List.get_eq_getElem] at hostResultElem
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      hostKindElem, hostResultElem] at hostGet'
                | some hostChild =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      fragmentKind, fragmentResult] at fragmentGet
                    have hostResultElem := hostResult
                    simp only [List.get_eq_getElem] at hostResultElem
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      hostKindElem, hostResultElem] at hostGet'
                    have fragmentItemEq : fragmentItems.get
                        (Fin.cast fragmentCount.symm fragmentOccurrenceIndex) =
                      .cut fragmentChild := fragmentGet.symm
                    have hostItemEq : mappedHostItems.get hostIndex =
                        .cut hostChild := by
                      have getIndex : Fin.cast
                          (Concrete.Elaboration.compileOccurrencesWith?_length
                            (Concrete.Elaboration.compileRegion? input.val
                              hostFuel) hostContext hostBinders
                            mappedHostCompiled).symm hostOccurrenceIndex =
                        hostIndex := by
                        apply Fin.ext
                        rfl
                      rw [← getIndex]
                      exact hostGet'.symm
                    rw [hostItemEq, fragmentItemEq]
                    apply ItemIso.cut
                    exact extractionCompileRegion_iso input selection layout
                      fragmentFuel hostFuel childMaterial fragmentContext
                      hostContext membership fragmentBinders hostBinders
                      (fragmentEnumeration.cutChild
                        (Concrete.Diagram.extractDiagramRaw_wellFormed input
                          selection layout) fragmentKind)
                      (hostEnumeration.cutChild input.property hostKind')
                      (binderWitness.cutChild
                        (layout.materialRegion childMaterial)
                        (selection.selectedRegions.get childMaterial)
                        fragmentKind hostKind')
                      (fragmentExact.extend_child
                        (Concrete.Diagram.extractDiagramRaw_wellFormed input
                          selection layout) childParent)
                      (hostExact.extend_child input.property
                        (by simpa only [CRegion.parent?] using
                          congrArg CRegion.parent? hostKind'))
                      fragmentChild hostChild fragmentResult hostResult
        | bubble actualParent arity =>
            have actualParentEq : actualParent = layout.bodyContainer := by
              rw [fragmentKind] at childParent
              exact Option.some.inj childParent
            subst actualParent
            have hostKind := extractionTerminalDirectChild_bubble input
              selection layout (layout.materialRegion childMaterial) arity
              fragmentKind
            have hostKind' : input.val.regions
                (selection.selectedRegions.get childMaterial) =
              .bubble selection.val.anchor arity := by simpa using hostKind
            have hostKindElem := hostKind'
            simp only [List.get_eq_getElem] at hostKindElem
            let fragmentPushed := fragmentBinders.push
              (layout.materialRegion childMaterial) arity
            let hostPushed := hostBinders.push
              (selection.selectedRegions.get childMaterial) arity
            cases fragmentResult : Concrete.Elaboration.compileRegion?
                (input.val.extractDiagramRaw selection layout) fragmentFuel
                (layout.materialRegion childMaterial) fragmentContext
                fragmentPushed with
            | none =>
                simp [Concrete.Elaboration.compileOccurrenceWith?, fragmentKind,
                  fragmentPushed, fragmentResult] at fragmentGet
            | some fragmentChild =>
                cases hostResult : Concrete.Elaboration.compileRegion?
                    input.val hostFuel
                    (selection.selectedRegions.get childMaterial)
                    hostContext hostPushed with
                | none =>
                    have hostResultElem := hostResult
                    dsimp only [hostPushed] at hostResultElem
                    simp only [List.get_eq_getElem] at hostResultElem
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      hostKindElem, hostResultElem] at hostGet'
                | some hostChild =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      fragmentKind, fragmentPushed, fragmentResult]
                      at fragmentGet
                    have hostResultElem := hostResult
                    dsimp only [hostPushed] at hostResultElem
                    simp only [List.get_eq_getElem] at hostResultElem
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      hostKindElem, hostResultElem] at hostGet'
                    have fragmentItemEq : fragmentItems.get
                        (Fin.cast fragmentCount.symm fragmentOccurrenceIndex) =
                      .bubble arity fragmentChild := fragmentGet.symm
                    have hostItemEq : mappedHostItems.get hostIndex =
                        .bubble arity hostChild := by
                      have getIndex : Fin.cast
                          (Concrete.Elaboration.compileOccurrencesWith?_length
                            (Concrete.Elaboration.compileRegion? input.val
                              hostFuel) hostContext hostBinders
                            mappedHostCompiled).symm hostOccurrenceIndex =
                        hostIndex := by
                        apply Fin.ext
                        rfl
                      rw [← getIndex]
                      exact hostGet'.symm
                    rw [hostItemEq, fragmentItemEq]
                    apply ItemIso.bubble
                    let childWitness := binderWitness.bubbleChild childMaterial
                      arity fragmentKind hostKind'
                    exact extractionCompileRegion_iso input selection layout
                      fragmentFuel hostFuel childMaterial fragmentContext
                      hostContext membership fragmentPushed hostPushed
                      (fragmentEnumeration.bubbleChild
                        (Concrete.Diagram.extractDiagramRaw_wellFormed input
                          selection layout) fragmentKind)
                      (hostEnumeration.bubbleChild input.property hostKind')
                      childWitness
                      (fragmentExact.extend_child
                        (Concrete.Diagram.extractDiagramRaw_wellFormed input
                          selection layout) childParent)
                      (hostExact.extend_child input.property
                        (by simpa only [CRegion.parent?] using
                          congrArg CRegion.parent? hostKind'))
                      fragmentChild hostChild fragmentResult hostResult
  have occurrencePermutation :=
    extractionHostOccurrenceMap_terminal_perm_selected input selection layout
  have selectedNodup : (selectedOccurrences input.val selection).Nodup :=
    List.filter_sublist.nodup
      (Concrete.Elaboration.localOccurrences_nodup input.val
        selection.val.anchor)
  have mappedNodup := occurrencePermutation.nodup_iff.mpr selectedNodup
  have reorderedItems := CompilePartition.compileOccurrences_perm_iso
    input.val (Concrete.Elaboration.compileRegion? input.val hostFuel)
    hostContext hostBinders occurrencePermutation mappedNodup selectedNodup
    mappedHostCompiled hostCompiled
  simpa only [preparedItems] using reorderedItems.symm.trans alignedItems

end VisualProof.Refinement.Implementation.IterationExtraction
