import VisualProof.Refinement.Implementation.CompilePartition
import VisualProof.Refinement.Implementation.IterationExtractionRegionContext
import VisualProof.Refinement.Implementation.IterationExtractionRegionLocal
import VisualProof.Refinement.Implementation.IterationExtractionRegionChild

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationExtractionOccurrence

noncomputable def extractionCompileNode_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
    (relationMap : RelationRenaming fragmentRels hostRels)
    (node : Fin layout.nodeCount)
    (bindersRelated : ∀ region binder arity
      (fragmentRelation : RelVar fragmentRels arity),
      (input.val.extractDiagramRaw selection layout).nodes node =
          .atom region binder →
      fragmentBinders binder = some ⟨arity, fragmentRelation⟩ →
      hostBinders (extractionBinderOrigin input selection layout binder) =
        some ⟨arity, relationMap fragmentRelation⟩)
    (fragmentItem : Item fragmentContext.length fragmentRels)
    (hostItem : Item hostContext.length hostRels)
    (fragmentCompiled : Concrete.Elaboration.compileNode?
      (input.val.extractDiagramRaw selection layout) fragmentContext
      fragmentBinders node = some fragmentItem)
    (hostCompiled : Concrete.Elaboration.compileNode? input.val hostContext
      hostBinders (selection.selectedNodes.get node) = some hostItem) :
    ItemIso (FiniteEquiv.refl (Fin hostContext.length)) hostRels hostItem
      ((fragmentItem.renameRelations relationMap).renameWires
        (extractionContextIndexMapOfMembership input selection layout
          fragmentContext hostContext membership)) := by
  let wireMap := extractionContextIndexMapOfMembership input selection layout
    fragmentContext hostContext membership
  have bindersMap : ∀ region binder,
      (input.val.extractDiagramRaw selection layout).nodes node =
          .atom region binder →
      hostBinders (extractionBinderOrigin input selection layout binder) =
        (fragmentBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩ := by
    intro region binder nodeEq
    cases relationEq : fragmentBinders binder with
    | none =>
        have impossible := fragmentCompiled
        unfold Concrete.Elaboration.compileNode? at impossible
        rw [nodeEq] at impossible
        simp [relationEq] at impossible
    | some relation =>
        rcases relation with ⟨arity, relation⟩
        simpa using bindersRelated region binder arity relation nodeEq relationEq
  have mapped := Concrete.Elaboration.compileNode?_map
    fragmentContext hostContext fragmentBinders hostBinders node
    (selection.selectedNodes.get node)
    (extractionRegionOrigin input selection layout)
    (extractionBinderOrigin input selection layout) wireMap relationMap
    (by
      have shape := extractionNode_shape input selection layout node
      rw [Concrete.Diagram.extractDiagramRaw_node] at shape
      cases nodeEq : (input.val.extractDiagramRaw selection layout).nodes node <;>
        rw [Concrete.Diagram.extractDiagramRaw_node] at nodeEq <;>
        rw [nodeEq] at shape <;> exact shape)
    (extractionResolvePort_mapOfMembership input selection layout
      fragmentContext hostContext membership hostNodup node)
    bindersMap
  rw [fragmentCompiled, hostCompiled] at mapped
  have itemEq : hostItem =
      (fragmentItem.renameWires wireMap).renameRelations relationMap := by
    exact Option.some.inj mapped
  rw [itemEq, Item.renameWires_renameRelations]
  exact ItemIso.refl _

noncomputable def extractionCompileRegion_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    ∀ {fragmentRels hostRels : RelCtx}
      (fragmentFuel hostFuel : Nat)
      (material : Fin layout.materialRegionCount)
      (fragmentContext : Concrete.Elaboration.WireContext
        (input.val.extractDiagramRaw selection layout))
      (hostContext : Concrete.Elaboration.WireContext input.val)
      (membership : ∀ wire,
        input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
          wire ∈ fragmentContext)
      (fragmentBinders : Concrete.Elaboration.BinderContext
        (input.val.extractDiagramRaw selection layout) fragmentRels)
      (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
      (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
        (input.val.extractDiagramRaw selection layout) fragmentBinders
        (layout.materialRegion material))
      (_hostEnumeration : Concrete.Elaboration.BinderContext.Enumeration
        input.val hostBinders (selection.selectedRegions.get material))
      (binderWitness : ExtractionBinderWitness input selection layout
        (layout.materialRegion material) (selection.selectedRegions.get material)
        fragmentBinders fragmentEnumeration hostBinders)
      (_fragmentExact :
        (fragmentContext.extend (layout.materialRegion material)).Exact
          (layout.materialRegion material))
      (_hostExact :
        (hostContext.extend (selection.selectedRegions.get material)).Exact
          (selection.selectedRegions.get material))
      (fragmentBody : Region fragmentContext.length fragmentRels)
      (hostBody : Region hostContext.length hostRels),
      Concrete.Elaboration.compileRegion?
          (input.val.extractDiagramRaw selection layout) fragmentFuel
          (layout.materialRegion material) fragmentContext fragmentBinders =
        some fragmentBody →
      Concrete.Elaboration.compileRegion? input.val hostFuel
          (selection.selectedRegions.get material) hostContext hostBinders =
        some hostBody →
      RegionIso (FiniteEquiv.refl (Fin hostContext.length)) hostRels
        hostBody
        ((fragmentBody.renameRelations binderWitness.relationMap).renameWires
          (extractionContextIndexMapOfMembership input selection layout
            fragmentContext hostContext membership)) := by
  intro fragmentRels hostRels fragmentFuel
  induction fragmentFuel generalizing fragmentRels hostRels with
  | zero =>
      intro hostFuel material fragmentContext hostContext membership
        fragmentBinders hostBinders fragmentEnumeration _hostEnumeration
        binderWitness _fragmentExact _hostExact fragmentBody hostBody
        fragmentCompiled hostCompiled
      simp [Concrete.Elaboration.compileRegion?] at fragmentCompiled
  | succ fragmentFuel induction =>
      intro hostFuel
      cases hostFuel with
      | zero =>
          intro material fragmentContext hostContext membership fragmentBinders
            hostBinders fragmentEnumeration _hostEnumeration binderWitness
            _fragmentExact _hostExact fragmentBody hostBody fragmentCompiled
            hostCompiled
          simp [Concrete.Elaboration.compileRegion?] at hostCompiled
      | succ hostFuel =>
          intro material fragmentContext hostContext membership fragmentBinders
            hostBinders fragmentEnumeration _hostEnumeration binderWitness
            _fragmentExact _hostExact fragmentBody hostBody fragmentCompiled
            hostCompiled
          let fragmentRegion := layout.materialRegion material
          let hostRegion := selection.selectedRegions.get material
          let fragmentExtended := fragmentContext.extend fragmentRegion
          let hostExtended := hostContext.extend hostRegion
          simp only [Concrete.Elaboration.compileRegion?] at fragmentCompiled hostCompiled
          change (do
              let items ← Concrete.Elaboration.compileOccurrencesWith?
                (input.val.extractDiagramRaw selection layout)
                (Concrete.Elaboration.compileRegion?
                  (input.val.extractDiagramRaw selection layout) fragmentFuel)
                fragmentExtended fragmentBinders
                (Concrete.Elaboration.localOccurrences
                  (input.val.extractDiagramRaw selection layout) fragmentRegion)
              pure (Concrete.Elaboration.finishRegion
                (input.val.extractDiagramRaw selection layout) fragmentContext
                fragmentRegion items)) = some fragmentBody at fragmentCompiled
          change (do
              let items ← Concrete.Elaboration.compileOccurrencesWith?
                input.val
                (Concrete.Elaboration.compileRegion? input.val hostFuel)
                hostExtended hostBinders
                (Concrete.Elaboration.localOccurrences input.val hostRegion)
              pure (Concrete.Elaboration.finishRegion input.val hostContext
                hostRegion items)) = some hostBody at hostCompiled
          cases fragmentItemsResult :
              Concrete.Elaboration.compileOccurrencesWith?
                (input.val.extractDiagramRaw selection layout)
                (Concrete.Elaboration.compileRegion?
                  (input.val.extractDiagramRaw selection layout) fragmentFuel)
                fragmentExtended fragmentBinders
                (Concrete.Elaboration.localOccurrences
                  (input.val.extractDiagramRaw selection layout)
                  fragmentRegion) with
          | none => simp [fragmentItemsResult] at fragmentCompiled
          | some fragmentItems =>
              simp [fragmentItemsResult] at fragmentCompiled
              subst fragmentBody
              cases hostItemsResult :
                  Concrete.Elaboration.compileOccurrencesWith? input.val
                    (Concrete.Elaboration.compileRegion? input.val hostFuel)
                    hostExtended hostBinders
                    (Concrete.Elaboration.localOccurrences input.val hostRegion) with
              | none => simp [hostItemsResult] at hostCompiled
              | some hostItems =>
                  simp [hostItemsResult] at hostCompiled
                  subst hostBody
                  let occurrenceMap := extractionHostOccurrenceMap input
                    selection layout
                  let mappedOccurrences :=
                    (Concrete.Elaboration.localOccurrences
                      (input.val.extractDiagramRaw selection layout)
                      fragmentRegion).map occurrenceMap
                  have mappedEach : ∀ hostOccurrence,
                      hostOccurrence ∈ mappedOccurrences →
                      ∃ item, Concrete.Elaboration.compileOccurrenceWith?
                        input.val
                        (Concrete.Elaboration.compileRegion? input.val hostFuel)
                        hostExtended hostBinders hostOccurrence = some item := by
                    intro hostOccurrence hostMember
                    simp only [mappedOccurrences, List.mem_map] at hostMember
                    obtain ⟨fragmentOccurrence, fragmentMember, rfl⟩ :=
                      hostMember
                    apply CompilePartition.compileOccurrence_success_of_mem
                      input.val
                      (Concrete.Elaboration.compileRegion? input.val hostFuel)
                      hostExtended hostBinders hostItemsResult
                    exact extractionHostOccurrenceMap_mem_local_material input
                      selection layout material fragmentOccurrence
                      fragmentMember
                  let mappedResult :=
                    Concrete.Elaboration.compileOccurrencesWith? input.val
                      (Concrete.Elaboration.compileRegion? input.val hostFuel)
                      hostExtended hostBinders mappedOccurrences
                  have mappedPresent : mappedResult.isSome := by
                    cases mappedResultEq : mappedResult with
                    | none =>
                        exfalso
                        obtain ⟨items, compiled⟩ :=
                          Concrete.Elaboration.compileOccurrencesWith?_complete
                            (Concrete.Elaboration.compileRegion? input.val
                              hostFuel)
                            hostExtended hostBinders mappedOccurrences mappedEach
                        have resultEq :
                            Concrete.Elaboration.compileOccurrencesWith?
                                input.val
                                (Concrete.Elaboration.compileRegion? input.val
                                  hostFuel)
                                hostExtended hostBinders mappedOccurrences =
                              none := by
                          simpa [mappedResult] using mappedResultEq
                        rw [resultEq] at compiled
                        contradiction
                    | some items => trivial
                  let mappedHostItems := mappedResult.get mappedPresent
                  have mappedHostItemsResult :
                      Concrete.Elaboration.compileOccurrencesWith? input.val
                          (Concrete.Elaboration.compileRegion? input.val hostFuel)
                          hostExtended hostBinders mappedOccurrences =
                        some mappedHostItems := by
                    change mappedResult = some mappedHostItems
                    exact Option.eq_some_of_isSome mappedPresent
                  let fragmentLength :=
                    Concrete.Elaboration.WireContext.length_extend fragmentContext
                      fragmentRegion
                  let hostLength :=
                    Concrete.Elaboration.WireContext.length_extend hostContext
                      hostRegion
                  let outerMap := extractionContextIndexMapOfMembership input
                    selection layout fragmentContext hostContext membership
                  let localEquiv := extractionMaterialLocalEquiv input selection
                    layout material
                  let forwardWire := Concrete.Elaboration.castFinEquiv rfl
                    hostLength
                    (extendWireEquiv
                      (FiniteEquiv.refl (Fin hostContext.length)) localEquiv)
                  have extendedMap := extractionContextIndexMap_extend input
                    selection layout fragmentContext hostContext membership
                    material _hostExact
                  have pullback : ∀
                      (fragmentItem : Item fragmentExtended.length fragmentRels)
                      (hostItem : Item hostExtended.length hostRels),
                      ItemIso (FiniteEquiv.refl (Fin hostExtended.length))
                        hostRels hostItem
                        ((fragmentItem.renameRelations
                          binderWitness.relationMap).renameWires
                            (extractionContextIndexMapOfMembership input
                              selection layout fragmentExtended hostExtended
                              (extractionContextMembership_extend_material input
                                selection layout fragmentContext hostContext
                                membership material))) →
                      ItemIso forwardWire.symm hostRels hostItem
                        (((fragmentItem.castWiresEq fragmentLength
                            ).renameRelations binderWitness.relationMap
                          ).renameWires
                            (extendWireRenaming outerMap
                              (Concrete.Elaboration.exactScopeWires
                                (input.val.extractDiagramRaw selection layout)
                                fragmentRegion).length)) := by
                    intro fragmentItem hostItem embedded
                    let prepared :=
                      ((fragmentItem.castWiresEq fragmentLength
                          ).renameRelations binderWitness.relationMap
                        ).renameWires
                          (extendWireRenaming outerMap
                            (Concrete.Elaboration.exactScopeWires
                              (input.val.extractDiagramRaw selection layout)
                              fragmentRegion).length)
                    have itemEq : prepared.renameWires forwardWire =
                        ((fragmentItem.renameRelations
                          binderWitness.relationMap).renameWires
                            (extractionContextIndexMapOfMembership input
                              selection layout fragmentExtended hostExtended
                              (extractionContextMembership_extend_material input
                                selection layout fragmentContext hostContext
                                membership material))) := by
                      simp only [prepared, Item.castWiresEq_eq_renameWires,
                        Item.renameWires_renameRelations,
                        Item.renameWires_comp]
                      rw [extendedMap]
                      rfl
                    rw [← itemEq] at embedded
                    have renamedBack := ItemIso.renameWiresEquiv
                      (prepared.renameWires forwardWire) forwardWire.symm
                    have backEq :
                        (prepared.renameWires forwardWire).renameWires
                            forwardWire.symm = prepared := by
                      rw [Item.renameWires_comp]
                      have inverse : forwardWire.symm.toFun ∘
                          forwardWire.toFun = id := by
                        funext index
                        exact forwardWire.left_inv index
                      rw [inverse, Item.renameWires_id]
                    rw [backEq] at renamedBack
                    simpa using embedded.trans renamedBack
                  let preparedItems :=
                    ((fragmentItems.castWiresEq fragmentLength
                        ).renameRelations binderWitness.relationMap
                      ).renameWires
                        (extendWireRenaming outerMap
                          (Concrete.Elaboration.exactScopeWires
                            (input.val.extractDiagramRaw selection layout)
                            fragmentRegion).length)
                  have fragmentCount :=
                    Concrete.Elaboration.compileOccurrencesWith?_length
                      (Concrete.Elaboration.compileRegion?
                        (input.val.extractDiagramRaw selection layout)
                        fragmentFuel) fragmentExtended fragmentBinders
                      fragmentItemsResult
                  have mappedCount :=
                    Concrete.Elaboration.compileOccurrencesWith?_length
                      (Concrete.Elaboration.compileRegion? input.val hostFuel)
                      hostExtended hostBinders mappedHostItemsResult
                  have itemCount : mappedHostItems.length =
                      preparedItems.length := by
                    simp only [preparedItems, ItemSeq.renameWires_length,
                      ItemSeq.renameRelations_length,
                      ItemSeq.castWiresEq_length]
                    rw [mappedCount, fragmentCount, List.length_map]
                    rfl
                  have alignedItems : ItemSeqIso forwardWire.symm hostRels
                      mappedHostItems preparedItems := by
                    refine ItemSeqIso.permute
                      (FiniteEquiv.finCast itemCount) ?_
                    intro hostIndex
                    let hostOccurrenceIndex := Fin.cast mappedCount hostIndex
                    let fragmentOccurrenceIndex : Fin
                        (Concrete.Elaboration.localOccurrences
                          (input.val.extractDiagramRaw selection layout)
                          fragmentRegion).length :=
                      Fin.cast (List.length_map occurrenceMap)
                        hostOccurrenceIndex
                    have hostGet :=
                      Concrete.Elaboration.compileOccurrencesWith?_get
                        (Concrete.Elaboration.compileRegion? input.val hostFuel)
                        hostExtended hostBinders mappedHostItemsResult
                        hostOccurrenceIndex
                    have fragmentGet :=
                      Concrete.Elaboration.compileOccurrencesWith?_get
                        (Concrete.Elaboration.compileRegion?
                          (input.val.extractDiagramRaw selection layout)
                          fragmentFuel) fragmentExtended fragmentBinders
                        fragmentItemsResult fragmentOccurrenceIndex
                    have occurrenceGet :
                        ((Concrete.Elaboration.localOccurrences
                          (input.val.extractDiagramRaw selection layout)
                          fragmentRegion).map occurrenceMap).get
                            hostOccurrenceIndex =
                          occurrenceMap
                            ((Concrete.Elaboration.localOccurrences
                              (input.val.extractDiagramRaw selection layout)
                              fragmentRegion).get fragmentOccurrenceIndex) := by
                      rw [List.get_eq_getElem, List.getElem_map]
                      congr 2
                    rw [occurrenceGet] at hostGet
                    have preparedGet : preparedItems.get
                          (FiniteEquiv.finCast itemCount hostIndex) =
                        ((((fragmentItems.get
                            (Fin.cast fragmentCount.symm
                              fragmentOccurrenceIndex)).castWiresEq
                              fragmentLength).renameRelations
                                binderWitness.relationMap).renameWires
                          (extendWireRenaming outerMap
                            (Concrete.Elaboration.exactScopeWires
                              (input.val.extractDiagramRaw selection layout)
                              fragmentRegion).length)) := by
                      let originalIndex := Fin.cast fragmentCount.symm
                        fragmentOccurrenceIndex
                      let castIndex := Fin.cast
                        (ItemSeq.castWiresEq_length fragmentLength
                          fragmentItems).symm originalIndex
                      let relationIndex := Fin.cast
                        (ItemSeq.renameRelations_length
                          (fragmentItems.castWiresEq fragmentLength)
                          binderWitness.relationMap).symm castIndex
                      let wireIndex :=
                        (fragmentItems.castWiresEq fragmentLength
                          |>.renameRelations binderWitness.relationMap
                          |>.renameWiresPositionEquiv
                            (extendWireRenaming outerMap
                              (Concrete.Elaboration.exactScopeWires
                                (input.val.extractDiagramRaw selection layout)
                                fragmentRegion).length)) relationIndex
                      have indexEq : FiniteEquiv.finCast itemCount hostIndex =
                          wireIndex := by
                        apply Fin.ext
                        rfl
                      rw [indexEq]
                      unfold preparedItems wireIndex relationIndex castIndex
                      rw [ItemSeq.get_renameWires,
                        ItemSeq.get_renameRelations,
                        ItemSeq.get_castWiresEq]
                    rw [preparedGet]
                    cases occurrenceEq :
                        (Concrete.Elaboration.localOccurrences
                          (input.val.extractDiagramRaw selection layout)
                          fragmentRegion).get fragmentOccurrenceIndex with
                    | node node =>
                        rw [occurrenceEq] at fragmentGet hostGet
                        apply pullback
                        apply extractionCompileNode_iso input selection layout
                          fragmentExtended hostExtended
                          (extractionContextMembership_extend_material input
                            selection layout fragmentContext hostContext membership
                            material) _hostExact.nodup fragmentBinders hostBinders
                          binderWitness.relationMap node
                        · intro region binder arity relation nodeShape lookup
                          have owner := fragmentEnumeration.lookup_owner relation
                            lookup
                          rw [← owner]
                          exact binderWitness.lookup relation
                        · exact fragmentGet
                        · exact hostGet
                    | child child =>
                        rw [occurrenceEq] at fragmentGet hostGet
                        have childMember :
                            Concrete.Elaboration.LocalOccurrence.child child ∈
                              Concrete.Elaboration.localOccurrences
                                (input.val.extractDiagramRaw selection layout)
                                fragmentRegion := by
                          rw [← occurrenceEq]
                          exact List.get_mem _ fragmentOccurrenceIndex
                        have childParent :=
                          (Concrete.Elaboration.mem_localOccurrences_child _ _ _).1
                            childMember
                        obtain ⟨childMaterial, childEq⟩ :=
                          materialDirectChild input selection layout material
                            child childParent
                        subst child
                        have mappedChild :=
                          extractionHostOccurrenceMap_materialChild input
                            selection layout childMaterial
                        dsimp only [occurrenceMap] at hostGet
                        have hostGet' :
                            Concrete.Elaboration.compileOccurrenceWith? input.val
                              (Concrete.Elaboration.compileRegion? input.val
                                hostFuel) hostExtended hostBinders
                              (.child (selection.selectedRegions.get
                                childMaterial)) =
                              some (mappedHostItems.get (Fin.cast
                                (Concrete.Elaboration.compileOccurrencesWith?_length
                                  (Concrete.Elaboration.compileRegion? input.val
                                    hostFuel) hostExtended hostBinders
                                  mappedHostItemsResult).symm
                                hostOccurrenceIndex)) := by
                          exact (congrArg (fun occurrence =>
                            Concrete.Elaboration.compileOccurrenceWith? input.val
                              (Concrete.Elaboration.compileRegion? input.val
                                hostFuel) hostExtended hostBinders occurrence)
                            mappedChild).symm.trans hostGet
                        cases fragmentKind :
                            (input.val.extractDiagramRaw selection layout).regions
                              (layout.materialRegion childMaterial) with
                        | sheet =>
                            simp [Concrete.Elaboration.compileOccurrenceWith?,
                              fragmentKind] at fragmentGet
                        | cut actualParent =>
                            have actualParentEq : actualParent = fragmentRegion := by
                              rw [fragmentKind] at childParent
                              exact Option.some.inj childParent
                            subst actualParent
                            have hostKind := extractionMaterialDirectChild_cut
                              input selection layout material
                              (layout.materialRegion childMaterial) fragmentKind
                            have hostKind' : input.val.regions
                                (selection.selectedRegions.get childMaterial) =
                              .cut hostRegion := by simpa using hostKind
                            have hostKindElem := hostKind'
                            simp only [List.get_eq_getElem] at hostKindElem
                            cases fragmentResult :
                                Concrete.Elaboration.compileRegion?
                                  (input.val.extractDiagramRaw selection layout)
                                  fragmentFuel
                                  (layout.materialRegion childMaterial)
                                  fragmentExtended fragmentBinders with
                            | none =>
                                simp [Concrete.Elaboration.compileOccurrenceWith?,
                                  fragmentKind, fragmentResult] at fragmentGet
                            | some fragmentChild =>
                                cases hostResult :
                                    Concrete.Elaboration.compileRegion? input.val
                                      hostFuel
                                      (selection.selectedRegions.get childMaterial)
                                      hostExtended hostBinders with
                                | none =>
                                    have hostResultElem := hostResult
                                    simp only [List.get_eq_getElem]
                                      at hostResultElem
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      hostKindElem, hostResultElem]
                                      at hostGet'
                                | some hostChild =>
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      fragmentKind, fragmentResult] at fragmentGet
                                    have hostResultElem := hostResult
                                    simp only [List.get_eq_getElem]
                                      at hostResultElem
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      hostKindElem, hostResultElem]
                                      at hostGet'
                                    have fragmentItemEq :
                                        fragmentItems.get
                                            (Fin.cast fragmentCount.symm
                                              fragmentOccurrenceIndex) =
                                          .cut fragmentChild := by
                                      exact fragmentGet.symm
                                    have hostItemEq :
                                        mappedHostItems.get hostIndex =
                                          .cut hostChild := by
                                      have getIndex : Fin.cast
                                          (Concrete.Elaboration.compileOccurrencesWith?_length
                                            (Concrete.Elaboration.compileRegion?
                                              input.val hostFuel) hostExtended
                                            hostBinders mappedHostItemsResult).symm
                                          hostOccurrenceIndex = hostIndex := by
                                        apply Fin.ext
                                        rfl
                                      rw [← getIndex]
                                      exact hostGet'.symm
                                    rw [hostItemEq, fragmentItemEq]
                                    apply pullback
                                    apply ItemIso.cut
                                    exact induction hostFuel childMaterial
                                      fragmentExtended hostExtended
                                      (extractionContextMembership_extend_material
                                        input selection layout fragmentContext
                                        hostContext membership material)
                                      fragmentBinders hostBinders
                                      (fragmentEnumeration.cutChild
                                        (Concrete.Diagram.extractDiagramRaw_wellFormed
                                          input selection layout) fragmentKind)
                                      (_hostEnumeration.cutChild input.property
                                        hostKind')
                                      (binderWitness.cutChild
                                        (layout.materialRegion childMaterial)
                                        (selection.selectedRegions.get childMaterial)
                                        fragmentKind hostKind')
                                      (_fragmentExact.extend_child
                                        (Concrete.Diagram.extractDiagramRaw_wellFormed
                                          input selection layout) childParent)
                                      (_hostExact.extend_child input.property
                                        (by simpa only [CRegion.parent?] using
                                          congrArg CRegion.parent? hostKind'))
                                      fragmentChild hostChild fragmentResult hostResult
                        | bubble actualParent arity =>
                            have actualParentEq : actualParent = fragmentRegion := by
                              rw [fragmentKind] at childParent
                              exact Option.some.inj childParent
                            subst actualParent
                            have hostKind := extractionMaterialDirectChild_bubble
                              input selection layout material
                              (layout.materialRegion childMaterial) arity
                              fragmentKind
                            have hostKind' : input.val.regions
                                (selection.selectedRegions.get childMaterial) =
                              .bubble hostRegion arity := by simpa using hostKind
                            have hostKindElem := hostKind'
                            simp only [List.get_eq_getElem] at hostKindElem
                            let fragmentPushed := fragmentBinders.push
                              (layout.materialRegion childMaterial) arity
                            let hostPushed := hostBinders.push
                              (selection.selectedRegions.get childMaterial) arity
                            cases fragmentResult :
                                Concrete.Elaboration.compileRegion?
                                  (input.val.extractDiagramRaw selection layout)
                                  fragmentFuel
                                  (layout.materialRegion childMaterial)
                                  fragmentExtended fragmentPushed with
                            | none =>
                                simp [Concrete.Elaboration.compileOccurrenceWith?,
                                  fragmentKind, fragmentPushed, fragmentResult]
                                  at fragmentGet
                            | some fragmentChild =>
                                cases hostResult :
                                    Concrete.Elaboration.compileRegion? input.val
                                      hostFuel
                                      (selection.selectedRegions.get childMaterial)
                                      hostExtended hostPushed with
                                | none =>
                                    have hostResultElem := hostResult
                                    dsimp only [hostPushed] at hostResultElem
                                    simp only [List.get_eq_getElem]
                                      at hostResultElem
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      hostKindElem,
                                      hostResultElem] at hostGet'
                                | some hostChild =>
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      fragmentKind, fragmentPushed,
                                      fragmentResult] at fragmentGet
                                    have hostResultElem := hostResult
                                    dsimp only [hostPushed] at hostResultElem
                                    simp only [List.get_eq_getElem]
                                      at hostResultElem
                                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                                      hostKindElem,
                                      hostResultElem] at hostGet'
                                    have fragmentItemEq :
                                        fragmentItems.get
                                            (Fin.cast fragmentCount.symm
                                              fragmentOccurrenceIndex) =
                                          .bubble arity fragmentChild := by
                                      exact fragmentGet.symm
                                    have hostItemEq :
                                        mappedHostItems.get hostIndex =
                                          .bubble arity hostChild := by
                                      have getIndex : Fin.cast
                                          (Concrete.Elaboration.compileOccurrencesWith?_length
                                            (Concrete.Elaboration.compileRegion?
                                              input.val hostFuel) hostExtended
                                            hostBinders mappedHostItemsResult).symm
                                          hostOccurrenceIndex = hostIndex := by
                                        apply Fin.ext
                                        rfl
                                      rw [← getIndex]
                                      exact hostGet'.symm
                                    rw [hostItemEq, fragmentItemEq]
                                    apply pullback
                                    apply ItemIso.bubble
                                    let childWitness := binderWitness.bubbleChild
                                      childMaterial arity fragmentKind hostKind'
                                    exact induction hostFuel childMaterial
                                      fragmentExtended hostExtended
                                      (extractionContextMembership_extend_material
                                        input selection layout fragmentContext
                                        hostContext membership material)
                                      fragmentPushed hostPushed
                                      (fragmentEnumeration.bubbleChild
                                        (Concrete.Diagram.extractDiagramRaw_wellFormed
                                          input selection layout) fragmentKind)
                                      (_hostEnumeration.bubbleChild input.property
                                        hostKind') childWitness
                                      (_fragmentExact.extend_child
                                        (Concrete.Diagram.extractDiagramRaw_wellFormed
                                          input selection layout) childParent)
                                      (_hostExact.extend_child input.property
                                        (by simpa only [CRegion.parent?] using
                                          congrArg CRegion.parent? hostKind'))
                                      fragmentChild hostChild fragmentResult hostResult
                  have occurrencePermutation :=
                    extractionHostOccurrenceMap_material_perm_host input
                      selection layout material
                  have hostOccurrencesNodup :=
                    Concrete.Elaboration.localOccurrences_nodup input.val
                      hostRegion
                  have mappedOccurrencesNodup :=
                    occurrencePermutation.nodup_iff.mpr hostOccurrencesNodup
                  have reorderedItems :=
                    CompilePartition.compileOccurrences_perm_iso input.val
                      (Concrete.Elaboration.compileRegion? input.val hostFuel)
                      hostExtended hostBinders occurrencePermutation
                      mappedOccurrencesNodup hostOccurrencesNodup
                      mappedHostItemsResult hostItemsResult
                  have hostAligned := reorderedItems.symm.trans alignedItems
                  apply Concrete.Elaboration.regionIso_of_cast hostLength rfl
                    (FiniteEquiv.refl (Fin hostContext.length)) localEquiv.symm
                    hostItems preparedItems
                  have wireEq :
                      (FiniteEquiv.refl (Fin hostExtended.length)).trans
                          forwardWire.symm =
                        Concrete.Elaboration.castFinEquiv hostLength rfl
                          (extendWireEquiv
                            (FiniteEquiv.refl (Fin hostContext.length))
                            localEquiv.symm) := by
                    apply FiniteEquiv.ext
                    intro wire
                    apply Fin.ext
                    rfl
                  rw [← wireEq]
                  exact hostAligned

end VisualProof.Refinement.Implementation.IterationExtraction
