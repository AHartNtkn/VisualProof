import VisualProof.Rule.Soundness.Iteration.ExtractionRegionSemantic

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A copied direct cut in the extracted terminal body has the corresponding
direct cut shape at the selection anchor. -/
theorem extractionTerminalDirectChild_cut
    (input : CheckedDiagram signature)
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

/-- A copied direct bubble in the extracted terminal body has the corresponding
direct bubble shape and arity at the selection anchor. -/
theorem extractionTerminalDirectChild_bubble
    (input : CheckedDiagram signature)
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

/-- A valuation of the complete host anchor context canonically supplies the
local witnesses of the extracted terminal body while preserving every given
ambient value. -/
theorem extractionTerminalExtendedEnvironmentsAgree_backward
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentExact :
      (fragmentContext.extend layout.bodyContainer).Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentOuter : Fin fragmentContext.length → D)
    (hostEnv : Fin hostContext.length → D)
    (outerAgrees :
      (extractionContextRelation input selection layout fragmentContext
        hostContext).EnvironmentsAgree fragmentOuter hostEnv) :
    ∃ fragmentLocal : Fin (ConcreteElaboration.exactScopeWires
        (input.val.extractDiagramRaw selection layout)
        layout.bodyContainer).length → D,
      (extractionContextRelation input selection layout
        (fragmentContext.extend layout.bodyContainer) hostContext
      ).EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment fragmentContext
          layout.bodyContainer fragmentOuter fragmentLocal)
        hostEnv := by
  let fragmentExtended := fragmentContext.extend layout.bodyContainer
  let fullMap := extractionContextIndexMap input selection layout
    fragmentExtended hostContext fragmentExact hostExact
  let fragmentLocal : Fin (ConcreteElaboration.exactScopeWires
      (input.val.extractDiagramRaw selection layout)
      layout.bodyContainer).length → D :=
    fun index => hostEnv
      (fullMap (extendedLocalIndex fragmentContext layout.bodyContainer index))
  refine ⟨fragmentLocal, ?_⟩
  intro fragmentIndex hostIndex related
  rcases extendedIndex_cases fragmentContext layout.bodyContainer fragmentIndex with
    ⟨outerIndex, rfl⟩ | ⟨localIndex, rfl⟩
  · rw [extendedEnvironment_outer]
    apply outerAgrees outerIndex hostIndex
    unfold extractionContextRelation at related ⊢
    have outerGet : (fragmentContext.extend layout.bodyContainer).get
        (fragmentContext.outerIndex layout.bodyContainer outerIndex) =
        fragmentContext.get outerIndex := by
      simpa only [List.get_eq_getElem] using
        ConcreteElaboration.WireContext.extend_outer fragmentContext
          layout.bodyContainer outerIndex
    exact (congrArg (input.val.fragmentWireOrigin selection layout)
      outerGet).symm.trans related
  · rw [extendedEnvironment_local]
    change hostEnv (fullMap
      (extendedLocalIndex fragmentContext layout.bodyContainer localIndex)) =
      hostEnv hostIndex
    apply congrArg hostEnv
    apply Fin.ext
    apply (List.getElem_inj hostExact.nodup).mp
    have chosen := extractionContextIndexMap_spec input selection layout
      fragmentExtended hostContext fragmentExact hostExact
      (extendedLocalIndex fragmentContext layout.bodyContainer localIndex)
    unfold extractionContextRelation at chosen related
    exact chosen.symm.trans related

/-- The recursive extraction compiler transports the complete selected
occurrence block from any exact extracted context at the terminal container.
Keeping this item-sequence kernel separate permits both the nested terminal
presentation and the zero-spine open-root presentation to use one proof. -/
theorem extractionCompileSelectedItems_denote
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {fragmentRels hostRels : RelCtx}
    (fragmentFuel hostFuel : Nat)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val hostBinders selection.val.anchor)
    (hostCover : hostBinders.Covers selection.val.anchor)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentItems : ItemSeq signature fragmentContext.length fragmentRels)
    (hostItems : ItemSeq signature hostContext.length hostRels)
    (fragmentCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (input.val.extractDiagramRaw selection layout)
        (ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout) fragmentFuel)
        fragmentContext fragmentBinders
        (ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer) =
        some fragmentItems)
    (hostCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        hostContext hostBinders (selectedOccurrences input.val selection) =
        some hostItems) :
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      fragmentBinders fragmentEnumeration hostBinders hostCover
    ConcreteElaboration.ItemSeqSimulation model named .backward
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      (fragmentItems.renameRelations binderWitness.relationMap) hostItems := by
  dsimp only
  let occurrenceMap := extractionHostOccurrenceMap input selection layout
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    fragmentBinders fragmentEnumeration hostBinders hostCover
  have membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext := by
    exact fragmentWireOrigin_mem_context_iff input selection layout
      fragmentContext hostContext fragmentExact hostExact
  obtain ⟨mappedHostItems, mappedHostCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete
      (ConcreteElaboration.compileRegion? signature input.val hostFuel)
      hostContext hostBinders
      ((ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout)
        layout.bodyContainer).map occurrenceMap)
      (by
        intro hostOccurrence hostMember
        apply ModalSoundness.compileOccurrence_success_of_mem input.val
          (ConcreteElaboration.compileRegion? signature input.val hostFuel)
          hostContext hostBinders hostCompiled
        exact (extractionHostOccurrenceMap_terminal_perm_selected input
          selection layout).mem_iff.mp hostMember)
  have mappedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      .backward
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      (fragmentItems.renameRelations binderWitness.relationMap)
      mappedHostItems := by
    apply
      ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
        model named .backward
        (ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout) fragmentFuel)
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        fragmentContext hostContext fragmentBinders hostBinders
        (extractionContextRelation input selection layout fragmentContext
          hostContext)
        binderWitness.relationMap occurrenceMap
        (ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer)
    · intro occurrence occurrenceMember fragmentItem hostItem
        fragmentOccurrenceCompiled hostOccurrenceCompiled
      cases occurrence with
      | node node =>
          apply extractionCompileNode_itemSimulationOfMembership input selection
            layout model named .backward fragmentContext hostContext membership
            hostExact.nodup fragmentBinders hostBinders
            binderWitness.relationMap node
          · intro region binder arity relation nodeShape lookup
            have owner := fragmentEnumeration.lookup_owner relation lookup
            rw [← owner]
            exact binderWitness.lookup relation
          · exact fragmentOccurrenceCompiled
          · exact hostOccurrenceCompiled
      | child child =>
          have childParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
              occurrenceMember
          obtain ⟨childMaterial, childEq⟩ := terminalChild_is_material input
            selection layout child childParent
          subst child
          dsimp only [occurrenceMap] at hostOccurrenceCompiled
          have mappedChild := extractionHostOccurrenceMap_materialChild
            (signature := signature) input selection layout childMaterial
          have hostOccurrenceCompiled' :
              ConcreteElaboration.compileOccurrenceWith? signature input.val
                (ConcreteElaboration.compileRegion? signature input.val hostFuel)
                hostContext hostBinders
                (.child (selection.selectedRegions.get childMaterial)) =
                  some hostItem := by
            exact (congrArg (fun occurrence =>
              ConcreteElaboration.compileOccurrenceWith? signature input.val
                (ConcreteElaboration.compileRegion? signature input.val hostFuel)
                hostContext hostBinders occurrence) mappedChild).symm.trans
              hostOccurrenceCompiled
          cases fragmentKind :
              (input.val.extractDiagramRaw selection layout).regions
                (layout.materialRegion childMaterial) with
          | sheet =>
              simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind]
                at fragmentOccurrenceCompiled
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
              unfold ConcreteElaboration.compileOccurrenceWith?
                at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              rw [hostKind'] at hostOccurrenceCompiled'
              cases fragmentResult :
                  ConcreteElaboration.compileRegion? signature
                    (input.val.extractDiagramRaw selection layout) fragmentFuel
                    (layout.materialRegion childMaterial) fragmentContext
                    fragmentBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentResult] at fragmentOccurrenceCompiled
              | some fragmentChild =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentResult] at fragmentOccurrenceCompiled
                  subst fragmentItem
                  cases hostResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        hostFuel (selection.selectedRegions.get childMaterial)
                        hostContext hostBinders with
                  | none =>
                      have hostResult' := hostResult
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                  | some hostChild =>
                      have hostResult' := hostResult
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                      subst hostItem
                      have bodies := extractionCompileRegion_material_denote
                        input selection layout model named .forward fragmentFuel
                        hostFuel childMaterial fragmentContext hostContext
                        membership fragmentBinders hostBinders
                        (fragmentEnumeration.cutChild
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) fragmentKind)
                        (hostEnumeration.cutChild input.property hostKind')
                        (binderWitness.cutChild
                          (layout.materialRegion childMaterial)
                          (selection.selectedRegions.get childMaterial)
                          fragmentKind hostKind')
                        (fragmentExact.extend_child
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) childParent)
                        (hostExact.extend_child input.property
                          (by simpa only [CRegion.parent?] using
                            congrArg CRegion.parent? hostKind'))
                        fragmentChild hostChild fragmentResult hostResult
                      intro fragmentEnv hostEnv relEnv environments hostNot
                        fragmentDenotes
                      exact hostNot (bodies fragmentEnv hostEnv relEnv
                        environments fragmentDenotes)
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
              unfold ConcreteElaboration.compileOccurrenceWith?
                at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              rw [hostKind'] at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              let fragmentPushed := fragmentBinders.push
                (layout.materialRegion childMaterial) arity
              let hostPushed := hostBinders.push
                (selection.selectedRegions.get childMaterial) arity
              cases fragmentResult :
                  ConcreteElaboration.compileRegion? signature
                    (input.val.extractDiagramRaw selection layout) fragmentFuel
                    (layout.materialRegion childMaterial) fragmentContext
                    fragmentPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentPushed, fragmentResult] at fragmentOccurrenceCompiled
              | some fragmentChild =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentPushed, fragmentResult] at fragmentOccurrenceCompiled
                  subst fragmentItem
                  cases hostResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        hostFuel (selection.selectedRegions.get childMaterial)
                        hostContext hostPushed with
                  | none =>
                      have hostResult' := hostResult
                      dsimp only [hostPushed] at hostResult'
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                  | some hostChild =>
                      have hostResult' := hostResult
                      dsimp only [hostPushed] at hostResult'
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                      subst hostItem
                      let childWitness := binderWitness.bubbleChild childMaterial
                        arity fragmentKind hostKind'
                      have bodies := extractionCompileRegion_material_denote
                        input selection layout model named .backward fragmentFuel
                        hostFuel childMaterial fragmentContext hostContext
                        membership fragmentPushed hostPushed
                        (fragmentEnumeration.bubbleChild
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) fragmentKind)
                        (hostEnumeration.bubbleChild input.property hostKind')
                        childWitness
                        (fragmentExact.extend_child
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) childParent)
                        (hostExact.extend_child input.property
                          (by simpa only [CRegion.parent?] using
                            congrArg CRegion.parent? hostKind'))
                        fragmentChild hostChild fragmentResult hostResult
                      intro fragmentEnv hostEnv relEnv environments
                      rintro ⟨relationValue, hostDenotes⟩
                      exact ⟨relationValue, bodies fragmentEnv hostEnv
                        (relationValue, relEnv) environments hostDenotes⟩
    · exact fragmentCompiled
    · exact mappedHostCompiled
  intro fragmentEnv hostEnv relEnv environments hostDenotes
  apply mappedSimulation fragmentEnv hostEnv relEnv environments
  exact (ModalSoundness.compileOccurrences_denote_perm input.val
    (ConcreteElaboration.compileRegion? signature input.val hostFuel)
    hostContext hostBinders
    (extractionHostOccurrenceMap_terminal_perm_selected input selection layout)
    mappedHostCompiled hostCompiled model named hostEnv relEnv).mpr hostDenotes

/-- The selected anchor block entails the extracted terminal material.  This
is the compiler-level copy law consumed by iteration contraction. -/
theorem extractionCompileTerminal_selected_denote
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {fragmentRels hostRels : RelCtx}
    (fragmentFuel hostFuel : Nat)
    (fragmentContext : ConcreteElaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : ConcreteElaboration.WireContext input.val)
    (fragmentBinders : ConcreteElaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (hostEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val hostBinders selection.val.anchor)
    (hostCover : hostBinders.Covers selection.val.anchor)
    (fragmentExact :
      (fragmentContext.extend layout.bodyContainer).Exact layout.bodyContainer)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentItems : ItemSeq signature
      (fragmentContext.extend layout.bodyContainer).length fragmentRels)
    (hostItems : ItemSeq signature hostContext.length hostRels)
    (fragmentCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (input.val.extractDiagramRaw selection layout)
        (ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout) fragmentFuel)
        (fragmentContext.extend layout.bodyContainer) fragmentBinders
        (ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer) =
        some fragmentItems)
    (hostCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        hostContext hostBinders (selectedOccurrences input.val selection) =
        some hostItems) :
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      fragmentBinders fragmentEnumeration hostBinders hostCover
    ConcreteElaboration.RegionSimulation model named .backward
      (extractionContextRelation input selection layout fragmentContext
        hostContext)
      ((ConcreteElaboration.finishRegion
          (input.val.extractDiagramRaw selection layout) fragmentContext
          layout.bodyContainer fragmentItems).renameRelations
        binderWitness.relationMap)
      (Region.mk 0 hostItems) := by
  dsimp only
  let fragmentExtended := fragmentContext.extend layout.bodyContainer
  let occurrenceMap := extractionHostOccurrenceMap input selection layout
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    fragmentBinders fragmentEnumeration hostBinders hostCover
  have fullMembership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentExtended := by
    exact fragmentWireOrigin_mem_context_iff input selection layout
      fragmentExtended hostContext fragmentExact hostExact
  obtain ⟨mappedHostItems, mappedHostCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete
      (ConcreteElaboration.compileRegion? signature input.val hostFuel)
      hostContext hostBinders
      ((ConcreteElaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout)
        layout.bodyContainer).map occurrenceMap)
      (by
        intro hostOccurrence hostMember
        apply ModalSoundness.compileOccurrence_success_of_mem input.val
          (ConcreteElaboration.compileRegion? signature input.val hostFuel)
          hostContext hostBinders hostCompiled
        exact (extractionHostOccurrenceMap_terminal_perm_selected input
          selection layout).mem_iff.mp hostMember)
  have mappedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      .backward
      (extractionContextRelation input selection layout fragmentExtended
        hostContext)
      (fragmentItems.renameRelations binderWitness.relationMap)
      mappedHostItems := by
    apply
      ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
        model named .backward
        (ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout) fragmentFuel)
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        fragmentExtended hostContext fragmentBinders hostBinders
        (extractionContextRelation input selection layout fragmentExtended
          hostContext)
        binderWitness.relationMap occurrenceMap
        (ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout) layout.bodyContainer)
    · intro occurrence occurrenceMember fragmentItem hostItem
        fragmentOccurrenceCompiled hostOccurrenceCompiled
      cases occurrence with
      | node node =>
          apply extractionCompileNode_itemSimulationOfMembership input selection
            layout model named .backward fragmentExtended hostContext
            fullMembership hostExact.nodup fragmentBinders hostBinders
            binderWitness.relationMap node
          · intro region binder arity relation nodeShape lookup
            have owner := fragmentEnumeration.lookup_owner relation lookup
            rw [← owner]
            exact binderWitness.lookup relation
          · exact fragmentOccurrenceCompiled
          · exact hostOccurrenceCompiled
      | child child =>
          have childParent :=
            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
              occurrenceMember
          obtain ⟨childMaterial, childEq⟩ := terminalChild_is_material input
            selection layout child childParent
          subst child
          dsimp only [occurrenceMap] at hostOccurrenceCompiled
          have mappedChild := extractionHostOccurrenceMap_materialChild
            (signature := signature) input selection layout childMaterial
          have hostOccurrenceCompiled' :
              ConcreteElaboration.compileOccurrenceWith? signature input.val
                (ConcreteElaboration.compileRegion? signature input.val hostFuel)
                hostContext hostBinders
                (.child (selection.selectedRegions.get childMaterial)) =
                  some hostItem := by
            exact (congrArg (fun occurrence =>
              ConcreteElaboration.compileOccurrenceWith? signature input.val
                (ConcreteElaboration.compileRegion? signature input.val hostFuel)
                hostContext hostBinders occurrence) mappedChild).symm.trans
              hostOccurrenceCompiled
          cases fragmentKind :
              (input.val.extractDiagramRaw selection layout).regions
                (layout.materialRegion childMaterial) with
          | sheet =>
              simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind]
                at fragmentOccurrenceCompiled
          | cut actualParent =>
              have actualParentEq : actualParent = layout.bodyContainer := by
                rw [fragmentKind] at childParent
                exact Option.some.inj childParent
              subst actualParent
              have hostKind := extractionTerminalDirectChild_cut input selection
                layout (layout.materialRegion childMaterial) fragmentKind
              have hostKind' : input.val.regions
                  (selection.selectedRegions.get childMaterial) =
                    .cut selection.val.anchor := by
                simpa using hostKind
              unfold ConcreteElaboration.compileOccurrenceWith?
                at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              rw [hostKind'] at hostOccurrenceCompiled'
              cases fragmentResult :
                  ConcreteElaboration.compileRegion? signature
                    (input.val.extractDiagramRaw selection layout) fragmentFuel
                    (layout.materialRegion childMaterial) fragmentExtended
                    fragmentBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentResult] at fragmentOccurrenceCompiled
              | some fragmentChild =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentResult] at fragmentOccurrenceCompiled
                  subst fragmentItem
                  cases hostResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        hostFuel (selection.selectedRegions.get childMaterial)
                        hostContext hostBinders with
                  | none =>
                      have hostResult' := hostResult
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                  | some hostChild =>
                      have hostResult' := hostResult
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                      subst hostItem
                      have bodies := extractionCompileRegion_material_denote
                        input selection layout model named .forward fragmentFuel
                        hostFuel childMaterial fragmentExtended hostContext
                        fullMembership fragmentBinders hostBinders
                        (fragmentEnumeration.cutChild
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) fragmentKind)
                        (hostEnumeration.cutChild input.property hostKind')
                        (binderWitness.cutChild
                          (layout.materialRegion childMaterial)
                          (selection.selectedRegions.get childMaterial)
                          fragmentKind hostKind')
                        (fragmentExact.extend_child
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) childParent)
                        (hostExact.extend_child input.property
                          (by simpa only [CRegion.parent?] using
                            congrArg CRegion.parent? hostKind'))
                        fragmentChild hostChild fragmentResult hostResult
                      intro fragmentEnv hostEnv relEnv environments hostNot
                        fragmentDenotes
                      exact hostNot (bodies fragmentEnv hostEnv relEnv
                        environments fragmentDenotes)
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
                    .bubble selection.val.anchor arity := by
                simpa using hostKind
              unfold ConcreteElaboration.compileOccurrenceWith?
                at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              rw [hostKind'] at hostOccurrenceCompiled'
              dsimp only at hostOccurrenceCompiled'
              let fragmentPushed := fragmentBinders.push
                (layout.materialRegion childMaterial) arity
              let hostPushed := hostBinders.push
                (selection.selectedRegions.get childMaterial) arity
              cases fragmentResult :
                  ConcreteElaboration.compileRegion? signature
                    (input.val.extractDiagramRaw selection layout) fragmentFuel
                    (layout.materialRegion childMaterial) fragmentExtended
                    fragmentPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentPushed, fragmentResult] at fragmentOccurrenceCompiled
              | some fragmentChild =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, fragmentKind,
                    fragmentPushed, fragmentResult] at fragmentOccurrenceCompiled
                  subst fragmentItem
                  cases hostResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        hostFuel (selection.selectedRegions.get childMaterial)
                        hostContext hostPushed with
                  | none =>
                      have hostResult' := hostResult
                      dsimp only [hostPushed] at hostResult'
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                  | some hostChild =>
                      have hostResult' := hostResult
                      dsimp only [hostPushed] at hostResult'
                      simp only [List.get_eq_getElem] at hostResult'
                      simp [hostResult'] at hostOccurrenceCompiled'
                      subst hostItem
                      let childWitness := binderWitness.bubbleChild childMaterial
                        arity fragmentKind hostKind'
                      have bodies := extractionCompileRegion_material_denote
                        input selection layout model named .backward fragmentFuel
                        hostFuel childMaterial fragmentExtended hostContext
                        fullMembership fragmentPushed hostPushed
                        (fragmentEnumeration.bubbleChild
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) fragmentKind)
                        (hostEnumeration.bubbleChild input.property hostKind')
                        childWitness
                        (fragmentExact.extend_child
                          (ConcreteDiagram.extractDiagramRaw_wellFormed input
                            selection layout) childParent)
                        (hostExact.extend_child input.property
                          (by simpa only [CRegion.parent?] using
                            congrArg CRegion.parent? hostKind'))
                        fragmentChild hostChild fragmentResult hostResult
                      intro fragmentEnv hostEnv relEnv environments
                      rintro ⟨relationValue, hostDenotes⟩
                      exact ⟨relationValue, bodies fragmentEnv hostEnv
                        (relationValue, relEnv) environments hostDenotes⟩
    · exact fragmentCompiled
    · exact mappedHostCompiled
  have selectedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      .backward
      (extractionContextRelation input selection layout fragmentExtended
        hostContext)
      (fragmentItems.renameRelations binderWitness.relationMap) hostItems := by
    intro fragmentEnv hostEnv relEnv environments hostDenotes
    apply mappedSimulation fragmentEnv hostEnv relEnv environments
    exact (ModalSoundness.compileOccurrences_denote_perm input.val
      (ConcreteElaboration.compileRegion? signature input.val hostFuel)
      hostContext hostBinders
      (extractionHostOccurrenceMap_terminal_perm_selected input selection layout)
      mappedHostCompiled hostCompiled model named hostEnv relEnv).mpr hostDenotes
  rw [ConcreteElaboration.finishRegion_renameRelations]
  intro fragmentOuter hostEnv relEnv outerAgrees hostDenotes
  have hostItemsDenote :=
    (denoteRegion_mk_zero_iff model named hostEnv relEnv hostItems).1 hostDenotes
  obtain ⟨fragmentLocal, fullAgrees⟩ :=
    extractionTerminalExtendedEnvironmentsAgree_backward input selection layout
      fragmentContext hostContext fragmentExact hostExact fragmentOuter hostEnv
      outerAgrees
  have fragmentItemsDenote := selectedSimulation
    (ConcreteElaboration.extendedEnvironment fragmentContext
      layout.bodyContainer fragmentOuter fragmentLocal)
    hostEnv relEnv fullAgrees hostItemsDenote
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
  refine ⟨fragmentLocal, ?_⟩
  exact (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend fragmentContext
      layout.bodyContainer))
    (extendWireEnv fragmentOuter fragmentLocal) relEnv
    (fragmentItems.renameRelations binderWitness.relationMap)).mpr
      fragmentItemsDenote

/-- Zero-spine counterpart of the terminal theorem.  The extracted pattern's
ordered boundary remains ambient while its nonboundary root wires are chosen
as existential witnesses from the exact host-anchor valuation. -/
theorem extractionCompileRoot_selected_denote
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (hzero : layout.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (hostFuel : Nat)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val hostBinders selection.val.anchor)
    (hostCover : hostBinders.Covers selection.val.anchor)
    (hostExact : hostContext.Exact selection.val.anchor)
    (fragmentItems : ItemSeq signature
      (input.val.extractOpenRaw selection layout).rootWires.length [])
    (hostItems : ItemSeq signature hostContext.length hostRels)
    (fragmentCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (input.val.extractDiagramRaw selection layout)
        (ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout)
          (input.val.extractDiagramRaw selection layout).regionCount)
        (input.val.extractOpenRaw selection layout).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences
          (input.val.extractDiagramRaw selection layout)
          (input.val.extractDiagramRaw selection layout).root) =
        some fragmentItems)
    (hostCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        hostContext hostBinders (selectedOccurrences input.val selection) =
        some hostItems) :
    let fragment := input.val.extractOpenRaw selection layout
    let relationMap : RelationRenaming [] hostRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming hostRels
    ConcreteElaboration.RegionSimulation model named .backward
      (extractionContextRelation input selection layout fragment.exposedWires
        hostContext)
      ((ConcreteElaboration.finishRoot fragment.exposedWires
        fragment.hiddenWires fragmentItems).renameRelations relationMap)
      (Region.mk 0 hostItems) := by
  dsimp only
  let fragment := input.val.extractOpenRaw selection layout
  have bodyEq : layout.bodyContainer = fragment.diagram.root :=
    layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero
  let fragmentEnumeration :
      ConcreteElaboration.BinderContext.Enumeration fragment.diagram
        ConcreteElaboration.BinderContext.empty layout.bodyContainer :=
    bodyEq.symm ▸ ConcreteElaboration.BinderContext.Enumeration.empty
      fragment.diagram
  have fragmentExact : ConcreteElaboration.WireContext.Exact
      fragment.rootWires layout.bodyContainer := by
    rw [bodyEq]
    exact ConcreteElaboration.openRootWires_exact
      (ConcreteDiagram.extractOpenRaw_wellFormed input selection layout)
  have itemsSimulation := extractionCompileSelectedItems_denote input selection
    layout model named
    (input.val.extractDiagramRaw selection layout).regionCount hostFuel
    fragment.rootWires hostContext ConcreteElaboration.BinderContext.empty
    hostBinders fragmentEnumeration hostEnumeration hostCover fragmentExact
    hostExact fragmentItems hostItems
    (by simpa [fragment, bodyEq] using fragmentCompiled) hostCompiled
  have relationMapEq :
      ((ExtractionBinderWitness.terminal input selection layout
        ConcreteElaboration.BinderContext.empty fragmentEnumeration hostBinders
        hostCover).relationMap : RelationRenaming [] hostRels) =
          (Splice.Input.PlugLayout.emptyRelationRenaming hostRels :
            RelationRenaming [] hostRels) := by
    apply @funext
    intro arity
    funext relation
    exact Fin.elim0 relation.index
  dsimp only at itemsSimulation
  rw [relationMapEq] at itemsSimulation
  let fullMap := extractionContextIndexMap input selection layout
    fragment.rootWires hostContext fragmentExact hostExact
  let rootLengthEq : fragment.exposedWires.length +
      fragment.hiddenWires.length = fragment.rootWires.length := by
    exact (List.length_append (as := fragment.exposedWires)
      (bs := fragment.hiddenWires)).symm
  intro fragmentOuter hostEnv relEnv outerAgrees hostDenotes
  have hostItemsDenote :=
    (denoteRegion_mk_zero_iff model named hostEnv relEnv hostItems).1
      hostDenotes
  let fragmentHidden : Fin fragment.hiddenWires.length → model.Carrier :=
    fun index => hostEnv (fullMap
      (Fin.cast rootLengthEq
        (Fin.natAdd fragment.exposedWires.length index)))
  let fragmentFull := ConcreteElaboration.rootEnvironment
    fragment.exposedWires fragment.hiddenWires fragmentOuter fragmentHidden
  have fullAgrees :
      (extractionContextRelation input selection layout fragment.rootWires
        hostContext).EnvironmentsAgree fragmentFull hostEnv := by
    intro fragmentIndex hostIndex related
    let appendIndex : Fin
        (fragment.exposedWires.length + fragment.hiddenWires.length) :=
      Fin.cast rootLengthEq.symm fragmentIndex
    have fragmentIndexEq : fragmentIndex = Fin.cast rootLengthEq appendIndex := by
      apply Fin.ext
      rfl
    have related' :
        (extractionContextRelation input selection layout fragment.rootWires
          hostContext).Rel (Fin.cast rootLengthEq appendIndex) hostIndex := by
      have transported := related
      rw [fragmentIndexEq] at transported
      exact transported
    suffices fragmentFull (Fin.cast rootLengthEq appendIndex) =
        hostEnv hostIndex by
      simpa [appendIndex] using this
    refine Fin.addCases (motive := fun index =>
      (extractionContextRelation input selection layout fragment.rootWires
        hostContext).Rel (Fin.cast rootLengthEq index) hostIndex →
      fragmentFull (Fin.cast rootLengthEq index) =
        hostEnv hostIndex) (fun exposedIndex branchRelated => ?_)
      (fun hiddenIndex branchRelated => ?_) appendIndex related'
    · have outerRelated :
          (extractionContextRelation input selection layout
            fragment.exposedWires hostContext).Rel exposedIndex hostIndex := by
        unfold extractionContextRelation at branchRelated ⊢
        change input.val.fragmentWireOrigin selection layout
            ((fragment.exposedWires ++ fragment.hiddenWires)[exposedIndex.val]'_) =
          hostContext[hostIndex.val]'_ at branchRelated
        rw [List.getElem_append_left exposedIndex.isLt] at branchRelated
        exact branchRelated
      simpa [fragmentFull, ConcreteElaboration.rootEnvironment,
        rootLengthEq, appendIndex, extendWireEnv] using
          outerAgrees exposedIndex hostIndex outerRelated
    · have chosen := extractionContextIndexMap_spec input selection layout
          fragment.rootWires hostContext fragmentExact hostExact
          (Fin.cast rootLengthEq
            (Fin.natAdd fragment.exposedWires.length hiddenIndex))
      have hostIndexEq : fullMap
          (Fin.cast rootLengthEq
            (Fin.natAdd fragment.exposedWires.length hiddenIndex)) =
          hostIndex := by
        apply Fin.ext
        apply (List.getElem_inj hostExact.nodup).mp
        unfold extractionContextRelation at chosen branchRelated
        exact chosen.symm.trans (by
          simpa [rootLengthEq, appendIndex, fragment,
            OpenConcreteDiagram.rootWires,
            List.get_eq_getElem] using branchRelated)
      simpa [fragmentFull, ConcreteElaboration.rootEnvironment,
        rootLengthEq, extendWireEnv] using congrArg hostEnv hostIndexEq
  have fragmentItemsDenote := itemsSimulation fragmentFull hostEnv relEnv
    fullAgrees hostItemsDenote
  unfold ConcreteElaboration.finishRoot
  simp only [Region.renameRelations, denoteRegion_mk,
    ItemSeq.castWiresEq_eq_renameWires]
  refine ⟨fragmentHidden, ?_⟩
  have renamedDenote := (denoteItemSeq_renameWires model named
    (Fin.cast rootLengthEq.symm)
    (extendWireEnv fragmentOuter fragmentHidden) relEnv
    (fragmentItems.renameRelations
      (Splice.Input.PlugLayout.emptyRelationRenaming hostRels))).mpr
      (by simpa [fragmentFull, ConcreteElaboration.rootEnvironment] using
        fragmentItemsDenote)
  change denoteItemSeq model named
    (extendWireEnv fragmentOuter fragmentHidden) relEnv
    ((fragmentItems.renameWires (Fin.cast rootLengthEq.symm)).renameRelations
      (Splice.Input.PlugLayout.emptyRelationRenaming hostRels))
  have commute :
      (fragmentItems.renameWires
          (Fin.cast rootLengthEq.symm)).renameRelations
          (Splice.Input.PlugLayout.emptyRelationRenaming hostRels) =
        (fragmentItems.renameRelations
          (Splice.Input.PlugLayout.emptyRelationRenaming hostRels)).renameWires
          (Fin.cast rootLengthEq.symm) :=
    ItemSeq.renameWires_renameRelations fragmentItems
      (Fin.cast rootLengthEq.symm)
      (Splice.Input.PlugLayout.emptyRelationRenaming hostRels)
  exact commute.symm ▸ renamedDenote

end VisualProof.Rule.IterationSoundness
