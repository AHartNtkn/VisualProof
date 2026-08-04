import VisualProof.Rule.Soundness.Iteration.ExtractionRegionLocal
import VisualProof.Rule.Soundness.Modal

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- A child occurrence below copied material maps to that child's material
provenance, never to extraction's administrative fallback. -/
theorem extractionHostOccurrenceMap_child_of_materialParent
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent)) :
    extractionHostOccurrenceMap input selection layout (.child child) =
      .child (extractionRegionOrigin input selection layout child) := by
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  simp only [extractionHostOccurrenceMap_materialChild,
    extractionRegionOrigin_materialRegion]

/-- A copied direct cut child has the corresponding direct host cut shape. -/
theorem extractionMaterialDirectChild_cut
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .cut (layout.materialRegion parent)) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .cut (selection.selectedRegions.get parent) := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent) := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  cases hostKind : input.val.regions (selection.selectedRegions.get childIndex) with
  | sheet =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_sheet
        selection layout childIndex hostKind
      rw [fragmentKind] at kind
      exact False.elim
        (bodyContainer_ne_materialRegion layout parent (CRegion.cut.inj kind))
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      have parentEq := CRegion.cut.inj kind
      rw [extractionRegionOrigin_materialRegion, hostKind]
      exact congrArg CRegion.cut
        ((fragmentParent_eq_materialRegion_iff input selection layout
          hostParent parent).1 parentEq)
  | bubble hostParent arity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent arity hostKind
      rw [fragmentKind] at kind
      cases kind

/-- A copied direct bubble child has the corresponding direct host bubble
shape and arity. -/
theorem extractionMaterialDirectChild_bubble
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (parent : Fin layout.materialRegionCount)
    (child : Fin layout.regionCount)
    (arity : Nat)
    (kind : (input.val.extractDiagramRaw selection layout).regions child =
      .bubble (layout.materialRegion parent) arity) :
    input.val.regions (extractionRegionOrigin input selection layout child) =
      .bubble (selection.selectedRegions.get parent) arity := by
  have childParent : ((input.val.extractDiagramRaw selection layout).regions
      child).parent? = some (layout.materialRegion parent) := by
    rw [kind]
    rfl
  obtain ⟨childIndex, rfl⟩ := materialDirectChild_is_material input selection
    layout parent child childParent
  cases hostKind : input.val.regions (selection.selectedRegions.get childIndex) with
  | sheet =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_sheet
        selection layout childIndex hostKind
      rw [fragmentKind] at kind
      cases kind
  | cut hostParent =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_cut
        selection layout childIndex hostParent hostKind
      rw [fragmentKind] at kind
      cases kind
  | bubble hostParent hostArity =>
      have fragmentKind := input.val.extractDiagramRaw_materialRegion_bubble
        selection layout childIndex hostParent hostArity hostKind
      rw [fragmentKind] at kind
      have equal := CRegion.bubble.inj kind
      rw [extractionRegionOrigin_materialRegion, hostKind, equal.2]
      exact congrArg (fun region => CRegion.bubble region arity)
        ((fragmentParent_eq_materialRegion_iff input selection layout
          hostParent parent).1 equal.1)

/-- Recursive semantic simulation of every copied material region. -/
theorem extractionCompileRegion_material_denote
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ∀ {fragmentRels hostRels : RelCtx}
      (direction : ConcreteElaboration.SimulationDirection)
      (fragmentFuel hostFuel : Nat)
      (material : Fin layout.materialRegionCount)
      (fragmentContext : ConcreteElaboration.WireContext
        (input.val.extractDiagramRaw selection layout))
      (hostContext : ConcreteElaboration.WireContext input.val)
      (membership : ∀ wire,
        input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
          wire ∈ fragmentContext)
      (fragmentBinders : ConcreteElaboration.BinderContext
        (input.val.extractDiagramRaw selection layout) fragmentRels)
      (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
      (fragmentEnumeration : ConcreteElaboration.BinderContext.Enumeration
        (input.val.extractDiagramRaw selection layout) fragmentBinders
        (layout.materialRegion material))
      (hostEnumeration : ConcreteElaboration.BinderContext.Enumeration
        input.val hostBinders (selection.selectedRegions.get material))
      (binderWitness : ExtractionBinderWitness input selection layout
        (layout.materialRegion material) (selection.selectedRegions.get material)
        fragmentBinders fragmentEnumeration hostBinders)
      (fragmentExact :
        (fragmentContext.extend (layout.materialRegion material)).Exact
          (layout.materialRegion material))
      (hostExact :
        (hostContext.extend (selection.selectedRegions.get material)).Exact
          (selection.selectedRegions.get material))
      (fragmentBody : Region signature fragmentContext.length fragmentRels)
      (hostBody : Region signature hostContext.length hostRels),
      ConcreteElaboration.compileRegion? signature
          (input.val.extractDiagramRaw selection layout) fragmentFuel
          (layout.materialRegion material) fragmentContext fragmentBinders =
        some fragmentBody →
      ConcreteElaboration.compileRegion? signature input.val hostFuel
          (selection.selectedRegions.get material) hostContext hostBinders =
        some hostBody →
      ConcreteElaboration.RegionSimulation model named direction
        (extractionContextRelation input selection layout fragmentContext
          hostContext)
        (fragmentBody.renameRelations binderWitness.relationMap) hostBody := by
  intro fragmentRels hostRels direction fragmentFuel
  induction fragmentFuel generalizing fragmentRels hostRels direction with
  | zero =>
      intro hostFuel material fragmentContext hostContext membership
        fragmentBinders hostBinders fragmentEnumeration hostEnumeration
        binderWitness fragmentExact hostExact fragmentBody hostBody
        fragmentCompiled hostCompiled
      simp [ConcreteElaboration.compileRegion?] at fragmentCompiled
  | succ fragmentFuel induction =>
      intro hostFuel
      cases hostFuel with
      | zero =>
          intro material fragmentContext hostContext membership fragmentBinders
            hostBinders fragmentEnumeration hostEnumeration binderWitness
            fragmentExact hostExact fragmentBody hostBody fragmentCompiled
            hostCompiled
          simp [ConcreteElaboration.compileRegion?] at hostCompiled
      | succ hostFuel =>
          intro material fragmentContext hostContext membership fragmentBinders
            hostBinders fragmentEnumeration hostEnumeration binderWitness
            fragmentExact hostExact fragmentBody hostBody fragmentCompiled
            hostCompiled
          let fragmentRegion := layout.materialRegion material
          let hostRegion := selection.selectedRegions.get material
          let fragmentExtended := fragmentContext.extend fragmentRegion
          let hostExtended := hostContext.extend hostRegion
          simp only [ConcreteElaboration.compileRegion?] at fragmentCompiled hostCompiled
          change (do
              let items ← ConcreteElaboration.compileOccurrencesWith? signature
                (input.val.extractDiagramRaw selection layout)
                (ConcreteElaboration.compileRegion? signature
                  (input.val.extractDiagramRaw selection layout) fragmentFuel)
                fragmentExtended fragmentBinders
                (ConcreteElaboration.localOccurrences
                  (input.val.extractDiagramRaw selection layout) fragmentRegion)
              pure (ConcreteElaboration.finishRegion
                (input.val.extractDiagramRaw selection layout) fragmentContext
                fragmentRegion items)) = some fragmentBody at fragmentCompiled
          change (do
              let items ← ConcreteElaboration.compileOccurrencesWith? signature
                input.val
                (ConcreteElaboration.compileRegion? signature input.val hostFuel)
                hostExtended hostBinders
                (ConcreteElaboration.localOccurrences input.val hostRegion)
              pure (ConcreteElaboration.finishRegion input.val hostContext
                hostRegion items)) = some hostBody at hostCompiled
          cases fragmentItemsResult :
              ConcreteElaboration.compileOccurrencesWith? signature
                (input.val.extractDiagramRaw selection layout)
                (ConcreteElaboration.compileRegion? signature
                  (input.val.extractDiagramRaw selection layout) fragmentFuel)
                fragmentExtended fragmentBinders
                (ConcreteElaboration.localOccurrences
                  (input.val.extractDiagramRaw selection layout)
                  fragmentRegion) with
          | none =>
              simp [fragmentItemsResult] at fragmentCompiled
          | some fragmentItems =>
              simp [fragmentItemsResult] at fragmentCompiled
              subst fragmentBody
              cases hostItemsResult :
                  ConcreteElaboration.compileOccurrencesWith? signature input.val
                    (ConcreteElaboration.compileRegion? signature input.val
                      hostFuel)
                    hostExtended hostBinders
                    (ConcreteElaboration.localOccurrences input.val hostRegion) with
              | none =>
                  simp [hostItemsResult] at hostCompiled
              | some hostItems =>
                  simp [hostItemsResult] at hostCompiled
                  subst hostBody
                  let occurrenceMap :=
                    extractionHostOccurrenceMap input selection layout
                  obtain ⟨mappedHostItems, mappedHostItemsResult⟩ :=
                    ConcreteElaboration.compileOccurrencesWith?_complete
                      (ConcreteElaboration.compileRegion? signature input.val
                        hostFuel)
                      hostExtended hostBinders
                      ((ConcreteElaboration.localOccurrences
                        (input.val.extractDiagramRaw selection layout)
                        fragmentRegion).map occurrenceMap)
                      (by
                        intro hostOccurrence hostMember
                        rw [List.mem_map] at hostMember
                        obtain ⟨fragmentOccurrence, fragmentMember, rfl⟩ :=
                          hostMember
                        apply ModalSoundness.compileOccurrence_success_of_mem
                          input.val
                          (ConcreteElaboration.compileRegion? signature input.val
                            hostFuel)
                          hostExtended hostBinders hostItemsResult
                        exact extractionHostOccurrenceMap_mem_local_material input
                          selection layout material fragmentOccurrence
                          fragmentMember)
                  have extendedMembership :=
                    extractionContextMembership_extend_material input selection
                      layout fragmentContext hostContext membership material
                  have itemSimulation : ConcreteElaboration.ItemSeqSimulation
                      model named direction
                      (extractionContextRelation input selection layout
                        fragmentExtended hostExtended)
                      (fragmentItems.renameRelations binderWitness.relationMap)
                      mappedHostItems := by
                    apply
                      ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                        model named direction
                        (ConcreteElaboration.compileRegion? signature
                          (input.val.extractDiagramRaw selection layout)
                          fragmentFuel)
                        (ConcreteElaboration.compileRegion? signature input.val
                          hostFuel)
                        fragmentExtended hostExtended fragmentBinders hostBinders
                        (extractionContextRelation input selection layout
                          fragmentExtended hostExtended)
                        binderWitness.relationMap occurrenceMap
                        (ConcreteElaboration.localOccurrences
                          (input.val.extractDiagramRaw selection layout)
                          fragmentRegion)
                    · intro occurrence occurrenceMember fragmentItem hostItem
                        fragmentOccurrenceCompiled hostOccurrenceCompiled
                      cases occurrence with
                      | node node =>
                          apply extractionCompileNode_itemSimulationOfMembership
                            input selection layout model named direction
                            fragmentExtended hostExtended extendedMembership
                            hostExact.nodup fragmentBinders hostBinders
                            binderWitness.relationMap node
                          · intro region binder arity relation nodeShape lookup
                            have owner := fragmentEnumeration.lookup_owner relation
                              lookup
                            rw [← owner]
                            exact binderWitness.lookup relation
                          · exact fragmentOccurrenceCompiled
                          · exact hostOccurrenceCompiled
                      | child child =>
                          have childParent :=
                            (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
                              occurrenceMember
                          obtain ⟨childMaterial, childEq⟩ :=
                            materialDirectChild_is_material input selection layout
                              material child childParent
                          subst child
                          dsimp only [occurrenceMap] at hostOccurrenceCompiled
                          have mappedChild :=
                            extractionHostOccurrenceMap_materialChild
                              (signature := signature) input selection layout
                              childMaterial
                          have hostOccurrenceCompiled' :
                              ConcreteElaboration.compileOccurrenceWith? signature
                                input.val
                                (ConcreteElaboration.compileRegion? signature
                                  input.val hostFuel)
                                hostExtended hostBinders
                                (.child (selection.selectedRegions.get
                                  childMaterial)) = some hostItem := by
                            exact (congrArg (fun occurrence =>
                              ConcreteElaboration.compileOccurrenceWith?
                                signature input.val
                                (ConcreteElaboration.compileRegion? signature
                                  input.val hostFuel)
                                hostExtended hostBinders occurrence)
                              mappedChild).symm.trans hostOccurrenceCompiled
                          cases fragmentKind :
                              (input.val.extractDiagramRaw selection layout).regions
                                (layout.materialRegion childMaterial) with
                          | sheet =>
                              simp [ConcreteElaboration.compileOccurrenceWith?,
                                fragmentKind] at fragmentOccurrenceCompiled
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
                                .cut (selection.selectedRegions.get material) := by
                                simpa using hostKind
                              unfold ConcreteElaboration.compileOccurrenceWith?
                                at hostOccurrenceCompiled'
                              dsimp only at hostOccurrenceCompiled'
                              rw [hostKind'] at hostOccurrenceCompiled'
                              cases fragmentResult :
                                  ConcreteElaboration.compileRegion? signature
                                    (input.val.extractDiagramRaw selection layout)
                                    fragmentFuel
                                    (layout.materialRegion childMaterial)
                                    fragmentExtended fragmentBinders with
                              | none =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    fragmentKind, fragmentResult]
                                    at fragmentOccurrenceCompiled
                              | some fragmentChild =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    fragmentKind, fragmentResult]
                                    at fragmentOccurrenceCompiled
                                  subst fragmentItem
                                  cases hostResult :
                                      ConcreteElaboration.compileRegion? signature
                                        input.val hostFuel
                                        (selection.selectedRegions.get childMaterial)
                                        hostExtended hostBinders with
                                  | none =>
                                      have hostResult' := hostResult
                                      simp only [List.get_eq_getElem] at hostResult'
                                      simp [hostResult']
                                        at hostOccurrenceCompiled'
                                  | some hostChild =>
                                      have hostResult' := hostResult
                                      simp only [List.get_eq_getElem] at hostResult'
                                      simp [hostResult']
                                        at hostOccurrenceCompiled'
                                      subst hostItem
                                      have bodies := induction direction.flip
                                        hostFuel childMaterial fragmentExtended
                                        hostExtended extendedMembership
                                        fragmentBinders hostBinders
                                        (fragmentEnumeration.cutChild
                                          (ConcreteDiagram.extractDiagramRaw_wellFormed
                                            input selection layout) fragmentKind)
                                        (hostEnumeration.cutChild input.property
                                          hostKind')
                                        (binderWitness.cutChild
                                          (layout.materialRegion childMaterial)
                                          (selection.selectedRegions.get
                                            childMaterial)
                                          fragmentKind hostKind')
                                        (fragmentExact.extend_child
                                          (ConcreteDiagram.extractDiagramRaw_wellFormed
                                            input selection layout) childParent)
                                        (hostExact.extend_child input.property
                                          (by simpa only [CRegion.parent?] using
                                            congrArg CRegion.parent? hostKind'))
                                        fragmentChild hostChild fragmentResult
                                        hostResult
                                      intro fragmentEnv hostEnv relEnv environments
                                      have bodyEntailment := bodies fragmentEnv hostEnv
                                        relEnv environments
                                      simp only [Item.renameRelations,
                                        cut_denotes_negation]
                                      cases direction with
                                      | forward =>
                                          exact fun fragmentNot hostDenotes =>
                                            fragmentNot (bodyEntailment hostDenotes)
                                      | backward =>
                                          exact fun hostNot fragmentDenotes =>
                                            hostNot (bodyEntailment fragmentDenotes)
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
                                .bubble (selection.selectedRegions.get material)
                                  arity := by
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
                                    (input.val.extractDiagramRaw selection layout)
                                    fragmentFuel
                                    (layout.materialRegion childMaterial)
                                    fragmentExtended fragmentPushed with
                              | none =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    fragmentKind, fragmentPushed, fragmentResult]
                                    at fragmentOccurrenceCompiled
                              | some fragmentChild =>
                                  simp [ConcreteElaboration.compileOccurrenceWith?,
                                    fragmentKind, fragmentPushed, fragmentResult]
                                    at fragmentOccurrenceCompiled
                                  subst fragmentItem
                                  cases hostResult :
                                      ConcreteElaboration.compileRegion? signature
                                        input.val hostFuel
                                        (selection.selectedRegions.get childMaterial)
                                        hostExtended hostPushed with
                                  | none =>
                                      have hostResult' := hostResult
                                      dsimp only [hostPushed] at hostResult'
                                      simp only [List.get_eq_getElem] at hostResult'
                                      simp [hostResult']
                                        at hostOccurrenceCompiled'
                                  | some hostChild =>
                                      have hostResult' := hostResult
                                      dsimp only [hostPushed] at hostResult'
                                      simp only [List.get_eq_getElem] at hostResult'
                                      simp [hostResult']
                                        at hostOccurrenceCompiled'
                                      subst hostItem
                                      let childWitness := binderWitness.bubbleChild
                                        childMaterial arity fragmentKind hostKind'
                                      have bodies := induction direction hostFuel
                                        childMaterial fragmentExtended hostExtended
                                        extendedMembership fragmentPushed hostPushed
                                        (fragmentEnumeration.bubbleChild
                                          (ConcreteDiagram.extractDiagramRaw_wellFormed
                                            input selection layout) fragmentKind)
                                        (hostEnumeration.bubbleChild input.property
                                          hostKind')
                                        childWitness
                                        (fragmentExact.extend_child
                                          (ConcreteDiagram.extractDiagramRaw_wellFormed
                                            input selection layout) childParent)
                                        (hostExact.extend_child input.property
                                          (by simpa only [CRegion.parent?] using
                                            congrArg CRegion.parent? hostKind'))
                                        fragmentChild hostChild fragmentResult
                                        hostResult
                                      intro fragmentEnv hostEnv relEnv environments
                                      simp only [Item.renameRelations,
                                        bubble_denotes_exists]
                                      cases direction with
                                      | forward =>
                                          rintro ⟨relationValue, fragmentDenotes⟩
                                          exact ⟨relationValue,
                                            bodies fragmentEnv hostEnv
                                              (relationValue, relEnv) environments
                                              fragmentDenotes⟩
                                      | backward =>
                                          rintro ⟨relationValue, hostDenotes⟩
                                          exact ⟨relationValue,
                                            bodies fragmentEnv hostEnv
                                              (relationValue, relEnv) environments
                                              hostDenotes⟩
                    · exact fragmentItemsResult
                    · exact mappedHostItemsResult
                  have itemSimulationHost :
                      ConcreteElaboration.ItemSeqSimulation model named direction
                        (extractionContextRelation input selection layout
                          fragmentExtended hostExtended)
                        (fragmentItems.renameRelations
                          binderWitness.relationMap) hostItems := by
                    intro fragmentEnv hostEnv relEnv environments
                    have mappedEntailment := itemSimulation fragmentEnv hostEnv
                      relEnv environments
                    have permutation := ModalSoundness.compileOccurrences_denote_perm
                      input.val
                      (ConcreteElaboration.compileRegion? signature input.val
                        hostFuel)
                      hostExtended hostBinders
                      (extractionHostOccurrenceMap_material_perm_host input
                        selection layout material)
                      mappedHostItemsResult hostItemsResult model named hostEnv
                      relEnv
                    cases direction with
                    | forward =>
                        exact fun fragmentDenotes =>
                          permutation.mp (mappedEntailment fragmentDenotes)
                    | backward =>
                        exact fun hostDenotes =>
                          mappedEntailment (permutation.mpr hostDenotes)
                  rw [ConcreteElaboration.finishRegion_renameRelations]
                  apply ConcreteElaboration.finishRegion_denote direction
                    fragmentContext hostContext fragmentRegion hostRegion
                    (extractionContextRelation input selection layout
                      fragmentContext hostContext)
                    model named
                    (fragmentItems.renameRelations binderWitness.relationMap)
                    hostItems
                  apply ConcreteElaboration.directionalLocalTransport_of_agreement
                    direction fragmentContext hostContext fragmentRegion hostRegion
                    (extractionContextRelation input selection layout
                      fragmentContext hostContext)
                    (extractionContextRelation input selection layout
                      fragmentExtended hostExtended)
                    model named
                    (fragmentItems.renameRelations binderWitness.relationMap)
                    hostItems
                  · exact extractionDirectionalEnvironmentSelection input
                      selection layout direction fragmentContext hostContext
                      membership material fragmentExact.nodup hostExact.nodup
                  · exact itemSimulationHost

end VisualProof.Rule.IterationSoundness
