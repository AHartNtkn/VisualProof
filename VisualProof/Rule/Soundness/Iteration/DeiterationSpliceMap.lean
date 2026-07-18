import VisualProof.Rule.Soundness.Iteration.DeiterationPattern

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private def finiteSumEquiv
    (left : FiniteEquiv (Fin a) (Fin b))
    (right : FiniteEquiv (Fin c) (Fin d)) :
    FiniteEquiv (Fin (a + c)) (Fin (b + d)) where
  toFun := Fin.addCases
    (fun index => Fin.castAdd d (left index))
    (fun index => Fin.natAdd b (right index))
  invFun := Fin.addCases
    (fun index => Fin.castAdd c (left.symm index))
    (fun index => Fin.natAdd a (right.symm index))
  left_inv := by
    intro index
    refine Fin.addCases (m := a) (n := c) (fun leftIndex => ?_)
      (fun rightIndex => ?_) index
    · simp only [Fin.addCases_left]
      exact congrArg (Fin.castAdd c) (left.left_inv leftIndex)
    · simp only [Fin.addCases_right]
      exact congrArg (Fin.natAdd a) (right.left_inv rightIndex)
  right_inv := by
    intro index
    refine Fin.addCases (m := b) (n := d) (fun leftIndex => ?_)
      (fun rightIndex => ?_) index
    · simp only [Fin.addCases_left]
      exact congrArg (Fin.castAdd d) (left.right_inv leftIndex)
    · simp only [Fin.addCases_right]
      exact congrArg (Fin.natAdd b) (right.right_inv rightIndex)

private theorem finiteSumEquiv_left
    (left : FiniteEquiv (Fin a) (Fin b))
    (right : FiniteEquiv (Fin c) (Fin d)) (index : Fin a) :
    finiteSumEquiv left right (Fin.castAdd c index) =
      Fin.castAdd d (left index) := by
  simp [finiteSumEquiv]

private theorem finiteSumEquiv_right
    (left : FiniteEquiv (Fin a) (Fin b))
    (right : FiniteEquiv (Fin c) (Fin d)) (index : Fin c) :
    finiteSumEquiv left right (Fin.natAdd a index) =
      Fin.natAdd b (right index) := by
  simp [finiteSumEquiv]

theorem deiterationPattern_material_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    (Splice.Decomposition.originalFragmentInput
      (deiterationDecomposition input selection)).binderSpine.IsMaterialRegion
        ((deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
          region) ↔
      (deiterationReinsertInput input selection witness).binderSpine.IsMaterialRegion
        region := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let countEq := deiterationPattern_proxyCount_eq input selection witness
  constructor
  · intro targetMaterial
    constructor
    · intro sourceRoot
      apply targetMaterial.1
      rw [sourceRoot]
      exact occurrence.diagram.root_eq
    · intro sourceIndex sourceProxy
      apply targetMaterial.2 (Fin.cast countEq sourceIndex)
      rw [← deiterationPattern_proxy_alignment input selection witness
        sourceIndex, sourceProxy]
  · intro sourceMaterial
    constructor
    · intro targetRoot
      apply sourceMaterial.1
      apply occurrence.diagram.regions.injective
      exact targetRoot.trans occurrence.diagram.root_eq.symm
    · intro targetIndex targetProxy
      let sourceIndex : Fin source.binderSpine.proxyCount :=
        Fin.cast countEq.symm targetIndex
      have aligned := deiterationPattern_proxy_alignment input selection witness
        sourceIndex
      have castEq : Fin.cast countEq sourceIndex = targetIndex := by
        apply Fin.ext
        rfl
      rw [castEq] at aligned
      apply sourceMaterial.2 sourceIndex
      apply occurrence.diagram.regions.injective
      exact targetProxy.trans aligned.symm

private theorem deiterationMaterial_mem_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions region ∈
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).plugLayout.materialRegions.enumeration ↔
      region ∈ (deiterationReinsertInput input selection witness).plugLayout.materialRegions.enumeration := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  constructor
  · intro membership
    have targetSurvives := (SurvivorDomain.mem_enumeration
      target.plugLayout.materialRegions (occurrence.diagram.regions region)).mp membership
    have targetMaterial := (Splice.Input.PlugLayout.materialRegions_survives_iff
      target.plugLayout (occurrence.diagram.regions region)).mp targetSurvives
    have sourceMaterial := (deiterationPattern_material_iff input selection witness region).mp
      targetMaterial
    have sourceSurvives := (Splice.Input.PlugLayout.materialRegions_survives_iff
      source.plugLayout region).mpr sourceMaterial
    exact (SurvivorDomain.mem_enumeration source.plugLayout.materialRegions region).mpr
      sourceSurvives
  · intro membership
    have sourceSurvives := (SurvivorDomain.mem_enumeration
      source.plugLayout.materialRegions region).mp membership
    have sourceMaterial := (Splice.Input.PlugLayout.materialRegions_survives_iff
      source.plugLayout region).mp sourceSurvives
    have targetMaterial := (deiterationPattern_material_iff input selection witness region).mpr
      sourceMaterial
    have targetSurvives := (Splice.Input.PlugLayout.materialRegions_survives_iff
      target.plugLayout (occurrence.diagram.regions region)).mpr targetMaterial
    exact (SurvivorDomain.mem_enumeration target.plugLayout.materialRegions
      (occurrence.diagram.regions region)).mpr targetSurvives

noncomputable def deiterationMaterialEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (deiterationReinsertInput input selection witness).plugLayout.materialRegions.Carrier
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.materialRegions.Carrier :=
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  FiniteEquiv.restrictLists occurrence.diagram.regions
    source.plugLayout.materialRegions.enumeration
    target.plugLayout.materialRegions.enumeration
    source.plugLayout.materialRegions.enumeration_nodup
    target.plugLayout.materialRegions.enumeration_nodup (by
      intro region
      exact deiterationMaterial_mem_iff input selection witness region)

theorem deiterationMaterialEquiv_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (material :
      (deiterationReinsertInput input selection witness).plugLayout.materialRegions.Carrier) :
    (Splice.Decomposition.originalFragmentInput
      (deiterationDecomposition input selection)).plugLayout.materialRegions.origin
        (deiterationMaterialEquiv input selection witness material) =
      (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
        ((deiterationReinsertInput input selection witness).plugLayout.materialRegions.origin
          material) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  have spec := FiniteEquiv.restrictLists_spec occurrence.diagram.regions
    source.plugLayout.materialRegions.enumeration
    target.plugLayout.materialRegions.enumeration
    source.plugLayout.materialRegions.enumeration_nodup
    target.plugLayout.materialRegions.enumeration_nodup (by
      intro region
      exact deiterationMaterial_mem_iff input selection witness region)
      material
  simpa [deiterationMaterialEquiv, source, target, occurrence,
    SurvivorDomain.origin] using spec

noncomputable def deiterationInternalWireEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (deiterationReinsertInput input selection witness).plugLayout.internalWires.Carrier
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.internalWires.Carrier :=
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  FiniteEquiv.restrictLists occurrence.diagram.wires
    source.plugLayout.internalWires.enumeration
    target.plugLayout.internalWires.enumeration
    source.plugLayout.internalWires.enumeration_nodup
    target.plugLayout.internalWires.enumeration_nodup (by
      intro wire
      constructor
      · intro membership
        have targetSurvives := (SurvivorDomain.mem_enumeration
          target.plugLayout.internalWires (occurrence.diagram.wires wire)).mp membership
        have targetInternal := (Splice.Input.PlugLayout.internalWires_survives_iff
          target.plugLayout (occurrence.diagram.wires wire)).mp targetSurvives
        have sourceInternal := (not_congr (occurrence.mem_exposedWires_iff wire)).mp
          targetInternal
        exact (SurvivorDomain.mem_enumeration source.plugLayout.internalWires wire).mpr
          ((Splice.Input.PlugLayout.internalWires_survives_iff
            source.plugLayout wire).mpr sourceInternal)
      · intro membership
        have sourceSurvives := (SurvivorDomain.mem_enumeration
          source.plugLayout.internalWires wire).mp membership
        have sourceInternal := (Splice.Input.PlugLayout.internalWires_survives_iff
          source.plugLayout wire).mp sourceSurvives
        have targetInternal := (not_congr (occurrence.mem_exposedWires_iff wire)).mpr
          sourceInternal
        exact (SurvivorDomain.mem_enumeration target.plugLayout.internalWires
          (occurrence.diagram.wires wire)).mpr
            ((Splice.Input.PlugLayout.internalWires_survives_iff target.plugLayout
              (occurrence.diagram.wires wire)).mpr targetInternal))

theorem deiterationInternalWireEquiv_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire :
      (deiterationReinsertInput input selection witness).plugLayout.internalWires.Carrier) :
    (Splice.Decomposition.originalFragmentInput
      (deiterationDecomposition input selection)).plugLayout.internalWires.origin
        (deiterationInternalWireEquiv input selection witness wire) =
      (deiterationPatternOccurrenceEquiv input selection witness).diagram.wires
        ((deiterationReinsertInput input selection witness).plugLayout.internalWires.origin
          wire) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  have spec := FiniteEquiv.restrictLists_spec occurrence.diagram.wires
    source.plugLayout.internalWires.enumeration
    target.plugLayout.internalWires.enumeration
    source.plugLayout.internalWires.enumeration_nodup
    target.plugLayout.internalWires.enumeration_nodup (by
      intro sourceWire
      constructor
      · intro membership
        have targetSurvives := (SurvivorDomain.mem_enumeration
          target.plugLayout.internalWires
          (occurrence.diagram.wires sourceWire)).mp membership
        have targetInternal := (Splice.Input.PlugLayout.internalWires_survives_iff
          target.plugLayout (occurrence.diagram.wires sourceWire)).mp targetSurvives
        have sourceInternal := (not_congr
          (occurrence.mem_exposedWires_iff sourceWire)).mp targetInternal
        exact (SurvivorDomain.mem_enumeration source.plugLayout.internalWires sourceWire).mpr
          ((Splice.Input.PlugLayout.internalWires_survives_iff
            source.plugLayout sourceWire).mpr sourceInternal)
      · intro membership
        have sourceSurvives := (SurvivorDomain.mem_enumeration
          source.plugLayout.internalWires sourceWire).mp membership
        have sourceInternal := (Splice.Input.PlugLayout.internalWires_survives_iff
          source.plugLayout sourceWire).mp sourceSurvives
        have targetInternal := (not_congr
          (occurrence.mem_exposedWires_iff sourceWire)).mpr sourceInternal
        exact (SurvivorDomain.mem_enumeration target.plugLayout.internalWires
          (occurrence.diagram.wires sourceWire)).mpr
            ((Splice.Input.PlugLayout.internalWires_survives_iff target.plugLayout
              (occurrence.diagram.wires sourceWire)).mpr targetInternal)) wire
  simpa [deiterationInternalWireEquiv, source, target, occurrence,
    SurvivorDomain.origin] using spec

noncomputable def deiterationQuotientEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).wireQuotient.Carrier :=
  (iterationQuotientWireEquiv
    (deiterationRemoved input selection)
    (deiterationRetainedSelection input selection witness)
    (deiterationReinsertTarget input selection)).trans
      (Splice.Decomposition.originalQuotientWireEquiv
        (deiterationDecomposition input selection)).symm

theorem deiterationQuotientEquiv_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    Splice.Decomposition.originalQuotientWireEquiv
        (deiterationDecomposition input selection)
        (deiterationQuotientEquiv input selection witness wire) =
      iterationQuotientWireEquiv
        (deiterationRemoved input selection)
        (deiterationRetainedSelection input selection witness)
        (deiterationReinsertTarget input selection) wire := by
  exact (Splice.Decomposition.originalQuotientWireEquiv
    (deiterationDecomposition input selection)).right_inv _

theorem deiterationBinderTarget_alignment
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin
      (deiterationReinsertInput input selection witness).binderSpine.proxyCount) :
    (deiterationReinsertInput input selection witness).binderTarget index =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).binderTarget
          (Fin.cast (deiterationPattern_proxyCount_eq input selection witness) index) := by
  let domains := deiterationDomains input selection
  let sourceLayout := deiterationRetainedLayout input selection witness
  let justifierLayout := deiterationOriginalLayout input selection witness
  let targetLayout : FragmentLayout input.val selection := {}
  let externalEq := deiterationExternalLengthEq input selection witness
  let sameEq := congrArg List.length witness.sameExternalBinders
  let targetIndex :=
    Fin.cast (deiterationPattern_proxyCount_eq input selection witness) index
  apply domains.regions.origin_injective
  change domains.regions.origin
      ((deiterationReinsertInput input selection witness).binderTarget index) =
    domains.regions.origin
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).binderTarget targetIndex)
  have listsEq : justifierLayout.externalBinders = targetLayout.externalBinders := by
    exact witness.sameExternalBinders
  calc
    domains.regions.origin
        ((deiterationReinsertInput input selection witness).binderTarget index) =
      justifierLayout.externalBinders.get (Fin.cast externalEq index) := by
        change domains.regions.origin (sourceLayout.externalBinders.get index) = _
        exact deiterationRetained_externalBinder_get_origin input selection witness index
    _ = targetLayout.externalBinders.get targetIndex := by
      have transported := List.get_of_eq listsEq (Fin.cast externalEq index)
      simpa only [List.get_eq_getElem, Fin.val_cast] using transported
    _ = domains.regions.origin
        ((Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).binderTarget targetIndex) := by
      symm
      change domains.regions.origin
          (Splice.Decomposition.originalBinderTarget
            (deiterationDecomposition input selection) targetIndex) = _
      unfold Splice.Decomposition.originalBinderTarget
      change (deiterationDecomposition input selection).frameDomains.regions.origin
          ((deiterationDecomposition input selection).frameDomains.regions.index
            ((deiterationDecomposition input selection).extraction.raw.layout
              |>.externalBinders.get targetIndex) _) = _
      rw [(deiterationDecomposition input selection).frameDomains.regions.origin_index]
      rfl

noncomputable def deiterationOutputRegionEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationReinsertInput input selection witness).plugLayout.plugRaw.regionCount)
      (Fin (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.regionCount) :=
  finiteSumEquiv (FiniteEquiv.refl
    (Fin (deiterationRemoved input selection).val.regionCount))
    (deiterationMaterialEquiv input selection witness)

noncomputable def deiterationOutputNodeEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationReinsertInput input selection witness).plugLayout.plugRaw.nodeCount)
      (Fin (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.nodeCount) :=
  finiteSumEquiv (FiniteEquiv.refl
    (Fin (deiterationRemoved input selection).val.nodeCount))
    (deiterationPatternOccurrenceEquiv input selection witness).diagram.nodes

noncomputable def deiterationOutputWireEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationReinsertInput input selection witness).plugLayout.plugRaw.wireCount)
      (Fin (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.wireCount) :=
  finiteSumEquiv (deiterationQuotientEquiv input selection witness)
    (deiterationInternalWireEquiv input selection witness)

@[simp] theorem deiterationOutputRegionEquiv_frame
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin (deiterationRemoved input selection).val.regionCount) :
    deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.frameRegion region) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.frameRegion region := by
  exact finiteSumEquiv_left _ _ region

@[simp] theorem deiterationOutputRegionEquiv_material
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region :
      (deiterationReinsertInput input selection witness).plugLayout.materialRegions.Carrier) :
    deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.materialRegion region) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.materialRegion
          (deiterationMaterialEquiv input selection witness region) := by
  exact finiteSumEquiv_right _ _ region

theorem deiterationOutputRegionEquiv_body
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.bodyRegion region) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.bodyRegion
          ((deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
            region) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  by_cases sourceMaterial : source.binderSpine.IsMaterialRegion region
  · have targetMaterial : target.binderSpine.IsMaterialRegion
        (occurrence.diagram.regions region) :=
      (deiterationPattern_material_iff input selection witness region).mpr sourceMaterial
    let material := sourceLayout.materialIndex region sourceMaterial
    have sourceOrigin : sourceLayout.materialRegions.origin material = region := by
      exact sourceLayout.materialRegions.origin_index region
        ((sourceLayout.materialRegions_survives_iff region).2 sourceMaterial)
    have materialEq : deiterationMaterialEquiv input selection witness material =
        targetLayout.materialIndex (occurrence.diagram.regions region) targetMaterial := by
      apply targetLayout.materialRegions.origin_injective
      rw [deiterationMaterialEquiv_origin input selection witness material,
        sourceOrigin]
      exact targetLayout.materialRegions.origin_index
        (occurrence.diagram.regions region)
        ((targetLayout.materialRegions_survives_iff _).2 targetMaterial) |>.symm
    rw [sourceLayout.bodyRegion_material region sourceMaterial,
      targetLayout.bodyRegion_material (occurrence.diagram.regions region) targetMaterial]
    change deiterationOutputRegionEquiv input selection witness
        (sourceLayout.materialRegion material) =
      targetLayout.materialRegion
        (targetLayout.materialIndex (occurrence.diagram.regions region) targetMaterial)
    rw [deiterationOutputRegionEquiv_material, materialEq]
  · have targetNonmaterial : ¬ target.binderSpine.IsMaterialRegion
        (occurrence.diagram.regions region) := by
      intro targetMaterial
      exact sourceMaterial
        ((deiterationPattern_material_iff input selection witness region).mp
          targetMaterial)
    rw [sourceLayout.bodyRegion_nonmaterial region sourceMaterial,
      targetLayout.bodyRegion_nonmaterial (occurrence.diagram.regions region)
        targetNonmaterial]
    rw [deiterationOutputRegionEquiv_frame]
    change targetLayout.frameRegion source.site = targetLayout.frameRegion target.site
    apply congrArg targetLayout.frameRegion
    rfl

private theorem binderRegion_eq_body_of_no_proxy
    (layout : Splice.Input.PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (notProxy : ∀ index, region ≠ input.binderSpine.proxy index) :
    layout.binderRegion region = layout.bodyRegion region := by
  have lookupNone : layout.proxyIndex? region = none := by
    unfold Splice.Input.PlugLayout.proxyIndex?
    cases lookup : indexOf? layout.proxies region with
    | none => simp [lookup]
    | some found =>
        have foundEq := indexOf?_sound lookup
        have member : region ∈ layout.proxies := by
          rw [← foundEq]
          exact List.get_mem _ _
        rw [Splice.Input.PlugLayout.proxies, List.mem_map] at member
        obtain ⟨index, _, equality⟩ := member
        exact False.elim (notProxy index equality.symm)
  unfold Splice.Input.PlugLayout.binderRegion
  rw [lookupNone]

theorem deiterationOutputRegionEquiv_binder
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.binderRegion region) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.binderRegion
          ((deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
            region) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  by_cases isProxy : ∃ index, region = source.binderSpine.proxy index
  · obtain ⟨index, equality⟩ := isProxy
    subst region
    let targetIndex := Fin.cast
      (deiterationPattern_proxyCount_eq input selection witness) index
    rw [sourceLayout.binderRegion_proxy index,
      deiterationPattern_proxy_alignment input selection witness index,
      targetLayout.binderRegion_proxy targetIndex,
      deiterationOutputRegionEquiv_frame]
    exact congrArg targetLayout.frameRegion
      (deiterationBinderTarget_alignment input selection witness index)
  · have sourceNoProxy : ∀ index, region ≠ source.binderSpine.proxy index := by
      intro index equality
      exact isProxy ⟨index, equality⟩
    have targetNoProxy : ∀ index,
        occurrence.diagram.regions region ≠ target.binderSpine.proxy index := by
      intro targetIndex equality
      let sourceIndex := Fin.cast
        (deiterationPattern_proxyCount_eq input selection witness).symm targetIndex
      have aligned := deiterationPattern_proxy_alignment input selection witness sourceIndex
      have castEq : Fin.cast
          (deiterationPattern_proxyCount_eq input selection witness) sourceIndex =
          targetIndex := by
        apply Fin.ext
        rfl
      rw [castEq] at aligned
      apply sourceNoProxy sourceIndex
      apply occurrence.diagram.regions.injective
      exact equality.trans aligned.symm
    rw [binderRegion_eq_body_of_no_proxy sourceLayout region sourceNoProxy,
      binderRegion_eq_body_of_no_proxy targetLayout
        (occurrence.diagram.regions region) targetNoProxy]
    exact deiterationOutputRegionEquiv_body input selection witness region

@[simp] theorem deiterationOutputNodeEquiv_frame
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : Fin (deiterationRemoved input selection).val.nodeCount) :
    deiterationOutputNodeEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.frameNode node) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.frameNode node := by
  exact finiteSumEquiv_left _ _ node

@[simp] theorem deiterationOutputNodeEquiv_pattern
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.nodeCount) :
    deiterationOutputNodeEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.patternNode node) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.patternNode
          ((deiterationPatternOccurrenceEquiv input selection witness).diagram.nodes node) := by
  exact finiteSumEquiv_right _ _ node

@[simp] theorem deiterationOutputWireEquiv_quotient
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    deiterationOutputWireEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.frameWire wire) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.frameWire
          (deiterationQuotientEquiv input selection witness wire) := by
  exact finiteSumEquiv_left _ _ wire

@[simp] theorem deiterationOutputWireEquiv_internal
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire :
      (deiterationReinsertInput input selection witness).plugLayout.internalWires.Carrier) :
    deiterationOutputWireEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.internalWire wire) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.internalWire
          (deiterationInternalWireEquiv input selection witness wire) := by
  exact finiteSumEquiv_right _ _ wire

end VisualProof.Rule.IterationSoundness
