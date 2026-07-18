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

end VisualProof.Rule.IterationSoundness
