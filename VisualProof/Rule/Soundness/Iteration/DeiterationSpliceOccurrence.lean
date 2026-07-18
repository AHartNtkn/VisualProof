import VisualProof.Rule.Soundness.Iteration.DeiterationSpliceMap

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private theorem finCount_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

private theorem deiterationMapFrameRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : CRegion (deiterationRemoved input selection).val.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapFrameRegion region).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapFrameRegion region := by
  cases region <;>
    simp [Splice.Input.PlugLayout.mapFrameRegion,
      CRegion.rename, deiterationOutputRegionEquiv_frame] <;> rfl

theorem deiterationMapPatternRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : CRegion
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapPatternRegion region).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapPatternRegion
          (region.rename
            (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions) := by
  cases region with
  | sheet =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_frame]
      rfl
  | cut parent =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_body]
      rfl
  | bubble parent arity =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_body]
      rfl

theorem deiterationOutputRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.regionCount) :
    ((deiterationReinsertInput input selection witness).plugLayout.plugRaw.regions
        region).rename (deiterationOutputRegionEquiv input selection witness) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.regions
          (deiterationOutputRegionEquiv input selection witness region) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.frame.val.regionCount)
    (n := sourceLayout.materialRegions.count) (fun frameRegion => ?_)
      (fun material => ?_) region
  · change (sourceLayout.plugRegion (sourceLayout.frameRegion frameRegion)).rename
        (deiterationOutputRegionEquiv input selection witness) =
      targetLayout.plugRegion
        (deiterationOutputRegionEquiv input selection witness
          (sourceLayout.frameRegion frameRegion))
    rw [sourceLayout.plugRegion_frameRegion,
      deiterationOutputRegionEquiv_frame,
      targetLayout.plugRegion_frameRegion]
    exact deiterationMapFrameRegion_eq input selection witness
      (source.frame.val.regions frameRegion)
  · change (sourceLayout.plugRegion (sourceLayout.materialRegion material)).rename
        (deiterationOutputRegionEquiv input selection witness) =
      targetLayout.plugRegion
        (deiterationOutputRegionEquiv input selection witness
          (sourceLayout.materialRegion material))
    rw [sourceLayout.plugRegion_materialRegion,
      deiterationOutputRegionEquiv_material,
      targetLayout.plugRegion_materialRegion,
      deiterationMaterialEquiv_origin]
    calc
      (sourceLayout.mapPatternRegion
          (source.pattern.val.diagram.regions
            (sourceLayout.materialRegions.origin material))).rename
            (deiterationOutputRegionEquiv input selection witness) =
        targetLayout.mapPatternRegion
          ((source.pattern.val.diagram.regions
            (sourceLayout.materialRegions.origin material)).rename
              occurrence.diagram.regions) :=
        deiterationMapPatternRegion_eq input selection witness _
      _ = targetLayout.mapPatternRegion
          (target.pattern.val.diagram.regions
            (occurrence.diagram.regions
              (sourceLayout.materialRegions.origin material))) := by
        exact congrArg targetLayout.mapPatternRegion
          (occurrence.diagram.regions_eq
            (sourceLayout.materialRegions.origin material))

private theorem deiterationMapFrameNode_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : CNode (deiterationRemoved input selection).val.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapFrameNode node).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapFrameNode node := by
  cases node <;>
    simp [Splice.Input.PlugLayout.mapFrameNode, CNode.rename,
      deiterationOutputRegionEquiv_frame] <;> rfl

private noncomputable def deiterationMapPatternNode_corresponds
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {sourceNode : CNode
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount}
    {targetNode : CNode
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).pattern.val.diagram.regionCount}
    (certified : CNode.CertifiedCorresponds
      (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
      sourceNode targetNode) :
    CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      ((deiterationReinsertInput input selection witness).plugLayout
        |>.mapPatternNode sourceNode)
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout
          |>.mapPatternNode targetNode) := by
  let sourceLayout := (deiterationReinsertInput input selection witness).plugLayout
  let targetLayout := (Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)).plugLayout
  cases certified with
  | term sourceRegion targetRegion ports sourceTerm targetTerm regionEq certificate =>
      exact .term (sourceLayout.bodyRegion sourceRegion)
        (targetLayout.bodyRegion targetRegion) ports sourceTerm targetTerm
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq)) certificate
  | atom sourceRegion sourceBinder targetRegion targetBinder regionEq binderEq =>
      exact .atom (sourceLayout.bodyRegion sourceRegion)
        (sourceLayout.binderRegion sourceBinder)
        (targetLayout.bodyRegion targetRegion)
        (targetLayout.binderRegion targetBinder)
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq))
        ((deiterationOutputRegionEquiv_binder input selection witness sourceBinder).trans
          (congrArg targetLayout.binderRegion binderEq))
  | named sourceRegion targetRegion definition arity regionEq =>
      exact .named (sourceLayout.bodyRegion sourceRegion)
        (targetLayout.bodyRegion targetRegion) definition arity
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq))

noncomputable def deiterationOutputNode_correspond
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.nodeCount) :
    CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      ((deiterationReinsertInput input selection witness).plugLayout.plugRaw.nodes node)
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.nodes
          (deiterationOutputNodeEquiv input selection witness node)) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.frame.val.nodeCount)
    (n := source.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
      (fun patternNode => ?_) node
  · change CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      (sourceLayout.plugNode (sourceLayout.frameNode frameNode))
      (targetLayout.plugNode
        (deiterationOutputNodeEquiv input selection witness
          (sourceLayout.frameNode frameNode)))
    rw [sourceLayout.plugNode_frameNode,
      deiterationOutputNodeEquiv_frame,
      targetLayout.plugNode_frameNode]
    exact CNode.CertifiedCorresponds.ofRenameEq _
      (deiterationMapFrameNode_eq input selection witness
        (source.frame.val.nodes frameNode))
  · change CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      (sourceLayout.plugNode (sourceLayout.patternNode patternNode))
      (targetLayout.plugNode
        (deiterationOutputNodeEquiv input selection witness
          (sourceLayout.patternNode patternNode)))
    rw [sourceLayout.plugNode_patternNode,
      deiterationOutputNodeEquiv_pattern,
      targetLayout.plugNode_patternNode]
    exact deiterationMapPatternNode_corresponds input selection witness
      (occurrence.diagram.nodes_correspond patternNode)

end VisualProof.Rule.IterationSoundness
