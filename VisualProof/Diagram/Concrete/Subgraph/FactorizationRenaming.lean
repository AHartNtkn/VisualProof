import VisualProof.Diagram.Concrete.Subgraph.FactorizationStructure

namespace VisualProof

namespace InsertionCompilation

/-- Apply a typed wire renaming to a packed variable. -/
def renamePacked
    (rho : WireRenaming source target) :
    PackedVar source → PackedVar target
  | ⟨sig, value⟩ => ⟨sig, rho value⟩

private theorem denseIndex_value_congr
    [DecidableEq α]
    (values : List α)
    {left right : α}
    (same : left = right)
    (leftMember : left ∈ values)
    (rightMember : right ∈ values) :
    DenseList.index values left leftMember =
      DenseList.index values right rightMember := by
  subst right
  rfl

/--
The fragment-root interface is renamed by the authoritative intrinsic
attachment.  Root-local fragment wires remain internal to `OpenCompilation`;
only its boundary classes enter the enclosing insertion-site environment.
-/
def rootFragmentRenaming
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    WireRenaming fragmentCompiled.openDiagram.classes
      compiled.site.frame.visible.sigs :=
  compiled.intrinsicAttachment.classMap

/-- The root-interface renaming is definitionally the intrinsic class map. -/
theorem rootFragmentRenaming_contextAction
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (value : PackedVar fragmentCompiled.openDiagram.classes) :
    renamePacked (rootFragmentRenaming compiled) value =
      renamePacked compiled.intrinsicAttachment.classMap value :=
  rfl

/-- Pulling an environment back through the root interface uses its class map. -/
theorem rootFragmentRenaming_extendEnvironment
    {pre : PreModel}
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (environment : Env pre compiled.site.frame.visible.sigs) :
    Env.comp environment (rootFragmentRenaming compiled) =
      Env.comp environment compiled.intrinsicAttachment.classMap :=
  rfl

/--
An intrinsic boundary mismatch is precisely a mismatch of the concrete targets
chosen at the representative and queried ordered positions.
-/
theorem intrinsicBoundaryMismatch_iff_target
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (position : Fin fragment.val.boundary.length) :
    renamePacked compiled.intrinsicAttachment.classMap
        (fragmentCompiled.boundaryPackedAt position) ≠
          compiled.targetPackedAt position ↔
      attachment.representativeTarget
          (fragment.val.boundary.get position)
          (List.get_mem fragment.val.boundary position) ≠
        attachment.target position := by
  generalize packedEquality : fragmentCompiled.boundaryPackedAt position = packed
  cases packed with
  | mk sig fiber =>
      have sourceOrigin := fragmentCompiled.boundaryPackedAt_origin position
      rw [packedEquality] at sourceOrigin
      have classOrigin :=
        compiled.intrinsicAttachment_classMap_eq_representative fiber
      change
        (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
            PackedVar compiled.site.frame.visible.sigs) ≠
          compiled.targetPackedAt position ↔ _
      rw [classOrigin]
      apply Iff.trans
        (not_congr
          (compiled.targetPackedAt_eq_iff
            (attachment.representativePosition
              (ExtractedBoundaryCompiler.wireOfPacked
                fragment.val.diagram
                (ConcreteElaboration.openBoundaryWires fragment.val)
                (⟨sig, fiber⟩ :
                  PackedVar fragmentCompiled.openDiagram.classes))
              (compiled.intrinsicClassWire_mem_boundary fiber))
            position))
      unfold ConcreteSpliceAttachment.representativeTarget
      have representativeEquality :
          attachment.representativePosition
              (ExtractedBoundaryCompiler.wireOfPacked
                fragment.val.diagram
                (ConcreteElaboration.openBoundaryWires fragment.val)
                (⟨sig, fiber⟩ :
                  PackedVar fragmentCompiled.openDiagram.classes))
              (compiled.intrinsicClassWire_mem_boundary fiber) =
            attachment.representativePosition
              (fragment.val.boundary.get position)
              (List.get_mem fragment.val.boundary position) := by
        unfold ConcreteSpliceAttachment.representativePosition
        exact denseIndex_value_congr fragment.val.boundary sourceOrigin _ _
      rw [representativeEquality]

end InsertionCompilation

end VisualProof
