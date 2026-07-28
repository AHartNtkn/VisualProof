import VisualProof.Diagram.Concrete.Subgraph.FactorizationRetargetSemantics

namespace VisualProof

universe u

/--
Two independently accepted concrete splices related by the checked identity
retarget operation have the same denotation in every premodel.
-/
theorem identity_retarget_sound
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {site : RemovalResult occurrence}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice site extracted.checked direction)
    (sourceResult : ConcreteSpliceResult checked.source)
    (sourceAccepted : splice checked.source = .ok sourceResult)
    (targetResult : ConcreteSpliceResult checked.target)
    (targetAccepted : splice checked.target = .ok targetResult)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv targetResult.checked ↔
      denoteChecked pre definitionEnv sourceResult.checked := by
  obtain ⟨common⟩ :=
    RemovalFactorization.commonAttachmentFrame_complete
      checked.source checked.target
  have targetBridge :=
    RemovalFactorization.CommonAttachmentFrame.denote_target_in_common_frame
      extracted common targetResult targetAccepted pre definitionEnv
  have sourceBridge :=
    RemovalFactorization.CommonAttachmentFrame.denote_source_in_common_frame
      extracted common sourceResult sourceAccepted pre definitionEnv
  have commonEquivalence :=
    RemovalFactorization.CommonAttachmentFrame.intrinsic_splices_equiv_of_checked_retargets
      extracted checked common pre definitionEnv
  exact targetBridge.trans
    (commonEquivalence.trans sourceBridge.symm)

end VisualProof
