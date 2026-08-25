import VisualProof.Rule.Completeness.Comprehension.Normalization.Exposure

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive


/-! One edit-indexed traversal materializes an argument primitive directly
from the recorded full external tuple at every selected Formal site. The
current argument tuple lives in the authoritative external context, so every
site is obtained only by substitution through its recorded tuple. -/

mutual
  def argumentRegionEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : Region sourceWires,
        Transform.RegionEdit operation frame data source :=
    match recordedSites with
    | .mk childSites =>
        let child := argumentItemsEdit childSites current operation
          (frame.append _) (operation.appendData frame data _) selectedSite
        ⟨.mk _ child.1, .mk child.2⟩
  termination_by structural recordedSites

  def argumentItemsEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : ItemSeq sourceWires,
        Transform.ItemsEdit operation frame data source :=
    match recordedSites with
    | .nil _ => ⟨.nil, .nil⟩
    | .cons itemSites tailSites =>
        let item := argumentItemEdit itemSites current operation frame data
          selectedSite
        let tail := argumentItemsEdit tailSites current operation frame data
          selectedSite
        ⟨.cons item.1 tail.1, .cons item.2 tail.2⟩
  termination_by structural recordedSites

  def argumentItemEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : Item sourceWires,
        Transform.ItemEdit operation frame data source :=
    match recordedSites with
    | .atom head ports => ⟨_, .atom head ports⟩
    | .selectedAtom _ siteData =>
        let application := current.map (fun wire =>
          EqualityNormalization.formalSubstitution siteData.2 wire)
        ⟨_, .selectedAtom application
          (selectedSite frame data siteData.2)⟩
    | .identity signature arity ports =>
        ⟨_, .identity signature arity ports⟩
    | .cut childSites =>
        let child := argumentRegionEdit childSites current operation frame data
          selectedSite
        ⟨.cut child.1, .cut child.2⟩
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame) :
      (argumentRegionEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val =
        recordedSites.selectedPaths :=
    match recordedSites with
    | .mk childSites => by
        simpa [argumentRegionEdit, Region.incidencePaths,
          RegionSites.selectedPaths, Transform.Frame.append] using
          argumentItemsEdit_selectedPaths childSites current operation
            (frame.append _) _ _ (invariant.append _) 0
  termination_by structural recordedSites

  theorem argumentItemsEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame)
      (itemIndex : Nat) :
      (argumentItemsEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val itemIndex =
        recordedSites.selectedPaths itemIndex :=
    match recordedSites with
    | .nil _ => rfl
    | .cons itemSites tailSites => by
        simp only [argumentItemsEdit, ItemSeq.incidencePaths,
          ItemsSites.selectedPaths]
        rw [argumentItemEdit_selectedPaths itemSites current operation frame
          data selectedSite invariant itemIndex,
          argumentItemsEdit_selectedPaths tailSites current operation frame
            data selectedSite invariant (itemIndex + 1)]
  termination_by structural recordedSites

  theorem argumentItemEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame)
      (itemIndex : Nat) :
      (argumentItemEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val itemIndex =
        recordedSites.selectedPaths itemIndex :=
    match recordedSites with
    | .atom head ports => by
        have headNe := Ne.symm (invariant.selectedFresh head)
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths, headNe, portsZero]
    | .selectedAtom ports siteData => by
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage current
          (WireRenaming.comp frame.sourceKeep
            (EqualityNormalization.formalSubstitution siteData.2))
          frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh
            (EqualityNormalization.formalSubstitution siteData.2 wire)))
        simp only [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths]
        change Vars.countIndex frame.selected.index.val
          (current.map (fun wire => frame.sourceKeep
            (EqualityNormalization.formalSubstitution siteData.2 wire))) = 0
          at portsZero
        rw [Vars.map_map, portsZero]
        rfl
    | .identity signature arity ports => by
        have portsZero := countPorts_map_eq_zero_of_no_preimage arity ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths, portsZero]
    | .cut childSites => by
        simp only [argumentItemEdit, Item.incidencePaths,
          ItemSites.selectedPaths]
        rw [argumentRegionEdit_selectedPaths childSites current operation
          frame data selectedSite invariant]
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentRegionEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentRegionEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals _ _ _ childSites =>
      by
        unfold argumentRegionEdit
        apply congrArg (Region.mk _)
        exact argumentItemsEdit_source_independent
          (recordedOperation := recordedOperation) (external := external)
          childSites current
          firstOperation (firstFrame.append _) _ _ secondOperation
          (secondFrame.append _) _ _ (by
            intro wireSignature wire
            apply Var.appendCases (left := common) (right := _)
              (motive := fun wire =>
                (firstFrame.append _).sourceKeep wire =
                  (secondFrame.append _).sourceKeep wire)
            · intro inheritedSignature inherited
              simpa [Transform.Frame.append, WireRenaming.appendRight] using
                congrArg
                  (fun wire : Var sourceWires inheritedSignature =>
                    wire.appendLeft locals)
                  (sourceKeepEq inherited)
            · intro localSignature localWire
              simp [Transform.Frame.append, WireRenaming.appendRight])
          (congrArg
            (fun wire : Var sourceWires (.rel currentArguments) =>
              wire.appendLeft locals)
            selectedEq)
  termination_by structural recordedSites

  theorem argumentItemsEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentItemsEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentItemsEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | .nil evidence => rfl
    | .cons itemSites tailSites =>
      by
        unfold argumentItemsEdit
        have itemEq := argumentItemEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            itemSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq
        have tailEq := argumentItemsEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            tailSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq
        change ItemSeq.cons
            (argumentItemEdit itemSites current firstOperation firstFrame
              firstData firstSelected).1
            (argumentItemsEdit tailSites current firstOperation firstFrame
              firstData firstSelected).1 =
          ItemSeq.cons
            (argumentItemEdit itemSites current secondOperation secondFrame
              secondData secondSelected).1
            (argumentItemsEdit tailSites current secondOperation secondFrame
              secondData secondSelected).1
        rw [itemEq, tailEq]
  termination_by structural recordedSites

  theorem argumentItemEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentItemEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentItemEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | .atom head ports =>
      by
        unfold argumentItemEdit
        change Item.atom (firstFrame.sourceKeep head)
            (ports.map fun wire => firstFrame.sourceKeep wire) =
          Item.atom (secondFrame.sourceKeep head)
            (ports.map fun wire => secondFrame.sourceKeep wire)
        rw [sourceKeepEq head, Vars.map_congr ports _ _ sourceKeepEq]
    | .selectedAtom ports siteData =>
      by
        unfold argumentItemEdit
        change Item.atom firstFrame.selected
            ((current.map fun wire =>
              EqualityNormalization.formalSubstitution siteData.2 wire).map
                fun wire => firstFrame.sourceKeep wire) =
          Item.atom secondFrame.selected
            ((current.map fun wire =>
              EqualityNormalization.formalSubstitution siteData.2 wire).map
                fun wire => secondFrame.sourceKeep wire)
        rw [selectedEq]
        apply congrArg (Item.atom secondFrame.selected)
        apply Vars.map_congr
        exact sourceKeepEq
    | .identity signature arity ports =>
      by
        unfold argumentItemEdit
        change Item.identity signature arity
            (fun position => firstFrame.sourceKeep (ports position)) =
          Item.identity signature arity
            (fun position => secondFrame.sourceKeep (ports position))
        apply congrArg (Item.identity signature arity)
        funext position
        exact sourceKeepEq (ports position)
    | .cut childSites =>
      by
        unfold argumentItemEdit
        exact congrArg Item.cut
          (argumentRegionEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            childSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq)
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentRegionEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedRegionPresentation (argumentRegionEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .mk childSites => by
        unfold argumentRegionEdit
        change Region.adjoinAt _ .nil
            (argumentItemsEdit childSites current operation
              (frame.append _) (operation.appendData frame data _)
              selectedSite).2.run =
          Region.adjoinAt _ .nil
            (retainedItemsPresentation
              (argumentItemsEdit childSites next
                (normalizationOperation targetArguments)
                ({ sourceKeep := (frame.append _).targetKeep
                   targetKeep := (frame.append _).targetKeep
                   selected := (targetSelected frame data).appendLeft _ } :
                  Transform.Frame targetArguments _ _ _)
                PUnit.unit (fun _ _ _ => PUnit.unit)).1)
        rw [← targetSelected_append frame data]
        exact congrArg (Region.adjoinAt _ .nil)
          (argumentItemsEdit_endpoint_eq childSites current next operation
            (frame.append _) (operation.appendData frame data _) selectedSite
            targetSelected targetSelected_append siteEndpoint)
  termination_by structural recordedSites

  theorem argumentItemsEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentItemsEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedItemsPresentation (argumentItemsEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .nil evidence => rfl
    | .cons itemSites tailSites => by
        unfold argumentItemsEdit
        change
          (argumentItemEdit itemSites current operation frame data
              selectedSite).2.run.conjoin
            (argumentItemsEdit tailSites current operation frame data
              selectedSite).2.run =
          retainedItemsPresentation (.cons
            (argumentItemEdit itemSites next
              (normalizationOperation targetArguments)
              ({ sourceKeep := frame.targetKeep
                 targetKeep := frame.targetKeep
                 selected := targetSelected frame data } :
                Transform.Frame targetArguments common targetWires targetWires)
              PUnit.unit (fun _ _ _ => PUnit.unit)).1
            (argumentItemsEdit tailSites next
              (normalizationOperation targetArguments)
              ({ sourceKeep := frame.targetKeep
                 targetKeep := frame.targetKeep
                 selected := targetSelected frame data } :
                Transform.Frame targetArguments common targetWires targetWires)
              PUnit.unit (fun _ _ _ => PUnit.unit)).1)
        rw [argumentItemEdit_endpoint_eq itemSites current next operation frame
          data selectedSite targetSelected targetSelected_append siteEndpoint]
        rw [argumentItemsEdit_endpoint_eq tailSites current next operation frame
          data selectedSite targetSelected targetSelected_append siteEndpoint]
        rfl
  termination_by structural recordedSites

  theorem argumentItemEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentItemEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedItemPresentation (argumentItemEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .atom head ports => rfl
    | .selectedAtom ports siteData => by
        unfold argumentItemEdit Transform.ItemEdit.run
        exact siteEndpoint frame data siteData.2
    | .identity signature arity ports => rfl
    | .cut childSites => by
        unfold argumentItemEdit Transform.ItemEdit.run
        exact congrArg (fun child => Region.singleton (.cut child))
          (argumentRegionEdit_endpoint_eq childSites current next operation
            frame data selectedSite targetSelected targetSelected_append
            siteEndpoint)
  termination_by structural recordedSites
end


/-- The computed Projection target is the canonical generated source for the
shorter tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentProjectionEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (before ++ signature :: after)) :
    let frame := Argument.Projection.rootFrame outer localBefore localAfter
      before after signature
    let head := Argument.Projection.targetHead outer localBefore localAfter
      before after
    let generated := argumentItemsEdit recordedSites current
      (Argument.Projection.operation before after signature) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      (Argument.Projection.Vars.dropAt before current)
      (normalizationOperation (before ++ after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame (before ++ after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
        (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++ .rel (before ++ after) :: localAfter) .nil
        generated.2.run)
      (.mk (localBefore ++ .rel (before ++ after) :: localAfter) follow.1) := by
  dsimp only
  let frame := Argument.Projection.rootFrame outer localBefore localAfter
    before after signature
  let head := Argument.Projection.targetHead outer localBefore localAfter
    before after
  let follow := argumentItemsEdit recordedSites
    (Argument.Projection.Vars.dropAt before current)
    (normalizationOperation (before ++ after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame (before ++ after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
      (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let shorter : Region outer :=
    .mk (localBefore ++ .rel (before ++ after) :: localAfter) follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    (Argument.Projection.Vars.dropAt before current)
    (Argument.Projection.operation before after signature) frame head
    (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [Argument.Projection.operation]
      rw [Argument.Projection.Vars.dropAt_map,
        Argument.Projection.Vars.dropAt_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++ .rel (before ++ after) :: localAfter) .nil
      (argumentItemsEdit recordedSites current
        (Argument.Projection.operation before after signature) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation shorter := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso shorter)

/-- The computed Permutation target is the canonical generated source for the
shorter tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentPermutationEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after)) :
    let frame := ArgumentPermutation.rootFrame outer localBefore localAfter
      (signature :: before ++ after) (before ++ signature :: after)
    let head := ArgumentPermutation.targetHead outer localBefore localAfter
      (before ++ signature :: after)
    let generated := argumentItemsEdit recordedSites current
      (ArgumentPermutation.operation (signature :: before ++ after)
        (before ++ signature :: after)
        (ArgumentPermutation.Permutation.moveHead signature before after)) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars current)
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame (before ++ signature :: after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter))
        (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++ .rel (before ++ signature :: after) :: localAfter) .nil
        generated.2.run)
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter) follow.1) := by
  dsimp only
  let frame := ArgumentPermutation.rootFrame outer localBefore localAfter
    (signature :: before ++ after) (before ++ signature :: after)
  let head := ArgumentPermutation.targetHead outer localBefore localAfter
    (before ++ signature :: after)
  let follow := argumentItemsEdit recordedSites
    ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars current)
    (normalizationOperation (before ++ signature :: after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame (before ++ signature :: after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter))
      (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let shorter : Region outer :=
    .mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter) follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
      current)
    (ArgumentPermutation.operation (signature :: before ++ after)
      (before ++ signature :: after)
      (ArgumentPermutation.Permutation.moveHead signature before after))
    frame head (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [ArgumentPermutation.operation]
      rw [ArgumentPermutation.Permutation.moveHead_map,
        ArgumentPermutation.Permutation.moveHead_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++ .rel (before ++ signature :: after) :: localAfter) .nil
      (argumentItemsEdit recordedSites current
        (ArgumentPermutation.operation (signature :: before ++ after)
          (before ++ signature :: after)
          (ArgumentPermutation.Permutation.moveHead signature before after)) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation shorter := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso shorter)


/-- The computed Duplicate target is the canonical generated source for the
duplicated tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentDuplicateEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (before ++ signature :: after)) :
    let frame := Argument.Duplicate.rootFrame outer localBefore localAfter
      before after signature
    let head := Argument.Duplicate.targetHead outer localBefore localAfter
      before after signature
    let generated := argumentItemsEdit recordedSites current
      (Argument.Duplicate.operation before after signature) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      (Argument.Duplicate.Vars.duplicateAt before current)
      (normalizationOperation (before ++ signature :: signature :: after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame
        (before ++ signature :: signature :: after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter))
        (outer ++ (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)
        .nil generated.2.run)
      (.mk (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)
        follow.1) := by
  dsimp only
  let frame := Argument.Duplicate.rootFrame outer localBefore localAfter
    before after signature
  let head := Argument.Duplicate.targetHead outer localBefore localAfter before
    after signature
  let follow := argumentItemsEdit recordedSites
    (Argument.Duplicate.Vars.duplicateAt before current)
    (normalizationOperation (before ++ signature :: signature :: after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame
      (before ++ signature :: signature :: after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter))
      (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let duplicated : Region outer :=
    .mk (localBefore ++
      .rel (before ++ signature :: signature :: after) :: localAfter)
      follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    (Argument.Duplicate.Vars.duplicateAt before current)
    (Argument.Duplicate.operation before after signature) frame head
    (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [Argument.Duplicate.operation]
      rw [Argument.Duplicate.Vars.duplicateAt_map,
        Argument.Duplicate.Vars.duplicateAt_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)
      .nil
      (argumentItemsEdit recordedSites current
        (Argument.Duplicate.operation before after signature) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation duplicated := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso duplicated)


/-- One actual projection-extension CPS stage. The long-argument source and
its dropping edit are derived together from the single recorded traversal;
the directed local rule is then used in its extension orientation. -/
theorem argumentProjectionStage
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++
        .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites next
          (Argument.Projection.operation before after signature)
          (Argument.Projection.rootFrame outer localBefore localAfter before
            after signature)
          (Argument.Projection.targetHead outer localBefore localAfter before
            after)
          (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++ .rel (before ++ after) :: localAfter)
        (argumentItemsEdit recordedSites
          (Argument.Projection.Vars.dropAt before next)
          (normalizationOperation (before ++ after))
          ({
            sourceKeep :=
              (Argument.Projection.rootFrame outer localBefore localAfter
                before after signature).targetKeep
            targetKeep :=
              (Argument.Projection.rootFrame outer localBefore localAfter
                before after signature).targetKeep
            selected := Argument.Projection.targetHead outer localBefore
              localAfter before after
          } : Transform.Frame (before ++ after)
            (outer ++ (localBefore ++ localAfter))
            (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
            (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation before after signature)
    (Argument.Projection.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Projection.targetHead outer localBefore localAfter before after)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description outer := {
    before := before
    after := after
    localBefore := localBefore
    localAfter := localAfter
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  let prepare := prepare.rawIso
    (argumentProjectionEndpointIso recordedSites next).symm
  have localTargetCanonical : description.target.Canonical :=
    request.occurrence.context.holeCanonical description.target
      prepare.rawPreparedCanonical
  have localExtension :=
    description.target_source_extension localTargetCanonical
  have filledExtension := request.occurrence.context.extendCanonical
    description.target description.source prepare.rawPreparedCanonical
      localExtension.1 localExtension.2
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical :=
    filledExtension.1
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (prepare.rawPreparedExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := Argument.Projection.Local
    inject := fun step => Step.argumentProjection step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso
    localStep := .mk (.extend description)
    preparation := prepare.telescope
  }
  exact branch.derive

/-- One actual argument-permutation CPS stage, generated directly from the
recorded selected applications. -/
theorem argumentPermutationStage
    {recordedArguments external before after outer
      localBefore localAfter recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites
          ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
            current)
          (normalizationOperation (before ++ signature :: after))
          ({ sourceKeep :=
              (ArgumentPermutation.rootFrame outer localBefore localAfter
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             targetKeep :=
              (ArgumentPermutation.rootFrame outer localBefore localAfter
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             selected := ArgumentPermutation.targetHead outer localBefore
               localAfter (before ++ signature :: after) } :
            Transform.Frame (before ++ signature :: after)
              (outer ++ (localBefore ++ localAfter))
              (outer ++ (localBefore ++
                .rel (before ++ signature :: after) :: localAfter))
              (outer ++ (localBefore ++
                .rel (before ++ signature :: after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++ .rel (signature :: before ++ after) :: localAfter)
        (argumentItemsEdit recordedSites current
          (ArgumentPermutation.operation (signature :: before ++ after)
            (before ++ signature :: after)
            (ArgumentPermutation.Permutation.moveHead signature before after))
          (ArgumentPermutation.rootFrame outer localBefore localAfter
            (signature :: before ++ after) (before ++ signature :: after))
          (ArgumentPermutation.targetHead outer localBefore localAfter
            (before ++ signature :: after))
          (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites current
    (ArgumentPermutation.operation (signature :: before ++ after)
      (before ++ signature :: after)
      (ArgumentPermutation.Permutation.moveHead signature before after))
    (ArgumentPermutation.rootFrame outer localBefore localAfter
      (signature :: before ++ after) (before ++ signature :: after))
    (ArgumentPermutation.targetHead outer localBefore localAfter
      (before ++ signature :: after))
    (fun _ _ _ => PUnit.unit)
  let description : ArgumentPermutation.Permutes.Description outer := {
    sourceArguments := signature :: before ++ after
    targetArguments := before ++ signature :: after
    before := localBefore
    after := localAfter
    permutation := ArgumentPermutation.Permutation.moveHead signature before after
    items := generated.1
    itemsEdit := generated.2
  }
  have preparedEq :
      (.mk (localBefore ++ .rel (signature :: before ++ after) :: localAfter)
        generated.1 :
        Region outer) = description.source := by
    rfl
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      prepare.rawPreparedCanonical
  have localExtension :=
    ArgumentPermutation.moveHead_source_target_extension
      description.itemsEdit localSourceCanonical
  have filledExtension := request.occurrence.context.extendCanonical
    description.source description.target prepare.rawPreparedCanonical
      localExtension.1 localExtension.2
  have rawPendingCanonical :
      (request.occurrence.context.fill description.target).Canonical :=
    filledExtension.1
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (prepare.rawPreparedExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.source
    rawPending := description.target
    localRule := symmetric ArgumentPermutation.Local
    inject := fun step => Step.argumentPermutation step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso.trans
      (argumentPermutationEndpointIso recordedSites current).symm
    localStep := Or.inl (.permute (.mk description))
    preparation := prepare.telescope
  }
  exact branch.derive

/-- One actual reverse-duplicate contraction CPS stage, generated directly
from the recorded selected applications. -/
theorem argumentDuplicateContractStage
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites next
          (Argument.Duplicate.operation before after signature)
          (Argument.Duplicate.rootFrame outer localBefore localAfter before
            after signature)
          (Argument.Duplicate.targetHead outer localBefore localAfter before
            after signature)
          (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites
          (Argument.Duplicate.Vars.duplicateAt before next)
          (normalizationOperation
            (before ++ signature :: signature :: after))
          ({ sourceKeep :=
              (Argument.Duplicate.rootFrame outer localBefore localAfter
                before after signature).targetKeep
             targetKeep :=
              (Argument.Duplicate.rootFrame outer localBefore localAfter
                before after signature).targetKeep
             selected := Argument.Duplicate.targetHead outer localBefore
               localAfter before after signature } : Transform.Frame
            (before ++ signature :: signature :: after)
            (outer ++ (localBefore ++ localAfter))
            (outer ++ (localBefore ++
              .rel (before ++ signature :: signature :: after) :: localAfter))
            (outer ++ (localBefore ++
              .rel (before ++ signature :: signature :: after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites next
    (Argument.Duplicate.operation before after signature)
    (Argument.Duplicate.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Duplicate.targetHead outer localBefore localAfter before after
      signature)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Duplicate.Duplicates.Description outer := {
    before := before
    after := after
    localBefore := localBefore
    localAfter := localAfter
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  let prepare := prepare.rawIso
    (argumentDuplicateEndpointIso recordedSites next).symm
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical := by
    let exactPendingIso := pendingIso.trans
      (RegionIso.ofEq (show
        (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
          generated.1 : Region outer) = description.source from rfl))
    exact (DiagramContext.fillIso request.occurrence.context exactPendingIso)
      |>.canonical_iff.mp request.pendingCanonical
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    let exactPendingIso := pendingIso.trans
      (RegionIso.ofEq (show
        (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
          generated.1 : Region outer) = description.source from rfl))
    let filledIso := DiagramContext.fillIso request.occurrence.context
      exactPendingIso
    let pendingEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill pending) request.pendingCanonical
        request.pendingExternalTwoEnded
    apply pendingEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · change (request.occurrence.context.fill pending).incidencePaths
          wire.index.val ≠ [] at nonempty
      rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
    · change (request.occurrence.context.fill pending).incidencePaths
          wire.index.val ≠ []
      rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      rawPendingCanonical
  have localExpansion :=
    description.source_target_extension localSourceCanonical
  have filledExpansion := request.occurrence.context.extendCanonical
    description.source description.target rawPendingCanonical
      localExpansion.1 localExpansion.2
  have derivedRawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (rawPendingExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExpansion.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := symmetric Argument.Duplicate.Local
    inject := fun step => Step.argumentDuplicate step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := filledExpansion.1
    rawPreparedExternalTwoEnded := derivedRawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso
    localStep := Or.inr (.duplicate (.mk description))
    preparation := prepare.telescope
  }
  exact branch.derive


theorem varsExtendHEqRight
    (initial : Vars context initialSignatures)
    {firstSignatures secondSignatures : List Sig}
    (first : Vars context firstSignatures)
    (second : Vars context secondSignatures)
    (signaturesEq : firstSignatures = secondSignatures)
    (equal : HEq first second) :
    HEq (Vars.extend initial first) (Vars.extend initial second) := by
  cases signaturesEq
  have valuesEq : first = second := eq_of_heq equal
  cases valuesEq
  rfl

/-- Split an intrinsic wire into the unique list prefix and suffix around its
signature. -/
theorem intrinsicVar_position
    (wire : Var external signature) :
    ∃ before after, external = before ++ signature :: after ∧
      HEq wire (Var.appendRight before
        (.here : Var (signature :: after) signature)) := by
  induction wire with
  | @here signature after =>
      exact ⟨[], after, rfl, HEq.rfl⟩
  | there wire induction =>
      obtain ⟨before, after, contextEq, wireEq⟩ := induction
      cases contextEq
      cases wireEq
      refine ⟨_ :: before, after, rfl, ?_⟩
      exact heq_of_eq rfl

theorem EqualityNormalization.formalPorts_cons_of_nonempty
    (nonempty : arguments ≠ []) :
    ∃ (signature : Sig) (rest : List Sig)
        (head : Var arguments signature) (tail : Vars arguments rest),
      arguments = signature :: rest ∧
        HEq (EqualityNormalization.formalPorts arguments)
          (Vars.cons head tail) := by
  cases arguments with
  | nil => exact (nonempty rfl).elim
  | cons signature rest =>
      refine ⟨signature, rest, .here,
        (EqualityNormalization.formalPorts rest).map fun wire => .there wire,
        rfl, ?_⟩
      simp only [EqualityNormalization.formalPorts,
        Erasure.Exposure.identityBoundary, Vars.map]
      exact HEq.rfl

end VisualProof.Rule.Completeness.Comprehension
