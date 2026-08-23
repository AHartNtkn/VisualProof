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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
  exact branch.compile

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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
  exact branch.compile

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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
  exact branch.compile

/-- Normalized generated regions are structurally identical after one generic
argument-index equality and the corresponding heterogeneous tuple equality. -/
noncomputable def argumentNormalizationPresentation
    {recordedArguments external firstArguments secondArguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (firstValues : Vars external firstArguments)
    (secondValues : Vars external secondArguments)
    (argumentsEq : firstArguments = secondArguments)
    (valuesEq : HEq firstValues secondValues) :
    RegionIso (WireEquiv.refl common)
      (.mk (.rel firstArguments :: retained)
        (argumentItemsEdit recordedSites firstValues
          (normalizationOperation firstArguments)
          ({ sourceKeep := Transform.Frame.keep common []
              [.rel firstArguments] retained
             targetKeep := Transform.Frame.keep common []
              [.rel firstArguments] retained
             selected := Transform.Frame.insertedHead common [] retained
              (.rel firstArguments) } : Transform.Frame firstArguments
            (common ++ retained)
            (common ++ (.rel firstArguments :: retained))
            (common ++ (.rel firstArguments :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)
      (.mk (.rel secondArguments :: retained)
        (argumentItemsEdit recordedSites secondValues
          (normalizationOperation secondArguments)
          ({ sourceKeep := Transform.Frame.keep common []
              [.rel secondArguments] retained
             targetKeep := Transform.Frame.keep common []
              [.rel secondArguments] retained
             selected := Transform.Frame.insertedHead common [] retained
              (.rel secondArguments) } : Transform.Frame secondArguments
            (common ++ retained)
            (common ++ (.rel secondArguments :: retained))
            (common ++ (.rel secondArguments :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
  subst secondArguments
  cases valuesEq
  exact RegionIso.refl _

/-- The authoritative all-sites region generated by a normalized argument
tuple. Every argument stage consumes this exact representation. -/
def argumentNormalizedRegion
    {recordedArguments external arguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (values : Vars external arguments) : Region common :=
  .mk (.rel arguments :: retained)
    (argumentItemsEdit recordedSites values
      (normalizationOperation arguments)
      ({ sourceKeep := Transform.Frame.keep common [] [.rel arguments] retained
         targetKeep := Transform.Frame.keep common [] [.rel arguments] retained
         selected := Transform.Frame.insertedHead common [] retained
           (.rel arguments) } : Transform.Frame arguments (common ++ retained)
        (common ++ (.rel arguments :: retained))
        (common ++ (.rel arguments :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)).1

/-- One normalized Projection CPS phase. The only mismatch is the dependent
`arguments ++ [] = arguments` presentation, discharged once here. -/
theorem argumentProjectionNormalized
    {recordedArguments external arguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external arguments) (inserted : Var external signature)
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend current (.cons inserted .nil))))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let next := Theory.Vars.extend current (.cons inserted .nil)
  have droppedEq : HEq
      (Argument.Projection.Vars.dropAt arguments next) current :=
    Argument.Projection.Vars.dropAt_extend_singleton current inserted
  let presentation := argumentNormalizationPresentation recordedSites current
    (Argument.Projection.Vars.dropAt arguments next)
    (List.append_nil arguments).symm droppedEq.symm
  let rawPending : Region common :=
    .mk ([] ++ .rel (arguments ++ signature :: []) :: retained)
      (argumentItemsEdit recordedSites next
        (Argument.Projection.operation arguments [] signature)
        (Argument.Projection.rootFrame common [] retained arguments []
          signature)
        (Argument.Projection.targetHead common [] retained arguments [])
        (fun _ _ _ => PUnit.unit)).1
  have pendingEq : argumentNormalizedRegion recordedSites next = rawPending := by
    dsimp only [argumentNormalizedRegion, rawPending]
    apply congrArg (Region.mk (.rel (arguments ++ signature :: []) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (arguments ++ signature :: []))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (arguments ++ signature :: [])) } : Transform.Frame
        (arguments ++ signature :: []) (common ++ retained)
        (common ++ (.rel (arguments ++ signature :: []) :: retained))
        (common ++ (.rel (arguments ++ signature :: []) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation arguments [] signature)
      (Argument.Projection.rootFrame common [] retained arguments [] signature)
      (Argument.Projection.targetHead common [] retained arguments [])
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  have stagedPrepare : request.Preparation
      (.mk ([] ++ .rel (arguments ++ []) :: retained)
        (argumentItemsEdit recordedSites
          (Argument.Projection.Vars.dropAt arguments next)
          (normalizationOperation (arguments ++ []))
          ({ sourceKeep :=
              (Argument.Projection.rootFrame common [] retained arguments []
                signature).targetKeep
             targetKeep :=
              (Argument.Projection.rootFrame common [] retained arguments []
                signature).targetKeep
             selected := Argument.Projection.targetHead common [] retained
               arguments [] } : Transform.Frame (arguments ++ [])
            (common ++ ([] ++ retained))
            (common ++ ([] ++ .rel (arguments ++ []) :: retained))
            (common ++ ([] ++ .rel (arguments ++ []) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    simpa only [argumentNormalizedRegion, Argument.Projection.rootFrame,
      Transform.Frame.replace] using prepare.rawIso presentation
  exact argumentProjectionStage (before := arguments) (after := [])
    (outer := common) (localBefore := []) (localAfter := retained)
      (instantiated := instantiated) recordedSites next
      (request := request) (pendingIso.trans (RegionIso.ofEq pendingEq))
      stagedPrepare

/-- Prepending one recorded argument preserves occurrence validity because it
is exactly Projection's extension direction. -/
theorem argumentPrependValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (inserted : Var external signature) (current : Vars external arguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (currentCanonical : (context.fill
      (argumentNormalizedRegion recordedSites current)).Canonical)
    (currentExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites current))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (.cons inserted current))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (.cons inserted current))) := by
  let next : Vars external ([] ++ signature :: arguments) :=
    .cons inserted current
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation [] arguments signature)
    (Argument.Projection.rootFrame common [] retained [] arguments signature)
    (Argument.Projection.targetHead common [] retained [] arguments)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description common := {
    before := []
    after := arguments
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : argumentNormalizedRegion recordedSites
      (.cons inserted current) = description.source := by
    dsimp only [argumentNormalizedRegion, description, generated, next]
    apply congrArg (Region.mk (.rel (signature :: arguments) :: retained))
    exact argumentItemsEdit_source_independent recordedSites
      (.cons inserted current) (normalizationOperation (signature :: arguments))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (signature :: arguments)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (signature :: arguments)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (signature :: arguments)) } : Transform.Frame
        (signature :: arguments) (common ++ retained)
        (common ++ (.rel (signature :: arguments) :: retained))
        (common ++ (.rel (signature :: arguments) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation [] arguments signature)
      (Argument.Projection.rootFrame common [] retained [] arguments signature)
      (Argument.Projection.targetHead common [] retained [] arguments)
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  let targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites current) := by
    simpa only [description, generated, next, argumentNormalizedRegion] using
      argumentProjectionEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) (before := []) (after := arguments)
        recordedSites next
  let filledTargetIso := DiagramContext.fillIso context targetIso
  have filledTargetCanonical : (context.fill description.target).Canonical :=
    filledTargetIso.canonical_iff.mpr currentCanonical
  have filledTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill description.target) := by
    let currentEndpoint := interface.withBody
      (context.fill (argumentNormalizedRegion recordedSites current))
      currentCanonical currentExternalTwoEnded
    apply currentEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localTargetCanonical : description.target.Canonical :=
    context.holeCanonical description.target filledTargetCanonical
  have localExtension := description.target_source_extension localTargetCanonical
  have filledExtension := context.extendCanonical description.target
    description.source filledTargetCanonical localExtension.1 localExtension.2
  have filledSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (filledTargetExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  rw [sourceEq]
  exact ⟨filledExtension.1, filledSourceExternalTwoEnded⟩

/-- Adding a whole tuple in front of the canonical external tuple preserves
validity, by repeated Projection extension. -/
theorem argumentExtendedValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (added : Vars external arguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (finalCanonical : (context.fill
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (finalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites
          (EqualityNormalization.formalPorts external)))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (Theory.Vars.extend added
        (EqualityNormalization.formalPorts external)))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (Theory.Vars.extend added
            (EqualityNormalization.formalPorts external)))) := by
  induction added with
  | nil => exact ⟨finalCanonical, finalExternalTwoEnded⟩
  | @cons signature rest head tail induction =>
      exact argumentPrependValidity recordedSites head
        (Theory.Vars.extend tail
          (EqualityNormalization.formalPorts external)) interface context
        induction.1 induction.2

/-- Move the current tuple head behind `before`, preserving the authoritative
normalized representation on both sides of the permutation step. -/
theorem argumentPermutationNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after))
    {instantiated : Region common}
    (request : Telescope.Request instantiated
      (argumentNormalizedRegion recordedSites
        ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
          current)))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let moved :=
    (ArgumentPermutation.Permutation.moveHead signature before after).mapVars
      current
  let rawPrepared : Region common :=
    .mk (.rel (signature :: before ++ after) :: retained)
      (argumentItemsEdit recordedSites current
        (ArgumentPermutation.operation (signature :: before ++ after)
          (before ++ signature :: after)
          (ArgumentPermutation.Permutation.moveHead signature before after))
        (ArgumentPermutation.rootFrame common [] retained
          (signature :: before ++ after) (before ++ signature :: after))
        (ArgumentPermutation.targetHead common [] retained
          (before ++ signature :: after))
        (fun _ _ _ => PUnit.unit)).1
  have preparedEq : argumentNormalizedRegion recordedSites current =
      rawPrepared := by
    dsimp only [argumentNormalizedRegion, rawPrepared]
    apply congrArg (Region.mk (.rel (signature :: before ++ after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites current
      (normalizationOperation (signature :: before ++ after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (signature :: before ++ after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (signature :: before ++ after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (signature :: before ++ after)) } : Transform.Frame
        (signature :: before ++ after) (common ++ retained)
        (common ++ (.rel (signature :: before ++ after) :: retained))
        (common ++ (.rel (signature :: before ++ after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (ArgumentPermutation.operation (signature :: before ++ after)
        (before ++ signature :: after)
        (ArgumentPermutation.Permutation.moveHead signature before after))
      (ArgumentPermutation.rootFrame common [] retained
        (signature :: before ++ after) (before ++ signature :: after))
      (ArgumentPermutation.targetHead common [] retained
        (before ++ signature :: after))
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [ArgumentPermutation.rootFrame, Transform.Frame.replace]) (by
          simp [ArgumentPermutation.rootFrame, Transform.Frame.replace])
  have pendingEq : argumentNormalizedRegion recordedSites moved =
      (.mk ([] ++ .rel (before ++ signature :: after) :: retained)
        (argumentItemsEdit recordedSites moved
          (normalizationOperation (before ++ signature :: after))
          ({ sourceKeep :=
              (ArgumentPermutation.rootFrame common [] retained
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             targetKeep :=
              (ArgumentPermutation.rootFrame common [] retained
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             selected := ArgumentPermutation.targetHead common [] retained
               (before ++ signature :: after) } : Transform.Frame
            (before ++ signature :: after) (common ++ ([] ++ retained))
            (common ++ ([] ++ .rel (before ++ signature :: after) :: retained))
            (common ++ ([] ++ .rel (before ++ signature :: after) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    rfl
  exact argumentPermutationStage (outer := common) (localBefore := [])
    (localAfter := retained) (instantiated := instantiated) recordedSites current
    (request := request) (RegionIso.ofEq pendingEq)
    (prepare.rawIso (RegionIso.ofEq preparedEq))

/-- Contract one adjacent duplicated argument while preserving normalized
all-sites regions as the authoritative continuation endpoints. -/
theorem argumentDuplicateNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites next))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites
        (Argument.Duplicate.Vars.duplicateAt before next))) :
    request.Result := by
  let duplicated := Argument.Duplicate.Vars.duplicateAt before next
  let rawPending : Region common :=
    .mk (.rel (before ++ signature :: after) :: retained)
      (argumentItemsEdit recordedSites next
        (Argument.Duplicate.operation before after signature)
        (Argument.Duplicate.rootFrame common [] retained before after signature)
        (Argument.Duplicate.targetHead common [] retained before after signature)
        (fun _ _ _ => PUnit.unit)).1
  have pendingEq : argumentNormalizedRegion recordedSites next = rawPending := by
    dsimp only [argumentNormalizedRegion, rawPending]
    apply congrArg (Region.mk (.rel (before ++ signature :: after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (before ++ signature :: after)) } : Transform.Frame
        (before ++ signature :: after) (common ++ retained)
        (common ++ (.rel (before ++ signature :: after) :: retained))
        (common ++ (.rel (before ++ signature :: after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Duplicate.operation before after signature)
      (Argument.Duplicate.rootFrame common [] retained before after signature)
      (Argument.Duplicate.targetHead common [] retained before after signature)
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Duplicate.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Duplicate.rootFrame, Transform.Frame.replace])
  have preparedEq : argumentNormalizedRegion recordedSites duplicated =
      (.mk ([] ++ .rel (before ++ signature :: signature :: after) :: retained)
        (argumentItemsEdit recordedSites duplicated
          (normalizationOperation (before ++ signature :: signature :: after))
          ({ sourceKeep :=
              (Argument.Duplicate.rootFrame common [] retained before after
                signature).targetKeep
             targetKeep :=
              (Argument.Duplicate.rootFrame common [] retained before after
                signature).targetKeep
             selected := Argument.Duplicate.targetHead common [] retained
               before after signature } : Transform.Frame
            (before ++ signature :: signature :: after)
            (common ++ ([] ++ retained))
            (common ++ ([] ++
              .rel (before ++ signature :: signature :: after) :: retained))
            (common ++ ([] ++
              .rel (before ++ signature :: signature :: after) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    rfl
  exact argumentDuplicateContractStage (outer := common) (localBefore := [])
    (localAfter := retained) (instantiated := instantiated) recordedSites next
    (request := request) (pendingIso.trans (RegionIso.ofEq pendingEq))
    (prepare.rawIso (RegionIso.ofEq preparedEq))

/-- Eliminate an intrinsic wire position into the unique list prefix and
suffix surrounding its signature.  The witness lives only in `Prop`; the
argument telescope consumes it immediately and does not expose a position
certificate as data. -/
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

/-- One argument occurrence is moved next to its canonical external copy and
contracted.  Both primitives are packaged here so the intrinsic-position
eliminator has no caller-visible intermediate endpoint. -/
theorem argumentMoveDuplicateNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external
      (signature :: before ++ signature :: after))
    (next : Vars external (before ++ signature :: after))
    (movedEq :
      (ArgumentPermutation.Permutation.moveHead signature before
        (signature :: after)).mapVars
          current =
        Argument.Duplicate.Vars.duplicateAt before next)
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites next))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let duplicated := Argument.Duplicate.Vars.duplicateAt before next
  let moved :=
    (ArgumentPermutation.Permutation.moveHead signature before
      (signature :: after)).mapVars
      current
  have movedRegionEq : argumentNormalizedRegion recordedSites moved =
      argumentNormalizedRegion recordedSites duplicated := by
    exact congrArg (argumentNormalizedRegion recordedSites) movedEq
  let generated := argumentItemsEdit recordedSites next
    (Argument.Duplicate.operation before after signature)
    (Argument.Duplicate.rootFrame common [] retained before after signature)
    (Argument.Duplicate.targetHead common [] retained before after signature)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Duplicate.Duplicates.Description common := {
    before := before
    after := after
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : description.source =
      argumentNormalizedRegion recordedSites next := by
    dsimp only [description, generated, argumentNormalizedRegion]
    apply congrArg (Region.mk (.rel (before ++ signature :: after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (Argument.Duplicate.operation before after signature)
      (Argument.Duplicate.rootFrame common [] retained before after signature)
      (Argument.Duplicate.targetHead common [] retained before after signature)
      (fun _ _ _ => PUnit.unit)
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (before ++ signature :: after)) } : Transform.Frame
        (before ++ signature :: after) (common ++ retained)
        (common ++ (.rel (before ++ signature :: after) :: retained))
        (common ++ (.rel (before ++ signature :: after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Duplicate.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Duplicate.rootFrame, Transform.Frame.replace])
  let sourceIso : RegionIso (WireEquiv.refl common) description.source
      (argumentNormalizedRegion recordedSites next) := RegionIso.ofEq sourceEq
  let exactSourceIso := sourceIso.trans pendingIso.symm
  let filledSourceIso := DiagramContext.fillIso request.occurrence.context
    exactSourceIso
  have filledSourceCanonical :
      (request.occurrence.context.fill description.source).Canonical :=
    filledSourceIso.canonical_iff.mpr request.pendingCanonical
  have filledSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    let pendingEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill pending)
      request.pendingCanonical request.pendingExternalTwoEnded
    apply pendingEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledSourceIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      filledSourceCanonical
  have localExpansion := description.source_target_extension
    localSourceCanonical
  have filledExpansion := request.occurrence.context.extendCanonical
    description.source description.target filledSourceCanonical
      localExpansion.1 localExpansion.2
  have filledTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (filledSourceExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExpansion.2 wire).length_le _)
  have targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites duplicated) := by
    simpa only [description, generated, argumentNormalizedRegion] using
      argumentDuplicateEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) recordedSites next
  let filledTargetIso := DiagramContext.fillIso request.occurrence.context
    targetIso
  have duplicatedCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites duplicated)).Canonical :=
    filledTargetIso.canonical_iff.mp filledExpansion.1
  have duplicatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (argumentNormalizedRegion recordedSites duplicated)) := by
    let targetEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill description.target) filledExpansion.1
      filledTargetExternalTwoEnded
    apply targetEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
  have movedCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites moved)).Canonical := by
    rw [movedRegionEq]
    exact duplicatedCanonical
  have movedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (argumentNormalizedRegion recordedSites moved)) := by
    rw [movedRegionEq]
    exact duplicatedExternalTwoEnded
  let stageInterface : OpenDiagram request.boundary :=
    request.occurrence.interface
  let stageContext : DiagramContext stageInterface.external common :=
    request.occurrence.context
  have duplicateSourceCanonical :
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated)
        request.endpoint)).Canonical := by
    exact match request.polarity with
      | .positive => by
          simpa only [stageContext] using duplicatedCanonical
      | .negative => by
          simpa only [stageContext] using request.endpointCanonical
  have duplicateSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      stageInterface.boundaryWire
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated)
        request.endpoint)) := by
    exact match request.polarity with
      | .positive => by
          simpa only [stageInterface, stageContext] using
            duplicatedExternalTwoEnded
      | .negative => by
          simpa only [stageInterface, stageContext] using
            request.endpointExternalTwoEnded
  let duplicateRequest : Telescope.Request
      (argumentNormalizedRegion recordedSites duplicated)
      pending := {
    boundary := request.boundary
    source := stageInterface.withBody
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated) request.endpoint))
      duplicateSourceCanonical duplicateSourceExternalTwoEnded
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := exactOccurrence stageInterface
      stageContext (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated) request.endpoint)
      duplicateSourceCanonical duplicateSourceExternalTwoEnded
    instantiatedCanonical := duplicatedCanonical
    instantiatedExternalTwoEnded := duplicatedExternalTwoEnded
    pendingCanonical := request.pendingCanonical
    pendingExternalTwoEnded := request.pendingExternalTwoEnded
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := request.continuation
  }
  let duplicatePreparation : duplicateRequest.Preparation
      (argumentNormalizedRegion recordedSites duplicated) := {
    prepared := argumentNormalizedRegion recordedSites duplicated
    preparedCanonical := duplicatedCanonical
    preparedExternalTwoEnded := duplicatedExternalTwoEnded
    rawPreparedCanonical := duplicatedCanonical
    rawPreparedExternalTwoEnded := duplicatedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := Telescope.refl request.polarity request.occurrence.interface
      request.occurrence.context duplicatedCanonical
      duplicatedExternalTwoEnded request.continuation.1
  }
  have duplicateCompiled := argumentDuplicateNormalized recordedSites next
    duplicateRequest pendingIso duplicatePreparation
  have duplicateTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      (argumentNormalizedRegion recordedSites moved) request.endpoint
      movedCanonical movedExternalTwoEnded request.endpointCanonical
      request.endpointExternalTwoEnded := by
    simpa only [movedRegionEq] using
      Telescope.Compiles.toTelescope request.polarity
      request.occurrence.interface request.occurrence.context
      duplicatedCanonical duplicatedExternalTwoEnded request.endpointCanonical
      request.endpointExternalTwoEnded request.continuation.1
      duplicateCompiled
  let permutationRequest : Telescope.Request instantiated
      (argumentNormalizedRegion recordedSites moved) := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := request.instantiatedCanonical
    instantiatedExternalTwoEnded := request.instantiatedExternalTwoEnded
    pendingCanonical := movedCanonical
    pendingExternalTwoEnded := movedExternalTwoEnded
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := duplicateTelescope
  }
  let permutationPreparation : permutationRequest.Preparation
      (argumentNormalizedRegion recordedSites current) := {
    prepared := prepare.prepared
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    preparedIso := prepare.preparedIso
    telescope := prepare.telescope
  }
  exact argumentPermutationNormalized recordedSites current permutationRequest
    permutationPreparation

/-- Contract every leading actual argument against its canonical occurrence
in the external tuple.  The recursion is on the existing intrinsic `Vars`
value; each head position is eliminated in `Prop` and immediately consumed by
the combined move/duplicate phase. -/
theorem argumentVarsContractTelescope
    {recordedArguments external addedArguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (added : Vars external addedArguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {endpoint : Region common}
    (finalCanonical : (context.fill (argumentNormalizedRegion recordedSites
      (EqualityNormalization.formalPorts external))).Canonical)
    (finalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (argumentNormalizedRegion
        recordedSites (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      finalCanonical finalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend added
          (EqualityNormalization.formalPorts external))) endpoint
      (argumentExtendedValidity recordedSites added interface context
        finalCanonical finalExternalTwoEnded).1
      (argumentExtendedValidity recordedSites added interface context
        finalCanonical finalExternalTwoEnded).2
      endpointCanonical endpointExternalTwoEnded := by
  induction added with
  | nil => exact continuation
  | @cons signature restArguments head tail induction =>
      let next := Theory.Vars.extend tail
        (EqualityNormalization.formalPorts external)
      let current := Theory.Vars.cons head next
      have nextValidity := argumentExtendedValidity recordedSites tail
        interface context finalCanonical finalExternalTwoEnded
      have currentValidity := argumentExtendedValidity recordedSites
        (.cons head tail) interface context finalCanonical
        finalExternalTwoEnded
      have tailTelescope := induction
      obtain ⟨before, after, externalEq, headEq⟩ := intrinsicVar_position head
      cases externalEq
      cases headEq
      let prefixValues : Vars (before ++ signature :: after) before :=
        (EqualityNormalization.formalPorts before).map fun wire =>
          wire.appendLeft (signature :: after)
      let suffixValues : Vars (before ++ signature :: after) after :=
        (EqualityNormalization.formalPorts after).map fun wire =>
          Var.appendRight before (.there wire)
      let selected : Var (before ++ signature :: after) signature :=
        Var.appendRight before (.here : Var (signature :: after) signature)
      have formalEq : EqualityNormalization.formalPorts
          (before ++ signature :: after) =
          Theory.Vars.extend prefixValues (.cons selected suffixValues) := by
        rw [EqualityNormalization.formalPorts_append before
          (signature :: after)]
        dsimp only [prefixValues, selected, suffixValues]
        apply congrArg (Theory.Vars.extend
          ((EqualityNormalization.formalPorts before).map fun wire =>
            wire.appendLeft (signature :: after)))
        simp only [EqualityNormalization.formalPorts,
          Erasure.Exposure.identityBoundary, Theory.Vars.map,
          Theory.Vars.extend]
        apply congrArg (Theory.Vars.cons
          (Var.appendRight before
            (.here : Var (signature :: after) signature)))
        rw [Theory.Vars.map_map]
      let stageBeforeValues := Theory.Vars.extend tail prefixValues
      let stageNext := Theory.Vars.extend stageBeforeValues
        (Theory.Vars.cons selected suffixValues)
      let stageCurrent := Theory.Vars.cons selected
        (Theory.Vars.extend stageBeforeValues
          (Theory.Vars.cons selected suffixValues))
      have nextEq : HEq stageNext next := by
        dsimp only [stageNext, stageBeforeValues, next]
        exact (Theory.Vars.extend_assoc tail prefixValues
          (Theory.Vars.cons selected suffixValues)).trans
            (heq_of_eq (congrArg (Theory.Vars.extend tail) formalEq.symm))
      have currentEq : HEq stageCurrent current := by
        dsimp only [stageCurrent, current]
        congr 1
        exact List.append_assoc _ _ _
      have movedEq :
          (ArgumentPermutation.Permutation.moveHead signature
            (restArguments ++ before) (signature :: after)).mapVars
              stageCurrent =
            Argument.Duplicate.Vars.duplicateAt
              (restArguments ++ before) stageNext := by
        dsimp only [stageCurrent, stageNext, stageBeforeValues]
        rw [ArgumentPermutation.Permutation.moveHead_cons_extend]
        rw [Argument.Duplicate.Vars.duplicateAt_extend]
      let pendingPresentation := argumentNormalizationPresentation
        recordedSites next stageNext
        (List.append_assoc restArguments before
          (signature :: after)).symm nextEq.symm
      let preparedPresentation := argumentNormalizationPresentation
        recordedSites current stageCurrent
        (congrArg (List.cons signature)
          (List.append_assoc restArguments before
            (signature :: after)).symm) currentEq.symm
      let request : Telescope.Request
          (argumentNormalizedRegion recordedSites current)
          (argumentNormalizedRegion recordedSites next) := {
        boundary := boundary
        source := interface.withBody
          (context.fill (polaritySource polarity
            (argumentNormalizedRegion recordedSites current) endpoint))
          (match polarity with
          | .positive => currentValidity.1
          | .negative => endpointCanonical)
          (match polarity with
          | .positive => currentValidity.2
          | .negative => endpointExternalTwoEnded)
        endpoint := endpoint
        polarity := polarity
        occurrence := exactOccurrence interface context
          (polaritySource polarity
            (argumentNormalizedRegion recordedSites current) endpoint)
          (match polarity with
          | .positive => currentValidity.1
          | .negative => endpointCanonical)
          (match polarity with
          | .positive => currentValidity.2
          | .negative => endpointExternalTwoEnded)
        instantiatedCanonical := currentValidity.1
        instantiatedExternalTwoEnded := currentValidity.2
        pendingCanonical := nextValidity.1
        pendingExternalTwoEnded := nextValidity.2
        endpointCanonical := endpointCanonical
        endpointExternalTwoEnded := endpointExternalTwoEnded
        continuation := tailTelescope
      }
      let prepare : request.Preparation
          (argumentNormalizedRegion recordedSites current) := {
        prepared := argumentNormalizedRegion recordedSites current
        preparedCanonical := currentValidity.1
        preparedExternalTwoEnded := currentValidity.2
        rawPreparedCanonical := currentValidity.1
        rawPreparedExternalTwoEnded := currentValidity.2
        preparedIso := RegionIso.refl _
        telescope := Telescope.refl polarity interface context
          currentValidity.1 currentValidity.2 polarityEq
      }
      have compiled := argumentMoveDuplicateNormalized recordedSites
        stageCurrent stageNext movedEq request pendingPresentation
        (prepare.rawIso preparedPresentation)
      exact Telescope.Compiles.toTelescope polarity interface context
        currentValidity.1 currentValidity.2 endpointCanonical
        endpointExternalTwoEnded polarityEq compiled

/-- Appending one argument preserves occurrence validity by Projection's
extension direction. -/
theorem argumentAppendValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external arguments) (inserted : Var external signature)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (currentCanonical : (context.fill
      (argumentNormalizedRegion recordedSites current)).Canonical)
    (currentExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites current))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (Theory.Vars.extend current
        (Theory.Vars.cons inserted Theory.Vars.nil)))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (Theory.Vars.extend current
            (Theory.Vars.cons inserted Theory.Vars.nil)))) := by
  let next := Theory.Vars.extend current
    (Theory.Vars.cons inserted Theory.Vars.nil)
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation arguments [] signature)
    (Argument.Projection.rootFrame common [] retained arguments [] signature)
    (Argument.Projection.targetHead common [] retained arguments [])
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description common := {
    before := arguments
    after := []
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : argumentNormalizedRegion recordedSites next =
      description.source := by
    dsimp only [argumentNormalizedRegion, description, generated, next]
    apply congrArg (Region.mk (.rel (arguments ++ signature :: []) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (arguments ++ signature :: []))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (arguments ++ signature :: [])) } : Transform.Frame
        (arguments ++ signature :: []) (common ++ retained)
        (common ++ (.rel (arguments ++ signature :: []) :: retained))
        (common ++ (.rel (arguments ++ signature :: []) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation arguments [] signature)
      (Argument.Projection.rootFrame common [] retained arguments [] signature)
      (Argument.Projection.targetHead common [] retained arguments [])
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  let targetPresentation := argumentNormalizationPresentation recordedSites
    current (Argument.Projection.Vars.dropAt arguments next)
    (List.append_nil arguments).symm
    (Argument.Projection.Vars.dropAt_extend_singleton current inserted).symm
  let targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites current) := by
    simpa only [description, generated, next, argumentNormalizedRegion] using
      (argumentProjectionEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) (before := arguments) (after := [])
        recordedSites next).trans targetPresentation.symm
  let filledTargetIso := DiagramContext.fillIso context targetIso
  have targetCanonical : (context.fill description.target).Canonical :=
    filledTargetIso.canonical_iff.mpr currentCanonical
  have targetExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill description.target) := by
    let endpoint := interface.withBody
      (context.fill (argumentNormalizedRegion recordedSites current))
      currentCanonical currentExternalTwoEnded
    apply endpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localTarget := context.holeCanonical description.target targetCanonical
  have extension := description.target_source_extension localTarget
  have filled := context.extendCanonical description.target description.source
    targetCanonical extension.1 extension.2
  have sourceExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (targetExternal wire)
      (Nat.add_le_add_left (filled.2 wire).length_le _)
  rw [sourceEq]
  exact ⟨filled.1, sourceExternal⟩

/-- Append a nonempty tuple by Projection, retaining an arbitrary presented
final endpoint.  The recursive result is used immediately as the
continuation of the head Projection, so no stage certificate escapes. -/
theorem argumentVarsProjectionCompiles
    {recordedArguments external currentArguments restArguments common retained
      boundary recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external currentArguments)
    (head : Var external signature) (tail : Vars external restArguments)
    {pending : Region common}
    (request : Telescope.Request
      (argumentNormalizedRegion recordedSites current) pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend current (Theory.Vars.cons head tail))))
    (baseCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (baseExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)))) :
    request.Result := by
  let first := Theory.Vars.extend current
    (Theory.Vars.cons head Theory.Vars.nil)
  have firstValidity := argumentAppendValidity recordedSites current head
    request.occurrence.interface request.occurrence.context
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
  let prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current) := {
    prepared := argumentNormalizedRegion recordedSites current
    preparedCanonical := request.instantiatedCanonical
    preparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    rawPreparedCanonical := request.instantiatedCanonical
    rawPreparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := Telescope.refl request.polarity request.occurrence.interface
      request.occurrence.context request.instantiatedCanonical
      request.instantiatedExternalTwoEnded request.continuation.1
  }
  cases tail with
  | nil =>
      let singletonPresentation := argumentNormalizationPresentation
        recordedSites (Theory.Vars.extend current
          (Theory.Vars.cons head Theory.Vars.nil))
          (Theory.Vars.extend current
            (Theory.Vars.cons head Theory.Vars.nil)) rfl HEq.rfl
      exact argumentProjectionNormalized recordedSites current head request
        (pendingIso.trans singletonPresentation) prepare
  | @cons nextSignature nextRest nextHead nextTail =>
      let remaining := Theory.Vars.cons nextHead nextTail
      let nestedFinal := Theory.Vars.extend first remaining
      have assocEq : HEq nestedFinal
          (Theory.Vars.extend current
            (Theory.Vars.cons head remaining)) := by
        exact Theory.Vars.extend_assoc current
          (Theory.Vars.cons head Theory.Vars.nil) remaining
      let associationPresentation := argumentNormalizationPresentation
        recordedSites
        (Theory.Vars.extend current (Theory.Vars.cons head remaining))
        nestedFinal (List.append_assoc currentArguments [signature]
          (nextSignature :: nextRest)).symm assocEq.symm
      let stageInterface : OpenDiagram request.boundary :=
        request.occurrence.interface
      let stageContext : DiagramContext stageInterface.external common :=
        request.occurrence.context
      have recursiveSourceCanonical : (stageContext.fill
          (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first)
            request.endpoint)).Canonical := by
        exact match request.polarity with
          | .positive => by simpa only [stageContext] using firstValidity.1
          | .negative => by
              simpa only [stageContext] using request.endpointCanonical
      have recursiveSourceExternal : OpenDiagram.ExternalTwoEnded
          stageInterface.boundaryWire (stageContext.fill
            (polaritySource request.polarity
              (argumentNormalizedRegion recordedSites first)
              request.endpoint)) := by
        exact match request.polarity with
          | .positive => by
              simpa only [stageInterface, stageContext] using firstValidity.2
          | .negative => by
              simpa only [stageInterface, stageContext] using
                request.endpointExternalTwoEnded
      let recursiveRequest : Telescope.Request
          (argumentNormalizedRegion recordedSites first) pending := {
        boundary := request.boundary
        source := stageInterface.withBody
          (stageContext.fill (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first) request.endpoint))
          recursiveSourceCanonical recursiveSourceExternal
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := exactOccurrence stageInterface
          stageContext (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first) request.endpoint)
          recursiveSourceCanonical recursiveSourceExternal
        instantiatedCanonical := firstValidity.1
        instantiatedExternalTwoEnded := firstValidity.2
        pendingCanonical := request.pendingCanonical
        pendingExternalTwoEnded := request.pendingExternalTwoEnded
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := request.continuation
      }
      have recursiveCompiled := argumentVarsProjectionCompiles
        (boundary := request.boundary) recordedSites
        first nextHead nextTail recursiveRequest
        (pendingIso.trans associationPresentation) baseCanonical
        baseExternalTwoEnded
      have recursiveTelescope := Telescope.Compiles.toTelescope
        request.polarity request.occurrence.interface request.occurrence.context
        firstValidity.1 firstValidity.2 request.endpointCanonical
        request.endpointExternalTwoEnded request.continuation.1
        recursiveCompiled
      let firstRequest : Telescope.Request
          (argumentNormalizedRegion recordedSites current)
          (argumentNormalizedRegion recordedSites first) := {
        boundary := request.boundary
        source := request.source
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := request.occurrence
        instantiatedCanonical := request.instantiatedCanonical
        instantiatedExternalTwoEnded := request.instantiatedExternalTwoEnded
        pendingCanonical := firstValidity.1
        pendingExternalTwoEnded := firstValidity.2
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := recursiveTelescope
      }
      let firstPrepare : firstRequest.Preparation
          (argumentNormalizedRegion recordedSites current) := {
        prepared := prepare.prepared
        preparedCanonical := prepare.preparedCanonical
        preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
        rawPreparedCanonical := prepare.rawPreparedCanonical
        rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
        preparedIso := prepare.preparedIso
        telescope := prepare.telescope
      }
      exact argumentProjectionNormalized recordedSites current head firstRequest
        (RegionIso.refl _) firstPrepare


/-- The fixed traversal frame retains the exact source-side instantiation
indices and uses the identity target context only as an inert site annotation
index. -/
def normalizationFrame (outer before after arguments : List Sig) :
    Transform.Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ after)) where
  sourceKeep := _root_.VisualProof.Rule.Comprehension.retain outer before after
    arguments
  targetKeep := WireRenaming.id
  selected := _root_.VisualProof.Rule.Comprehension.selected outer before after
    arguments

mutual
  /-- Unit site annotations exist for every exact authoritative region
  result. The existential stays in `Prop`, so no Instantiation proof is
  eliminated into caller-selectable data. -/
  theorem normalizationRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | mk itemsEvidence =>
        obtain ⟨sites⟩ := normalizationItemsSites_nonempty
          (frame := frame.append _) itemsEvidence
        exact ⟨.mk sites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item-sequence
  result. -/
  theorem normalizationItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := normalizationItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := normalizationItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item result. -/
  theorem normalizationItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨ItemSites.atom (pattern := pattern) (frame := frame) head ports⟩
    | selectedAtom ports =>
        exact ⟨ItemSites.selectedAtom (pattern := pattern) (frame := frame)
          ports PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨sites⟩ := normalizationRegionSites_nonempty childEvidence
        exact ⟨.cut sites⟩
  termination_by sizeOf source
end

/-- A fixed unit-data site traversal selected internally from exact
Instantiation evidence. -/
noncomputable def normalizationSites
    {arguments common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result) :
    ItemsSites (normalizationOperation arguments) PUnit.unit evidence :=
  Classical.choice (normalizationItemsSites_nonempty evidence)

/-! The literal positional atom required by `Leaf.Formal.operation []`.
Its head and every argument occupy distinct boundary positions. -/


end VisualProof.Rule.Completeness.Comprehension
