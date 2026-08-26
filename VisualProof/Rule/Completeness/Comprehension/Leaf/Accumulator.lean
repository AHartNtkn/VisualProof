import VisualProof.Rule.Completeness.Comprehension.Leaf.Targets

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- A caller-owned identification of a target frame's source carrier with its
target carrier.  `DataSelects` expresses the operation-specific connection
between the transported selected wire and the operation data. -/
structure TargetFrameBridge
    {arguments common sourceWires targetWires : List Sig}
    {operation : Transform.Operation arguments}
    (frame : Transform.Frame arguments common sourceWires targetWires)
    (DataSelects : operation.Data frame →
      Var targetWires (.rel arguments) → Prop)
    (data : operation.Data frame) where
  sourceToTarget : WireRenaming sourceWires targetWires
  targetHead : Var targetWires (.rel arguments)
  keep_commutes : ∀ {signature} (wire : Var common signature),
    sourceToTarget (frame.sourceKeep wire) = frame.targetKeep wire
  selected_commutes : sourceToTarget frame.selected = targetHead
  data_selects : DataSelects data targetHead

def TargetFrameBridge.append
    {arguments common sourceWires targetWires : List Sig}
    {operation : Transform.Operation arguments}
    {DataSelects : ∀ {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires},
      operation.Data frame → Var targetWires (.rel arguments) → Prop}
    (dataSelectsAppend : ∀
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame) (head : Var targetWires (.rel arguments)),
      DataSelects data head → ∀ locals,
        DataSelects (operation.appendData frame data locals)
          (head.appendLeft locals))
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : operation.Data frame}
    (bridge : TargetFrameBridge frame
      (@DataSelects common sourceWires targetWires frame) data)
    (locals : List Sig) :
    TargetFrameBridge (frame.append locals)
      (@DataSelects (common ++ locals) (sourceWires ++ locals)
        (targetWires ++ locals) (frame.append locals))
      (operation.appendData frame data locals) where
  sourceToTarget := bridge.sourceToTarget.appendRight locals
  targetHead := bridge.targetHead.appendLeft locals
  keep_commutes := by
    intro signature wire
    apply Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        bridge.sourceToTarget.appendRight locals
            ((frame.append locals).sourceKeep wire) =
          (frame.append locals).targetKeep wire)
    · intro inheritedSignature inherited
      simpa [Transform.Frame.append, WireRenaming.appendRight] using
        congrArg (fun wire => wire.appendLeft locals)
          (bridge.keep_commutes inherited)
    · intro localSignature localWire
      simp [Transform.Frame.append, WireRenaming.appendRight]
  selected_commutes := by
    simpa [Transform.Frame.append, WireRenaming.appendRight] using
      congrArg (fun wire => wire.appendLeft locals) bridge.selected_commutes
  data_selects := dataSelectsAppend data bridge.targetHead bridge.data_selects
    locals

/-- Coherent identification of the authoritative target carrier with the
formal target carrier. -/
structure TargetAmbientBridge
    {arguments targetArguments common originalSourceWires originalTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {operation : Transform.Operation arguments}
    {targetOperation : Transform.Operation targetArguments}
    (originalFrame : Transform.Frame arguments common originalSourceWires
      originalTargetWires)
    (formalFrame : Transform.Frame targetArguments common formalSourceWires
      formalTargetWires)
    (DataAligned : operation.Data originalFrame →
      targetOperation.Data formalFrame →
      WireEquiv originalTargetWires formalTargetWires → Prop)
    (originalData : operation.Data originalFrame)
    (formalData : targetOperation.Data formalFrame) where
  ambient : WireEquiv originalTargetWires formalTargetWires
  keep_commutes : ∀ {signature} (wire : Var common signature),
    ambient.toRenaming (originalFrame.targetKeep wire) =
      formalFrame.targetKeep wire
  data_aligned : DataAligned originalData formalData ambient

def TargetAmbientBridge.append
    {arguments targetArguments common originalSourceWires originalTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {operation : Transform.Operation arguments}
    {targetOperation : Transform.Operation targetArguments}
    {DataAligned : ∀
      {common originalSourceWires originalTargetWires formalSourceWires
        formalTargetWires : List Sig}
      {originalFrame : Transform.Frame arguments common originalSourceWires
        originalTargetWires}
      {formalFrame : Transform.Frame targetArguments common formalSourceWires
        formalTargetWires},
      operation.Data originalFrame → targetOperation.Data formalFrame →
        WireEquiv originalTargetWires formalTargetWires → Prop}
    (dataAlignedAppend : ∀
      {common originalSourceWires originalTargetWires formalSourceWires
        formalTargetWires : List Sig}
      {originalFrame : Transform.Frame arguments common originalSourceWires
        originalTargetWires}
      {formalFrame : Transform.Frame targetArguments common formalSourceWires
        formalTargetWires}
      (originalData : operation.Data originalFrame)
      (formalData : targetOperation.Data formalFrame)
      (ambient : WireEquiv originalTargetWires formalTargetWires),
      DataAligned originalData formalData ambient → ∀ locals,
        DataAligned
          (operation.appendData originalFrame originalData locals)
          (targetOperation.appendData formalFrame formalData locals)
          (ambient.append (WireEquiv.refl locals)))
    {originalFrame : Transform.Frame arguments common originalSourceWires
      originalTargetWires}
    {originalData : operation.Data originalFrame}
    {formalFrame : Transform.Frame targetArguments common formalSourceWires
      formalTargetWires}
    {formalData : targetOperation.Data formalFrame}
    (bridge : TargetAmbientBridge originalFrame formalFrame
      (@DataAligned common originalSourceWires originalTargetWires
        formalSourceWires formalTargetWires originalFrame formalFrame)
      originalData formalData)
    (locals : List Sig) :
    TargetAmbientBridge (originalFrame.append locals)
      (formalFrame.append locals)
      (@DataAligned (common ++ locals) (originalSourceWires ++ locals)
        (originalTargetWires ++ locals) (formalSourceWires ++ locals)
        (formalTargetWires ++ locals) (originalFrame.append locals)
        (formalFrame.append locals))
      (operation.appendData originalFrame originalData locals)
      (targetOperation.appendData formalFrame formalData locals) where
  ambient := bridge.ambient.append (WireEquiv.refl locals)
  keep_commutes := by
    intro signature wire
    refine Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (bridge.ambient.append (WireEquiv.refl locals)).toRenaming
            ((originalFrame.append locals).targetKeep wire) =
          (formalFrame.append locals).targetKeep wire) ?_ ?_ wire
    · intro signature inherited
      simp only [Transform.Frame.append, WireRenaming.appendRight,
        Var.appendMap_left, WireEquiv.append_apply_left]
      change (bridge.ambient.toRenaming
          (originalFrame.targetKeep inherited)).appendLeft locals =
        (formalFrame.targetKeep inherited).appendLeft locals
      rw [bridge.keep_commutes]
    · intro signature localWire
      simp only [Transform.Frame.append, WireRenaming.appendRight,
        Var.appendMap_right, WireEquiv.append_apply_right]
      change Var.appendRight formalTargetWires localWire =
        Var.appendRight formalTargetWires localWire
      rfl
  data_aligned := dataAlignedAppend originalData formalData bridge.ambient
    bridge.data_aligned locals

/-- Accumulate an authoritative instantiation into a caller-selected literal
target edit.  The selected-site premise is nonrecursive; this theorem owns the
only structural recursion over the authoritative sites. -/
theorem accumulateTarget
    {targetArguments targetExternal patternWires outer before after targetInserted
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires
      (outer ++ (before ++ after)) originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted
        targetArguments))
    (KRegion : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : Region sourceWires} {localResult : Region common}
      (localEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : RegionSites operation localData localEvidence)
      (values : Vars targetExternal targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (formalSource : Region formalSourceWires)
      (formalResult : Region common)
      (formalEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          targetPattern formalFrame.sourceKeep formalFrame.selected
          formalSource formalResult)
      (formalSites : RegionSites
        (recordingOperation targetBaseOperation targetExternal)
        formalData formalEvidence),
      formalSource =
        (argumentRegionEdit formalSites values
          (normalizationOperation targetArguments) formalFrame PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (KItems : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : ItemSeq sourceWires} {localResult : Region common}
      (localEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : ItemsSites operation localData localEvidence)
      (values : Vars targetExternal targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (retained : List Sig)
        (formalSource : ItemSeq (formalSourceWires ++ retained))
      (formalResult : Region (common ++ retained))
      (formalEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          targetPattern (formalFrame.append retained).sourceKeep
          (formalFrame.append retained).selected formalSource formalResult)
      (formalSites : ItemsSites
        (recordingOperation targetBaseOperation targetExternal)
        (targetBaseOperation.appendData formalFrame formalData retained)
        formalEvidence),
      formalSource =
        (argumentItemsEdit formalSites values
          (normalizationOperation targetArguments)
          (formalFrame.append retained) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (KItem : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : Item sourceWires} {localResult : Region common}
      (localEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : ItemSites operation localData localEvidence)
      (values : Vars targetExternal targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (retained : List Sig)
        (formalSource : ItemSeq (formalSourceWires ++ retained))
      (formalResult : Region (common ++ retained))
      (formalEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          targetPattern (formalFrame.append retained).sourceKeep
          (formalFrame.append retained).selected formalSource formalResult)
      (formalSites : ItemsSites
        (recordingOperation targetBaseOperation targetExternal)
        (targetBaseOperation.appendData formalFrame formalData retained)
        formalEvidence),
      formalSource =
        (argumentItemsEdit formalSites values
          (normalizationOperation targetArguments)
          (formalFrame.append retained) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (nilCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (localEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected
          (.nil : ItemSeq sourceWires) (Region.blank common))
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItems localEvidence
        (.nil (operation := operation) (data := localData) localEvidence)
        targetValues formalFrame
        formalData
        (KItems localEvidence
          (.nil (operation := operation) (data := localData) localEvidence)
          targetValues formalFrame formalData closeCommon closeTarget))
    (regionCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {locals : List Sig}
      {items : ItemSeq (sourceWires ++ locals)}
      {childResult : Region (common ++ locals)}
      {childEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern (localFrame.sourceKeep.appendRight locals)
          (localFrame.selected.appendLeft locals) items childResult}
      (childSites : ItemsSites operation
        (operation.appendData localFrame localData locals) childEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItems childEvidence childSites targetValues
          (formalFrame.append locals)
          (targetBaseOperation.appendData formalFrame formalData locals)
          (KItems childEvidence childSites targetValues
            (formalFrame.append locals)
            (targetBaseOperation.appendData formalFrame formalData locals)
            (fun region =>
              closeCommon (Region.adjoinAt locals .nil region))
            (fun region =>
              closeTarget (Region.adjoinAt locals .nil region))) →
      TargetRegion
        (VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
          childEvidence)
        (.mk childSites) targetValues formalFrame formalData
        (KRegion
          (VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            childEvidence)
          (.mk childSites) targetValues formalFrame formalData closeCommon
            closeTarget))
    (consCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {item : Item sourceWires} {tail : ItemSeq sourceWires}
      {itemResult tailResult : Region common}
      {itemEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          localPattern localFrame.sourceKeep localFrame.selected item itemResult}
      {tailEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected tail tailResult}
      (itemSites : ItemSites operation localData itemEvidence)
      (tailSites : ItemsSites operation localData tailEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem itemEvidence itemSites targetValues formalFrame formalData
          (KItem itemEvidence itemSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItems tailEvidence tailSites targetValues formalFrame formalData
          (KItems tailEvidence tailSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItems
        (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          itemEvidence tailEvidence)
        (.cons itemSites tailSites) targetValues formalFrame formalData
        (KItems
          (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemEvidence tailEvidence)
          (.cons itemSites tailSites) targetValues formalFrame formalData
            closeCommon closeTarget))
    (atomCase : ∀
      {common sourceWires targetWires atomArguments : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (head : Var common (.rel atomArguments))
      (ports : Vars common atomArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) head ports)
        (@ItemSites.atom patternWires operation evidencePattern common
          sourceWires targetWires atomArguments localPattern localFrame
          localData head ports)
        targetValues formalFrame formalData
        (KItem
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) head ports)
          (@ItemSites.atom patternWires operation evidencePattern common
            sourceWires targetWires atomArguments localPattern localFrame
            localData head ports)
          targetValues formalFrame formalData closeCommon closeTarget))
    (selectedCase : ∀
      {common sourceWires targetWires : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (application : Vars common patternWires)
      (siteData : operation.SiteData localFrame localData application)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) application)
        (@ItemSites.selectedAtom patternWires operation evidencePattern common
          sourceWires targetWires localPattern localFrame localData
          application siteData)
        targetValues formalFrame formalData
        (KItem
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) application)
          (@ItemSites.selectedAtom patternWires operation evidencePattern common
            sourceWires targetWires localPattern localFrame localData
            application siteData)
          targetValues formalFrame formalData closeCommon closeTarget))
    (identityCase : ∀
      {common sourceWires targetWires : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (signature : Sig) (arity : Nat)
      (ports : Fin arity → Var common signature)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) signature arity ports)
        (@ItemSites.identity patternWires operation evidencePattern common
          sourceWires targetWires localPattern localFrame localData signature
          arity ports)
        targetValues formalFrame formalData
        (KItem
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) signature arity ports)
          (@ItemSites.identity patternWires operation evidencePattern common
            sourceWires targetWires localPattern localFrame localData signature
            arity ports)
          targetValues formalFrame formalData closeCommon closeTarget))
    (termCase : ∀
      {common sourceWires targetWires : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (output : Var common .iota) (freeArity : Nat)
      (ports : Fin freeArity → Var common .iota)
      (term : Lambda.Term 0 (Fin freeArity))
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.term
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) output freeArity ports term)
        (@ItemSites.term patternWires operation evidencePattern common
          sourceWires targetWires localPattern localFrame localData output
          freeArity ports term)
        targetValues formalFrame formalData
        (KItem
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.term
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) output freeArity ports term)
          (@ItemSites.term patternWires operation evidencePattern common
            sourceWires targetWires localPattern localFrame localData output
            freeArity ports term)
          targetValues formalFrame formalData closeCommon closeTarget))
    (cutCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {body : Region sourceWires} {childResult : Region common}
      {childEvidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          localPattern localFrame.sourceKeep localFrame.selected body childResult}
      (childSites : RegionSites operation localData childEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetRegion childEvidence childSites targetValues formalFrame formalData
          (KRegion childEvidence childSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItem
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
          childEvidence)
        (.cut childSites) targetValues formalFrame formalData
        (KItem
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childEvidence)
          (.cut childSites) targetValues formalFrame formalData closeCommon
            closeTarget)) :
    TargetItems evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted targetArguments)
      targetData
      (KItems evidence sites targetValues
        (Transform.Frame.replace outer before after targetInserted targetArguments)
        targetData
        (fun region => Region.adjoinAt (before ++ after) .nil region)
        (fun region =>
          Region.adjoinAt (before ++ (targetInserted ++ after)) .nil
            region)) := by
  apply ItemsSites.rec
    (motive_1 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetRegion evidence sites targetValues formalFrame formalData
          (KRegion evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
    (motive_2 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetItems evidence sites targetValues formalFrame formalData
          (KItems evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
    (motive_3 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetItem evidence sites targetValues formalFrame formalData
          (KItem evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
  case nil =>
    intros
    apply nilCase
  case mk =>
    intros
    rename_i _ _ _ _ _ _ locals _ _ _ childSites childIH _ _
      formalFrame formalData closeCommon closeTarget
    exact regionCase childSites formalFrame formalData closeCommon
      closeTarget
      (childIH (formalFrame.append locals)
        (targetBaseOperation.appendData formalFrame formalData locals)
        (fun region => closeCommon (Region.adjoinAt locals .nil region))
        (fun region => closeTarget (Region.adjoinAt locals .nil region)))
  case cons =>
    intros
    solve_by_elim [consCase]
  case atom =>
    intros
    apply atomCase
  case selectedAtom =>
    intros
    apply selectedCase
  case identity =>
    intros
    apply identityCase
  case term =>
    intros
    apply termCase
  case cut =>
    intros
    rename_i _ _ _ _ _ _ _ _ _ childSites childIH _ _ formalFrame
      formalData closeCommon closeTarget
    exact cutCase childSites formalFrame formalData closeCommon
      closeTarget (childIH formalFrame formalData closeCommon closeTarget)

/-- Accumulate a hosted target transformation together with an abstract
structural side condition.  The side condition is threaded through the same
authoritative target traversal, so specializations never need to reconstruct
or repeat the target witnesses. -/
theorem accumulateHostedTargetWith
    {targetArguments targetExternal patternWires outer before after targetInserted originalSourceWires
      originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires (outer ++ (before ++ after))
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted targetArguments))
    (sourceValues : Vars targetExternal patternWires)
    (Side : {wires : List Sig} → Region wires → Region wires → Prop)
    (sideRefl : ∀ {wires : List Sig} (region : Region wires),
      Side region region)
    (sideAdjoinAt : ∀ {common : List Sig} (locals : List Sig)
      (before after : Region (common ++ locals)),
      Side before after →
        Side (Region.adjoinAt locals .nil before)
          (Region.adjoinAt locals .nil after))
    (sideConjoin : ∀ {wires : List Sig}
      {firstBefore firstAfter secondBefore secondAfter : Region wires},
      Side firstBefore firstAfter → Side secondBefore secondAfter →
        Side (firstBefore.conjoin secondBefore)
          (firstAfter.conjoin secondAfter))
    (sideCut : ∀ {wires : List Sig} {before after : Region wires},
      Side before after →
        Side (Region.singleton (.cut before))
          (Region.singleton (.cut after)))
    (SourceSide : {wires : List Sig} → Region wires → Region wires → Prop)
    (sourceSideRefl : ∀ {wires : List Sig} (region : Region wires),
      SourceSide region region)
    (sourceSideAdjoinAt : ∀ {common : List Sig} (locals : List Sig)
      (before after : Region (common ++ locals)),
      SourceSide before after →
        SourceSide (Region.adjoinAt locals .nil before)
          (Region.adjoinAt locals .nil after))
    (sourceSideConjoin : ∀ {wires : List Sig}
      {firstBefore firstAfter secondBefore secondAfter : Region wires},
      SourceSide firstBefore firstAfter →
        SourceSide secondBefore secondAfter →
          SourceSide (firstBefore.conjoin secondBefore)
            (firstAfter.conjoin secondAfter))
    (sourceSideCut : ∀ {wires : List Sig} {before after : Region wires},
      SourceSide before after →
        SourceSide (Region.singleton (.cut before))
          (Region.singleton (.cut after)))
    (sourceSideIso : ∀ {wires : List Sig}
      {before before' after after' : Region wires},
      RegionIso (WireEquiv.refl wires) before' before →
        RegionIso (WireEquiv.refl wires) after after' →
          SourceSide before after → SourceSide before' after')
    (DataSelects : ∀ {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame targetArguments common sourceWires targetWires},
      targetBaseOperation.Data frame →
        Var targetWires (.rel targetArguments) → Prop)
    (dataSelectsAppend : ∀
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      (data : targetBaseOperation.Data frame)
      (head : Var targetWires (.rel targetArguments)),
      DataSelects data head → ∀ locals,
        DataSelects (targetBaseOperation.appendData frame data locals)
          (head.appendLeft locals))
    (DataAligned : ∀
      {common localSourceWires localTargetWires formalSourceWires
        formalTargetWires : List Sig}
      {localFrame : Transform.Frame patternWires common localSourceWires
        localTargetWires}
      {formalFrame : Transform.Frame targetArguments common formalSourceWires
        formalTargetWires},
      operation.Data localFrame → targetBaseOperation.Data formalFrame →
        WireEquiv localTargetWires formalTargetWires → Prop)
    (dataAlignedAppend : ∀
      {common localSourceWires localTargetWires formalSourceWires
        formalTargetWires : List Sig}
      {localFrame : Transform.Frame patternWires common localSourceWires
        localTargetWires}
      {formalFrame : Transform.Frame targetArguments common formalSourceWires
        formalTargetWires}
      (localData : operation.Data localFrame)
      (formalData : targetBaseOperation.Data formalFrame)
      (ambient : WireEquiv localTargetWires formalTargetWires),
      DataAligned localData formalData ambient → ∀ locals,
        DataAligned (operation.appendData localFrame localData locals)
          (targetBaseOperation.appendData formalFrame formalData locals)
          (ambient.append (WireEquiv.refl locals)))
    (targetNaturality : DataNaturality targetBaseOperation)
    (Retained : List Sig → Prop)
    (retainedNil : Retained [])
    (retainedAppend : ∀ first second,
      Retained first → Retained second → Retained (first ++ second))
    (selectedCase : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemData : operation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : operation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := operation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained formalSource formalResult _formalEvidence formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Side
                  (VisualProof.Rule.Comprehension.Instantiation.instantiate
                    pattern application) staged ∧
                Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                  (Region.adjoinAt retained .nil formalResult)) ∧
                  (∀ (bridge : TargetFrameBridge selectedTargetFrame
                        (@DataSelects itemCommon selectedTargetSourceWires
                          selectedTargetWires selectedTargetFrame)
                        selectedTargetData)
                    (alignment : TargetAmbientBridge itemFrame
                      selectedTargetFrame
                      (@DataAligned itemCommon itemSourceWires itemTargetWires
                        selectedTargetSourceWires selectedTargetWires itemFrame
                        selectedTargetFrame)
                      itemData selectedTargetData),
                    Nonempty (RegionIso
                      (WireEquiv.refl selectedTargetWires)
                      ((itemEdit itemData
                        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                          (pattern := pattern) (retain := itemFrame.sourceKeep)
                          (selected := itemFrame.selected) application)
                        (ItemSites.selectedAtom (operation := operation)
                          (pattern := pattern) (frame := itemFrame)
                          application siteData)).endpoint.renameWires
                          alignment.ambient.toRenaming)
                      (.mk retained (formalSource.renameWires
                        (bridge.sourceToTarget.appendRight retained))))) ∧
                  SourceSide
                    (Region.singleton (.atom itemFrame.selected
                      (application.map fun wire => itemFrame.sourceKeep wire)))
                    (Region.adjoinAt retained .nil
                      (Region.ofItems
                        (argumentItemsEdit formalSites
                          sourceValues
                          (normalizationOperation patternWires)
                          (({ sourceKeep := itemFrame.sourceKeep
                              targetKeep := itemFrame.sourceKeep
                              selected := itemFrame.selected } :
                            Transform.Frame patternWires itemCommon
                              itemSourceWires itemSourceWires).append retained)
                          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) ∧
                  Retained retained)) :
    TargetItems
      (targetPattern := targetPattern)
      (targetOperation := targetBaseOperation)
      evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted targetArguments) targetData
      (fun retained formalSource formalResult _formalEvidence formalSites
          _coherence =>
        ∃ staged : Region (outer ++ (before ++ after)),
          HostedStrict result staged ∧
            Side result staged ∧
              Nonempty (RegionIso (WireEquiv.refl (outer ++ (before ++ after))) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
                (∀ (bridge : TargetFrameBridge
                      (Transform.Frame.replace outer before after targetInserted
                        targetArguments)
                      (fun data head => DataSelects data head) targetData)
                  (alignment : TargetAmbientBridge originalFrame
                    (Transform.Frame.replace outer before after targetInserted
                      targetArguments)
                    (@DataAligned (outer ++ (before ++ after))
                      originalSourceWires originalTargetWires
                      (outer ++ (before ++ .rel targetArguments :: after))
                      (outer ++ (before ++ (targetInserted ++ after)))
                      originalFrame
                      (Transform.Frame.replace outer before after
                        targetInserted targetArguments))
                    data targetData),
                  Nonempty (RegionIso
                    (WireEquiv.refl
                      (outer ++ (before ++ (targetInserted ++ after))))
                    ((itemsEdit data evidence sites).endpoint.renameWires
                      alignment.ambient.toRenaming)
                    (.mk retained (formalSource.renameWires
                      (bridge.sourceToTarget.appendRight retained))))) ∧
                SourceSide (Region.ofItems source)
                  (Region.adjoinAt retained .nil
                    (Region.ofItems
                      (argumentItemsEdit formalSites
                        sourceValues
                        (normalizationOperation patternWires)
                        (({ sourceKeep := originalFrame.sourceKeep
                            targetKeep := originalFrame.sourceKeep
                            selected := originalFrame.selected } :
                          Transform.Frame patternWires
                            (outer ++ (before ++ after))
                            originalSourceWires originalSourceWires).append
                          retained)
                        PUnit.unit (fun _ _ _ => PUnit.unit)).1)) ∧
                Retained retained) := by
  let common := outer ++ (before ++ after)
  let targetOperation := recordingOperation targetBaseOperation targetExternal
  let authoritativePattern := pattern
  let targetFrame := Transform.Frame.replace outer before after targetInserted targetArguments
  have foldedFamilyWithPattern :
      TargetItems
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        evidence sites targetValues targetFrame targetData
        (fun retained formalSource formalResult _formalEvidence formalSites
            _coherence =>
          pattern = authoritativePattern →
          ∃ staged : Region common,
            HostedStrict result staged ∧
              Side result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult)) ∧
                  (∀ (bridge : TargetFrameBridge targetFrame
                        (fun data head => DataSelects data head) targetData)
                    (alignment : TargetAmbientBridge originalFrame targetFrame
                      (@DataAligned (outer ++ (before ++ after))
                        originalSourceWires originalTargetWires
                        (outer ++ (before ++ .rel targetArguments :: after))
                        (outer ++ (before ++ (targetInserted ++ after)))
                        originalFrame targetFrame)
                      data targetData),
                    Nonempty (RegionIso
                      (WireEquiv.refl
                        (outer ++ (before ++ (targetInserted ++ after))))
                      ((itemsEdit data evidence sites).endpoint.renameWires
                        alignment.ambient.toRenaming)
                      (.mk retained (formalSource.renameWires
                        (bridge.sourceToTarget.appendRight retained))))) ∧
                  SourceSide (Region.ofItems source)
                    (Region.adjoinAt retained .nil
                      (Region.ofItems
                        (argumentItemsEdit formalSites
                          sourceValues
                          (normalizationOperation patternWires)
                          (({ sourceKeep := originalFrame.sourceKeep
                              targetKeep := originalFrame.sourceKeep
                              selected := originalFrame.selected } :
                            Transform.Frame patternWires
                              (outer ++ (before ++ after))
                              originalSourceWires originalSourceWires).append
                            retained)
                          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) ∧
                  Retained retained) := by
    refine accumulateTarget evidence sites targetValues targetData
      (KRegion := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget formalSource formalResult
          formalEvidence
        formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  formalResult) ∧
              (∀ (bridge : TargetFrameBridge formalFrame
                    (@DataSelects common formalSourceWires formalTargetWires
                      formalFrame) formalData)
                (alignment : TargetAmbientBridge localFrame formalFrame
                  (@DataAligned common sourceWires targetWires
                    formalSourceWires formalTargetWires localFrame formalFrame)
                  localData formalData),
                Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                  ((regionEdit localData _localEvidence
                    _localSites).endpoint.renameWires
                      alignment.ambient.toRenaming)
                  (formalSource.renameWires bridge.sourceToTarget))) ∧
              SourceSide localSource
                (argumentRegionEdit formalSites
                  sourceValues
                  (normalizationOperation patternWires)
                  ({ sourceKeep := localFrame.sourceKeep
                     targetKeep := localFrame.sourceKeep
                     selected := localFrame.selected } :
                    Transform.Frame patternWires common sourceWires
                      sourceWires)
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1)
      (KItems := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget retained formalSource formalResult
        formalEvidence formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult)) ∧
              (∀ (bridge : TargetFrameBridge formalFrame
                    (@DataSelects common formalSourceWires formalTargetWires
                      formalFrame) formalData)
                (alignment : TargetAmbientBridge localFrame formalFrame
                  (@DataAligned common sourceWires targetWires
                    formalSourceWires formalTargetWires localFrame formalFrame)
                  localData formalData),
                Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                  ((itemsEdit localData _localEvidence
                    _localSites).endpoint.renameWires
                      alignment.ambient.toRenaming)
                  (.mk retained (formalSource.renameWires
                    (bridge.sourceToTarget.appendRight retained))))) ∧
              SourceSide (Region.ofItems localSource)
                (Region.adjoinAt retained .nil
                  (Region.ofItems
                    (argumentItemsEdit formalSites
                      sourceValues
                      (normalizationOperation patternWires)
                      (({ sourceKeep := localFrame.sourceKeep
                          targetKeep := localFrame.sourceKeep
                          selected := localFrame.selected } :
                        Transform.Frame patternWires common sourceWires
                          sourceWires).append retained)
                      PUnit.unit (fun _ _ _ => PUnit.unit)).1)) ∧
              Retained retained)
      (KItem := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget retained formalSource formalResult
        formalEvidence formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult)) ∧
              (∀ (bridge : TargetFrameBridge formalFrame
                    (@DataSelects common formalSourceWires formalTargetWires
                      formalFrame) formalData)
                (alignment : TargetAmbientBridge localFrame formalFrame
                  (@DataAligned common sourceWires targetWires
                    formalSourceWires formalTargetWires localFrame formalFrame)
                  localData formalData),
                Nonempty (RegionIso (WireEquiv.refl formalTargetWires)
                  ((itemEdit localData _localEvidence
                    _localSites).endpoint.renameWires
                      alignment.ambient.toRenaming)
                  (.mk retained (formalSource.renameWires
                    (bridge.sourceToTarget.appendRight retained))))) ∧
              SourceSide (Region.singleton localSource)
                (Region.adjoinAt retained .nil
                  (Region.ofItems
                    (argumentItemsEdit formalSites
                      sourceValues
                      (normalizationOperation patternWires)
                      (({ sourceKeep := localFrame.sourceKeep
                          targetKeep := localFrame.sourceKeep
                          selected := localFrame.selected } :
                        Transform.Frame patternWires common sourceWires
                          sourceWires).append retained)
                      PUnit.unit (fun _ _ _ => PUnit.unit)).1)) ∧
              Retained retained)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case refine_1 =>
        intros
        rename_i nilCommon nilSourceWires nilTargetWires nilPattern nilFrame
          nilData nilEvidence formalSourceWires formalTargetWires
          formalFrame formalData _closeCommon _closeTarget
        unfold TargetItems
        let appendedData := targetOperation.appendData formalFrame formalData []
        let formalEvidence :
            VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (formalFrame.append []).sourceKeep
              (formalFrame.append []).selected
              (.nil : ItemSeq (formalSourceWires ++ []))
              (Region.blank (nilCommon ++ [])) := .nil
        let formalSites : ItemsSites
            targetOperation appendedData
            formalEvidence := .nil formalEvidence
        have hosted : HostedStrict (Region.blank nilCommon)
            (Region.blank nilCommon) := by
          intro outer hostLocals rename hostItems boundary source occurrence
            targetCanonical targetExternalTwoEnded
          simpa only [EqualityNormalization.StrictEquates] using
            EqualityNormalization.StrictEquates.refl occurrence
        have presentationEq : Region.adjoinAt [] .nil
            (Region.blank (nilCommon ++ [])) =
            Region.blank nilCommon := by
          rfl
        refine ⟨[], .nil, Region.blank (nilCommon ++ []), formalEvidence,
          formalSites, rfl, ?_⟩
        intro patternEq
        cases patternEq
        exact ⟨Region.blank nilCommon, hosted,
          sideRefl (Region.blank nilCommon),
          ⟨RegionIso.ofEq presentationEq.symm⟩, by
            intro bridge alignment
            refine ⟨?_⟩
            change RegionIso (WireEquiv.refl formalTargetWires)
              (Region.blank formalTargetWires) (Region.blank formalTargetWires)
            exact RegionIso.refl _, by
              simpa [argumentItemsEdit] using
                sourceSideRefl (Region.blank nilSourceWires), retainedNil⟩
    case refine_2 =>
      intros
      rename_i regionCommon regionSourceWires regionTargetWires regionPattern
        regionFrame regionData regionLocals regionItems regionResult
        regionEvidence regionSites formalSourceWires formalTargetWires
        formalFrame formalData _closeCommon _closeTarget regionIH
      let values := targetValues
      unfold TargetRegion
      let childData := targetOperation.appendData formalFrame formalData
        regionLocals
      obtain ⟨retained, childFormalSource, childFormalResult,
          childFormalEvidence, childFormalSites, childCoherence,
          childSemantic⟩ :=
        regionIH
      let combinedRetained := regionLocals ++ retained
      let commonRename := Region.adjoinMaterialWire regionCommon
        regionLocals retained
      let sourceRename := Region.adjoinMaterialWire formalSourceWires
        regionLocals retained
      let targetSourceRename := Region.adjoinMaterialWire formalTargetWires
        regionLocals retained
      let argumentSourceRename := Region.adjoinMaterialWire regionSourceWires
        regionLocals retained
      let combinedFrame := formalFrame.append combinedRetained
      let combinedData := targetOperation.appendData formalFrame formalData
        combinedRetained
      have keepCommutes : ∀ {signature}
          (wire : Var ((regionCommon ++ regionLocals) ++ retained)
            signature),
          sourceRename
              (((formalFrame.append regionLocals).append retained).sourceKeep
                wire) =
            combinedFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := regionCommon ++ regionLocals)
          (right := retained)
          (motive := fun wire => sourceRename
              (((formalFrame.append regionLocals).append retained).sourceKeep
                wire) =
            combinedFrame.sourceKeep (commonRename wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := regionCommon) (right := regionLocals)
            (motive := fun inherited => sourceRename
                (((formalFrame.append regionLocals).append retained).sourceKeep
                  (inherited.appendLeft retained)) =
              combinedFrame.sourceKeep
                (commonRename (inherited.appendLeft retained)))
          · intro commonSignature commonWire
            simp [sourceRename, commonRename, combinedFrame,
              combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
          · intro localSignature localWire
            simp [sourceRename, commonRename, combinedFrame,
              combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
        · intro retainedSignature retainedWire
          simp [sourceRename, commonRename, combinedFrame,
            combinedRetained, Transform.Frame.append,
            WireRenaming.appendRight, Region.adjoinMaterialWire]
      have selectedCommutes :
          sourceRename
              (((formalFrame.append regionLocals).append retained).selected) =
            combinedFrame.selected := by
        simp [sourceRename, combinedFrame, combinedRetained,
          Transform.Frame.append, Region.adjoinMaterialWire]
      let argumentFrame : Transform.Frame patternWires
          (regionCommon ++ regionLocals)
          (regionSourceWires ++ regionLocals)
          (regionSourceWires ++ regionLocals) := {
        sourceKeep := (regionFrame.append regionLocals).sourceKeep
        targetKeep := (regionFrame.append regionLocals).sourceKeep
        selected := (regionFrame.append regionLocals).selected
      }
      let mappedArgumentFrame : Transform.Frame patternWires
          (regionCommon ++ combinedRetained)
          (regionSourceWires ++ combinedRetained)
          (regionSourceWires ++ combinedRetained) := {
        sourceKeep := (regionFrame.append combinedRetained).sourceKeep
        targetKeep := (regionFrame.append combinedRetained).sourceKeep
        selected := (regionFrame.append combinedRetained).selected
      }
      have argumentKeepCommutes : ∀ {signature}
          (wire : Var ((regionCommon ++ regionLocals) ++ retained) signature),
          argumentSourceRename
              ((argumentFrame.append retained).sourceKeep wire) =
            mappedArgumentFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := regionCommon ++ regionLocals)
          (right := retained) (motive := fun wire =>
            argumentSourceRename
                ((argumentFrame.append retained).sourceKeep wire) =
              mappedArgumentFrame.sourceKeep (commonRename wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := regionCommon) (right := regionLocals)
            (motive := fun inherited =>
              argumentSourceRename
                  ((argumentFrame.append retained).sourceKeep
                    (inherited.appendLeft retained)) =
                mappedArgumentFrame.sourceKeep
                  (commonRename (inherited.appendLeft retained)))
          · intro
            simp [argumentSourceRename, argumentFrame, mappedArgumentFrame,
              commonRename, combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
          · intro
            simp [argumentSourceRename, argumentFrame, mappedArgumentFrame,
              commonRename, combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
        · intro
          simp [argumentSourceRename, argumentFrame, mappedArgumentFrame,
            commonRename, combinedRetained, Transform.Frame.append,
            WireRenaming.appendRight, Region.adjoinMaterialWire]
      have argumentSelectedCommutes :
          argumentSourceRename (argumentFrame.append retained).selected =
            mappedArgumentFrame.selected := by
        simp [argumentSourceRename, argumentFrame, mappedArgumentFrame,
          combinedRetained, Transform.Frame.append,
          Region.adjoinMaterialWire]
      have targetKeepCommutes : ∀ {signature}
          (wire : Var ((regionCommon ++ regionLocals) ++ retained)
            signature),
          targetSourceRename
              (((formalFrame.append regionLocals).append retained).targetKeep
                wire) =
            combinedFrame.targetKeep (commonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := regionCommon ++ regionLocals)
          (right := retained)
          (motive := fun wire => targetSourceRename
              (((formalFrame.append regionLocals).append retained).targetKeep
                wire) =
            combinedFrame.targetKeep (commonRename wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := regionCommon) (right := regionLocals)
            (motive := fun inherited => targetSourceRename
                (((formalFrame.append regionLocals).append retained).targetKeep
                  (inherited.appendLeft retained)) =
              combinedFrame.targetKeep
                (commonRename (inherited.appendLeft retained)))
          · intro commonSignature commonWire
            simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
          · intro localSignature localWire
            simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
        · intro retainedSignature retainedWire
          simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.adjoinMaterialWire]
      obtain ⟨mappedSource, mappedResult, mappedEvidence, mappedSites,
          mappedSourceEq, mappedArgumentEq,
          mappedSourceArgumentEq,
          ⟨mappedResultIso⟩, ⟨mappedEndpointIso⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := targetExternal)
          childFormalEvidence childFormalSites values sourceValues
          (argumentFrame.append retained) mappedArgumentFrame
          commonRename sourceRename targetSourceRename argumentSourceRename
          keepCommutes targetKeepCommutes selectedCommutes
          argumentKeepCommutes argumentSelectedCommutes targetNaturality
          (targetNaturality.appendAssoc formalFrame formalData regionLocals
            retained)
      let formalSource : Region formalSourceWires :=
        .mk combinedRetained mappedSource
      let formalResult : Region regionCommon :=
        Region.adjoinAt combinedRetained .nil mappedResult
      let formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern formalFrame.sourceKeep
            formalFrame.selected formalSource formalResult := by
        apply VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
        exact mappedEvidence
      let formalSites : RegionSites
          targetOperation formalData
          formalEvidence := by
        apply RegionSites.mk
        exact mappedSites
      have childCoherence' : childFormalSource =
          (argumentItemsEdit childFormalSites values
            (normalizationOperation targetArguments)
            ((formalFrame.append regionLocals).append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        simpa using childCoherence
      have mappedCoherence : mappedSource =
          (argumentItemsEdit mappedSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedSource = childFormalSource.renameWires sourceRename :=
            mappedSourceEq.symm
          _ = (argumentItemsEdit childFormalSites values
                (normalizationOperation targetArguments)
                ((formalFrame.append regionLocals).append retained)
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.renameWires
                sourceRename := congrArg
                  (fun items => items.renameWires sourceRename) childCoherence'
          _ = _ := mappedArgumentEq
      refine ⟨formalSource, formalResult, formalEvidence, formalSites,
        ?_, ?_⟩
      · unfold formalSource formalSites argumentRegionEdit
        exact congrArg (Region.mk combinedRetained) mappedCoherence
      intro patternEq
      cases patternEq
      obtain ⟨childStaged, childHosted, childScope,
          ⟨childPresentation⟩, childEndpoint, childSourceSide,
          _childRetained⟩ :=
        childSemantic rfl
      let staged := Region.adjoinAt regionLocals .nil childStaged
      have stagedSide : Side
          (Region.adjoinAt regionLocals .nil regionResult) staged := by
        simpa only [staged] using
          sideAdjoinAt regionLocals regionResult childStaged childScope
      have liftHosted : ∀ (childBefore childAfter :
          Region (regionCommon ++ regionLocals)),
          HostedStrict childBefore childAfter →
            HostedStrict
              (Region.adjoinAt regionLocals .nil childBefore)
              (Region.adjoinAt regionLocals .nil childAfter) := by
        intro childBefore childAfter childTransformation
        intro outer hostLocals rename hostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let childRename := rename.appendRight regionLocals
        let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
          regionLocals
        let nextRename := WireRenaming.comp assoc.toRenaming childRename
        let nextHostItems := Region.extendHostItems hostLocals hostItems
          (.mk regionLocals .nil)
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.adjoinAt regionLocals .nil childBefore).renameWires rename)
        let sourceAfter := Region.adjoinAt (hostLocals ++ regionLocals)
          nextHostItems (childBefore.renameWires nextRename)
        change Occurrence sourceBefore source at hostedOccurrence
        let sourceNested := RegionIso.adjoinAt hostLocals hostItems
          (RegionIso.renameWiresAdjoinAtNil childBefore rename)
        let sourceAssociated :=
          (RegionIso.adjoinAtAssoc hostLocals hostItems regionLocals .nil
            (childBefore.renameWires childRename)).symm
        let sourceCombined := RegionIso.adjoinAt
          (hostLocals ++ regionLocals) nextHostItems
          (RegionIso.renameWiresComp childBefore childRename
            assoc.toRenaming)
        let sourcePresentation : RegionIso (WireEquiv.refl outer)
            sourceBefore sourceAfter :=
          (sourceNested.trans sourceAssociated).trans sourceCombined
        have sourceAfterCanonical : sourceAfter.Canonical :=
          sourcePresentation.canonical_iff.mp
            (hostedOccurrence.context.holeCanonical _
              hostedOccurrence.sourceCanonical)
        have sourceSameNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := sourcePresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        let presentedOccurrence : Occurrence sourceAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceSameNonempty sourcePresentation
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((Region.adjoinAt regionLocals .nil childAfter).renameWires rename)
        let targetAfter := Region.adjoinAt (hostLocals ++ regionLocals)
          nextHostItems (childAfter.renameWires nextRename)
        let targetNested := RegionIso.adjoinAt hostLocals hostItems
          (RegionIso.renameWiresAdjoinAtNil childAfter rename)
        let targetAssociated :=
          (RegionIso.adjoinAtAssoc hostLocals hostItems regionLocals .nil
            (childAfter.renameWires childRename)).symm
        let targetCombined := RegionIso.adjoinAt
          (hostLocals ++ regionLocals) nextHostItems
          (RegionIso.renameWiresComp childAfter childRename
            assoc.toRenaming)
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetBefore targetAfter :=
          (targetNested.trans targetAssociated).trans targetCombined
        have targetAfterLocalCanonical : targetAfter.Canonical :=
          targetPresentation.canonical_iff.mp
            (hostedOccurrence.context.holeCanonical _ targetCanonical)
        have targetSameNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := targetPresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        have targetReplacement := hostedOccurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterLocalCanonical
          targetSameNonempty
        let targetBeforeEndpoint := hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            hostedOccurrence.interface.boundaryWire
            (hostedOccurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childStrict := childTransformation outer
          (hostLocals ++ regionLocals) nextRename nextHostItems
          presentedOccurrence presentedTargetCanonical
          presentedTargetExternalTwoEnded
        let finalBodyIso := DiagramContext.fillIso
          presentedOccurrence.context targetPresentation.symm
        let finalIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded finalBodyIso
        exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
            finalIso,
          transGen_iso finalIso childStrict.2 (OpenDiagramIso.refl source)⟩
      have hosted : HostedStrict
          (Region.adjoinAt regionLocals .nil regionResult) staged := by
        simpa only [staged] using
          liftHosted regionResult childStaged childHosted
      have presentation : RegionIso (WireEquiv.refl regionCommon)
          staged formalResult := by
        let lifted := RegionIso.adjoinAt regionLocals .nil childPresentation
        let flattened :=
          (RegionIso.adjoinAtAssoc regionLocals .nil retained .nil
            childFormalResult).symm
        let mappedUnderHost := RegionIso.adjoinAt combinedRetained .nil
          mappedResultIso
        let chained := (lifted.trans flattened).trans mappedUnderHost
        have ambientEq :
            ((WireEquiv.refl regionCommon).trans
              (WireEquiv.refl regionCommon).symm).trans
                (WireEquiv.refl regionCommon) =
              WireEquiv.refl regionCommon := by
          apply WireEquiv.ext
          intro signature wire
          rfl
        simpa only [staged, formalResult, combinedRetained,
          List.append_assoc, commonRename, Region.extendHostItems,
          ItemSeq.renameWires, ItemSeq.append_nil, ItemSeq.nil_append] using
            chained.castAmbient ambientEq
      exact ⟨staged, hosted, stagedSide, ⟨presentation⟩, by
        intro bridge alignment
        obtain ⟨childEndpointIso⟩ := childEndpoint
          (bridge.append dataSelectsAppend regionLocals)
          (alignment.append dataAlignedAppend regionLocals)
        let childRaw := (itemsEdit
          (operation.appendData regionFrame regionData regionLocals)
          regionEvidence regionSites).endpoint
        let sourcePresented := RegionIso.renameWiresAdjoinAtNil childRaw
          alignment.ambient.toRenaming
        let lifted := RegionIso.adjoinAt regionLocals .nil childEndpointIso
        have targetEq :
            Region.adjoinAt regionLocals .nil
                (.mk retained (childFormalSource.renameWires
                  ((bridge.append dataSelectsAppend regionLocals).sourceToTarget.appendRight
                    retained))) =
              formalSource.renameWires bridge.sourceToTarget := by
          unfold formalSource
          rw [← mappedSourceEq]
          unfold Region.adjoinAt Region.renameWires
          simp only [ItemSeq.nil_append, ItemSeq.renameWires_comp]
          congr 1
          apply congrArg (fun rename =>
            childFormalSource.renameWires rename)
          apply WireRenaming.ext
          intro signature wire
          apply Var.appendCases
            (left := formalSourceWires ++ regionLocals) (right := retained)
            (motive := fun wire =>
              (Region.adjoinMaterialWire formalTargetWires regionLocals retained)
                    (((bridge.sourceToTarget.appendRight regionLocals).appendRight
                      retained) wire) =
                (bridge.sourceToTarget.appendRight combinedRetained)
                  (sourceRename wire))
          · intro inheritedSignature inherited
            apply Var.appendCases (left := formalSourceWires)
              (right := regionLocals)
              (motive := fun inherited =>
                (Region.adjoinMaterialWire formalTargetWires regionLocals retained)
                      (((bridge.sourceToTarget.appendRight regionLocals).appendRight
                        retained) (inherited.appendLeft retained)) =
                  (bridge.sourceToTarget.appendRight combinedRetained)
                    (sourceRename (inherited.appendLeft retained)))
            · intro; simp [combinedRetained, sourceRename,
                Region.adjoinMaterialWire, WireRenaming.appendRight]
            · intro; simp [combinedRetained, sourceRename,
                Region.adjoinMaterialWire, WireRenaming.appendRight]
          · intro; simp [combinedRetained, sourceRename,
              Region.adjoinMaterialWire, WireRenaming.appendRight]
        exact ⟨(sourcePresented.trans lifted).trans
          (RegionIso.ofEq targetEq)⟩, by
        let childArgumentSource := Region.ofItems
          (argumentItemsEdit childFormalSites
            sourceValues
            (normalizationOperation patternWires)
            (({ sourceKeep := (regionFrame.append regionLocals).sourceKeep
                targetKeep := (regionFrame.append regionLocals).sourceKeep
                selected := (regionFrame.append regionLocals).selected } :
              Transform.Frame patternWires
                (regionCommon ++ regionLocals)
                (regionSourceWires ++ regionLocals)
                (regionSourceWires ++ regionLocals)).append retained)
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        have nested := sourceSideAdjoinAt regionLocals
          (Region.ofItems regionItems)
          (Region.adjoinAt retained .nil childArgumentSource) childSourceSide
        let flattened :=
          (RegionIso.adjoinAtAssoc regionLocals .nil retained .nil
            childArgumentSource).symm
        let mappedArgumentSource := Region.ofItems
          (argumentItemsEdit mappedSites sourceValues
            (normalizationOperation patternWires) mappedArgumentFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        have mappedArgumentRegionEq :
            childArgumentSource.renameWires argumentSourceRename =
              mappedArgumentSource := by
          unfold childArgumentSource mappedArgumentSource
          rw [Region.ofItems_renameWires]
          exact congrArg Region.ofItems mappedSourceArgumentEq
        let mappedPresentation := RegionIso.adjoinAt combinedRetained .nil
          (RegionIso.ofEq mappedArgumentRegionEq)
        let closePresentation := RegionIso.adjoinAtOfItems combinedRetained
          (argumentItemsEdit mappedSites sourceValues
            (normalizationOperation patternWires) mappedArgumentFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        let sourcePresentationRaw :=
          (flattened.trans mappedPresentation).trans closePresentation
        have sourceAmbientEq :
            (WireEquiv.refl regionSourceWires).symm.trans
                (WireEquiv.refl regionSourceWires) =
              WireEquiv.refl regionSourceWires := by
          apply WireEquiv.ext
          intro signature wire
          rfl
        let sourcePresentation :=
          sourcePresentationRaw.castAmbient sourceAmbientEq
        have moved := sourceSideIso
          (RegionIso.adjoinAtOfItems regionLocals regionItems).symm
          sourcePresentation nested
        simpa only [formalSites, argumentRegionEdit, combinedRetained,
          formalResult, formalSource, formalEvidence,
          List.append_assoc, Region.extendHostItems, ItemSeq.renameWires,
          ItemSeq.append_nil, ItemSeq.nil_append, childArgumentSource,
          mappedArgumentSource, mappedArgumentFrame, normalizationOperation,
          Transform.Frame.append] using moved⟩
    case refine_3 =>
      intros
      rename_i itemsCommon itemsSourceWires itemsTargetWires itemsPattern
        itemsFrame itemsData item tail itemResult tailResult itemEvidence
        tailEvidence itemSites tailSites formalSourceWires
        formalTargetWires formalFrame formalData _closeCommon _closeTarget
        itemIH tailIH
      let values := targetValues
      obtain ⟨itemRetained, itemFormalSource, itemFormalResult,
          itemFormalEvidence, itemFormalSites, itemCoherence, itemSemantic⟩ :=
        itemIH
      obtain ⟨tailRetained, tailFormalSource, tailFormalResult,
          tailFormalEvidence, tailFormalSites, tailCoherence, tailSemantic⟩ :=
        tailIH
      unfold TargetItems
      let combinedRetained := itemRetained ++ tailRetained
      let combinedFrame := formalFrame.append combinedRetained
      let combinedData := targetOperation.appendData formalFrame formalData
        combinedRetained
      let itemCommonRename := Region.conjoinLeftWire itemsCommon itemRetained
        tailRetained
      let tailCommonRename := Region.conjoinRightWire itemsCommon itemRetained
        tailRetained
      let itemSourceRename := Region.conjoinLeftWire formalSourceWires
        itemRetained tailRetained
      let tailSourceRename := Region.conjoinRightWire formalSourceWires
        itemRetained tailRetained
      let itemTargetRename := Region.conjoinLeftWire formalTargetWires
        itemRetained tailRetained
      let tailTargetRename := Region.conjoinRightWire formalTargetWires
        itemRetained tailRetained
      let authoritativeFrame : Transform.Frame patternWires itemsCommon
          itemsSourceWires itemsSourceWires := {
        sourceKeep := itemsFrame.sourceKeep
        targetKeep := itemsFrame.sourceKeep
        selected := itemsFrame.selected
      }
      let itemArgumentFrame := authoritativeFrame.append itemRetained
      let tailArgumentFrame := authoritativeFrame.append tailRetained
      let mappedArgumentFrame := authoritativeFrame.append combinedRetained
      let itemArgumentSourceRename := Region.conjoinLeftWire itemsSourceWires
        itemRetained tailRetained
      let tailArgumentSourceRename := Region.conjoinRightWire itemsSourceWires
        itemRetained tailRetained
      have itemArgumentKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ itemRetained) signature),
          itemArgumentSourceRename (itemArgumentFrame.sourceKeep wire) =
            mappedArgumentFrame.sourceKeep (itemCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := itemRetained)
          (motive := fun wire =>
            itemArgumentSourceRename (itemArgumentFrame.sourceKeep wire) =
              mappedArgumentFrame.sourceKeep (itemCommonRename wire)) <;>
          intro <;> simp [itemArgumentSourceRename, itemArgumentFrame,
            mappedArgumentFrame, authoritativeFrame, itemCommonRename,
            combinedRetained, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinLeftWire]
      have itemArgumentSelectedCommutes :
          itemArgumentSourceRename itemArgumentFrame.selected =
            mappedArgumentFrame.selected := by
        simp [itemArgumentSourceRename, itemArgumentFrame,
          mappedArgumentFrame, authoritativeFrame, combinedRetained,
          Transform.Frame.append, Region.conjoinLeftWire]
      have tailArgumentKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ tailRetained) signature),
          tailArgumentSourceRename (tailArgumentFrame.sourceKeep wire) =
            mappedArgumentFrame.sourceKeep (tailCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := tailRetained)
          (motive := fun wire =>
            tailArgumentSourceRename (tailArgumentFrame.sourceKeep wire) =
              mappedArgumentFrame.sourceKeep (tailCommonRename wire)) <;>
          intro <;> simp [tailArgumentSourceRename, tailArgumentFrame,
            mappedArgumentFrame, authoritativeFrame, tailCommonRename,
            combinedRetained, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinRightWire]
      have tailArgumentSelectedCommutes :
          tailArgumentSourceRename tailArgumentFrame.selected =
            mappedArgumentFrame.selected := by
        simp [tailArgumentSourceRename, tailArgumentFrame,
          mappedArgumentFrame, authoritativeFrame, combinedRetained,
          Transform.Frame.append, Region.conjoinRightWire]
      have itemKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ itemRetained) signature),
          itemSourceRename
              ((formalFrame.append itemRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (itemCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := itemRetained)
          (motive := fun wire => itemSourceRename
              ((formalFrame.append itemRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (itemCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, itemSourceRename,
            itemCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinLeftWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, itemSourceRename,
            itemCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinLeftWire]
      have itemSelectedCommutes :
          itemSourceRename (formalFrame.append itemRetained).selected =
            combinedFrame.selected := by
        simp [combinedFrame, combinedRetained, itemSourceRename,
          Transform.Frame.append, Region.conjoinLeftWire]
      have itemTargetKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ itemRetained) signature),
          itemTargetRename
              ((formalFrame.append itemRetained).targetKeep wire) =
            combinedFrame.targetKeep (itemCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := itemRetained)
          (motive := fun wire => itemTargetRename
              ((formalFrame.append itemRetained).targetKeep wire) =
            combinedFrame.targetKeep (itemCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, itemTargetRename,
            itemCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinLeftWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, itemTargetRename,
            itemCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinLeftWire]
      have tailKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ tailRetained) signature),
          tailSourceRename
              ((formalFrame.append tailRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (tailCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := tailRetained)
          (motive := fun wire => tailSourceRename
              ((formalFrame.append tailRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (tailCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, tailSourceRename,
            tailCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinRightWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, tailSourceRename,
            tailCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinRightWire]
      have tailSelectedCommutes :
          tailSourceRename (formalFrame.append tailRetained).selected =
            combinedFrame.selected := by
        simp [combinedFrame, combinedRetained, tailSourceRename,
          Transform.Frame.append, Region.conjoinRightWire]
      have tailTargetKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ tailRetained) signature),
          tailTargetRename
              ((formalFrame.append tailRetained).targetKeep wire) =
            combinedFrame.targetKeep (tailCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := tailRetained)
          (motive := fun wire => tailTargetRename
              ((formalFrame.append tailRetained).targetKeep wire) =
            combinedFrame.targetKeep (tailCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, tailTargetRename,
            tailCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinRightWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, tailTargetRename,
            tailCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinRightWire]
      obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
          mappedItemSites, mappedItemSourceEq, mappedItemArgumentEq,
          mappedItemSourceArgumentEq,
          ⟨mappedItemPresentation⟩,
          ⟨mappedItemEndpointPresentation⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := targetExternal)
          itemFormalEvidence itemFormalSites values sourceValues
          itemArgumentFrame mappedArgumentFrame itemCommonRename
          itemSourceRename itemTargetRename itemArgumentSourceRename
          itemKeepCommutes itemTargetKeepCommutes itemSelectedCommutes
          itemArgumentKeepCommutes itemArgumentSelectedCommutes targetNaturality
          (targetNaturality.conjoinLeft formalFrame formalData itemRetained
            tailRetained)
      obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
          mappedTailSites, mappedTailSourceEq, mappedTailArgumentEq,
          mappedTailSourceArgumentEq,
          ⟨mappedTailPresentation⟩,
          ⟨mappedTailEndpointPresentation⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := targetExternal)
          tailFormalEvidence tailFormalSites values sourceValues
          tailArgumentFrame mappedArgumentFrame tailCommonRename
          tailSourceRename tailTargetRename tailArgumentSourceRename
          tailKeepCommutes tailTargetKeepCommutes tailSelectedCommutes
          tailArgumentKeepCommutes tailArgumentSelectedCommutes targetNaturality
          (targetNaturality.conjoinRight formalFrame formalData itemRetained
            tailRetained)
      obtain ⟨combinedResult, combinedEvidence, combinedSites,
          combinedArgumentEq, combinedSourceArgumentEq,
          ⟨combinedPresentation⟩,
          ⟨combinedEndpointPresentation⟩⟩ :=
        targetItemsAppend mappedItemEvidence mappedItemSites
          mappedTailEvidence mappedTailSites values sourceValues
          mappedArgumentFrame
      have mappedItemCoherence : mappedItemSource =
          (argumentItemsEdit mappedItemSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedItemSource = itemFormalSource.renameWires itemSourceRename :=
            mappedItemSourceEq.symm
          _ = (argumentItemsEdit itemFormalSites values
                (normalizationOperation targetArguments)
                (formalFrame.append itemRetained) PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires itemSourceRename :=
            congrArg (fun items => items.renameWires itemSourceRename)
              itemCoherence
          _ = _ := mappedItemArgumentEq
      have mappedTailCoherence : mappedTailSource =
          (argumentItemsEdit mappedTailSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedTailSource = tailFormalSource.renameWires tailSourceRename :=
            mappedTailSourceEq.symm
          _ = (argumentItemsEdit tailFormalSites values
                (normalizationOperation targetArguments)
                (formalFrame.append tailRetained) PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires tailSourceRename :=
            congrArg (fun items => items.renameWires tailSourceRename)
              tailCoherence
          _ = _ := mappedTailArgumentEq
      have combinedCoherence : mappedItemSource.append mappedTailSource =
          (argumentItemsEdit combinedSites values
            (normalizationOperation targetArguments) combinedFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedItemSource.append mappedTailSource =
              (argumentItemsEdit mappedItemSites values
                (normalizationOperation targetArguments) combinedFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.append
                mappedTailSource := congrArg
                  (fun first => first.append mappedTailSource)
                  mappedItemCoherence
          _ = (argumentItemsEdit mappedItemSites values
                (normalizationOperation targetArguments) combinedFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.append
                (argumentItemsEdit mappedTailSites values
                  (normalizationOperation targetArguments) combinedFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1 := congrArg
                    (fun second =>
                      (argumentItemsEdit mappedItemSites values
                        (normalizationOperation targetArguments)
                        combinedFrame PUnit.unit
                        (fun _ _ _ => PUnit.unit)).1.append second)
                    mappedTailCoherence
          _ = _ := combinedArgumentEq.symm
      refine ⟨combinedRetained,
        mappedItemSource.append mappedTailSource, combinedResult,
        combinedEvidence, combinedSites, combinedCoherence, ?_⟩
      intro patternEq
      cases patternEq
      obtain ⟨itemStaged, itemHosted, itemScope,
          ⟨itemPresentation⟩, itemEndpoint, itemSourceSide,
          itemRetainedOk⟩ :=
        itemSemantic rfl
      obtain ⟨tailStaged, tailHosted, tailScope,
          ⟨tailPresentation⟩, tailEndpoint, tailSourceSide,
          tailRetainedOk⟩ :=
        tailSemantic rfl
      let staged := itemStaged.conjoin tailStaged
      have stagedSide : Side
          (itemResult.conjoin tailResult) staged := by
        exact sideConjoin itemScope tailScope
      have hosted : HostedStrict
          (itemResult.conjoin tailResult) staged := by
        simpa only [staged] using HostedStrict.conjoin itemResult tailResult
          itemStaged tailStaged itemHosted tailHosted
      let endpointMerged :=
        (RegionIso.conjoinCongr itemPresentation tailPresentation).trans
          (RegionIso.conjoinAdjoinAt itemRetained tailRetained
            itemFormalResult tailFormalResult)
      let mappedChildren := RegionIso.conjoinCongr mappedItemPresentation
        mappedTailPresentation
      let mappedUnderHost := RegionIso.adjoinAt combinedRetained .nil
        mappedChildren
      let combinedUnderHost := RegionIso.adjoinAt combinedRetained .nil
        combinedPresentation
      have presentation : RegionIso (WireEquiv.refl itemsCommon) staged
          (Region.adjoinAt combinedRetained .nil combinedResult) := by
        simpa only [staged, combinedRetained] using
          (endpointMerged.trans mappedUnderHost).trans combinedUnderHost
      exact ⟨staged, hosted, stagedSide, ⟨presentation⟩, by
        intro bridge alignment
        obtain ⟨itemEndpointIso⟩ := itemEndpoint bridge alignment
        obtain ⟨tailEndpointIso⟩ := tailEndpoint bridge alignment
        let itemRaw := (itemEdit itemsData itemEvidence itemSites).endpoint
        let tailRaw := (itemsEdit itemsData tailEvidence tailSites).endpoint
        let splitRename := RegionIso.renameWiresConjoin itemRaw tailRaw
          alignment.ambient.toRenaming
        let itemTargetSource := itemFormalSource.renameWires
          (bridge.sourceToTarget.appendRight itemRetained)
        let tailTargetSource := tailFormalSource.renameWires
          (bridge.sourceToTarget.appendRight tailRetained)
        let combinedTargetSource :=
          (mappedItemSource.append mappedTailSource).renameWires
            (bridge.sourceToTarget.appendRight combinedRetained)
        let itemToAdjoined := itemEndpointIso.trans
          (RegionIso.adjoinAtOfItems itemRetained itemTargetSource).symm
        let tailToAdjoined := tailEndpointIso.trans
          (RegionIso.adjoinAtOfItems tailRetained tailTargetSource).symm
        let children := RegionIso.conjoinCongr itemToAdjoined tailToAdjoined
        let flattened := RegionIso.conjoinAdjoinAt itemRetained tailRetained
          (Region.ofItems itemTargetSource) (Region.ofItems tailTargetSource)
        have itemRenameEq :
            WireRenaming.comp
                (Region.conjoinLeftWire formalTargetWires itemRetained
                  tailRetained)
                (bridge.sourceToTarget.appendRight itemRetained) =
              WireRenaming.comp
                (bridge.sourceToTarget.appendRight combinedRetained)
                itemSourceRename := by
          apply WireRenaming.ext
          intro signature wire
          apply Var.appendCases (left := formalSourceWires)
            (right := itemRetained)
            (motive := fun wire =>
              WireRenaming.comp
                    (Region.conjoinLeftWire formalTargetWires itemRetained
                      tailRetained)
                    (bridge.sourceToTarget.appendRight itemRetained) wire =
                WireRenaming.comp
                    (bridge.sourceToTarget.appendRight combinedRetained)
                    itemSourceRename wire) <;>
            intro <;> simp [combinedRetained, itemSourceRename,
              Region.conjoinLeftWire, WireRenaming.appendRight,
              WireRenaming.comp]
        have tailRenameEq :
            WireRenaming.comp
                (Region.conjoinRightWire formalTargetWires itemRetained
                  tailRetained)
                (bridge.sourceToTarget.appendRight tailRetained) =
              WireRenaming.comp
                (bridge.sourceToTarget.appendRight combinedRetained)
                tailSourceRename := by
          apply WireRenaming.ext
          intro signature wire
          apply Var.appendCases (left := formalSourceWires)
            (right := tailRetained)
            (motive := fun wire =>
              WireRenaming.comp
                    (Region.conjoinRightWire formalTargetWires itemRetained
                      tailRetained)
                    (bridge.sourceToTarget.appendRight tailRetained) wire =
                WireRenaming.comp
                    (bridge.sourceToTarget.appendRight combinedRetained)
                    tailSourceRename wire) <;>
            intro <;> simp [combinedRetained, tailSourceRename,
              Region.conjoinRightWire, WireRenaming.appendRight,
              WireRenaming.comp]
        have ofItemsRenameEq : ∀ {sourceWires targetWires : List Sig}
            (source : ItemSeq sourceWires)
            (rename : WireRenaming sourceWires targetWires),
            (Region.ofItems source).renameWires rename =
              Region.ofItems (source.renameWires rename) := by
          intro sourceWires targetWires source rename
          unfold Region.ofItems Region.renameWires
          congr 1
          simp only [ItemSeq.renameWires_comp]
          apply congrArg (fun mapped => source.renameWires mapped)
          apply WireRenaming.ext
          intro signature wire
          simp [WireRenaming.comp, WireRenaming.appendRight]
        have itemItemsEq :
            itemTargetSource.renameWires
                (Region.conjoinLeftWire formalTargetWires itemRetained
                  tailRetained) =
              mappedItemSource.renameWires
                (bridge.sourceToTarget.appendRight combinedRetained) := by
          unfold itemTargetSource
          rw [← mappedItemSourceEq]
          simp only [ItemSeq.renameWires_comp]
          rw [itemRenameEq]
        have tailItemsEq :
            tailTargetSource.renameWires
                (Region.conjoinRightWire formalTargetWires itemRetained
                  tailRetained) =
              mappedTailSource.renameWires
                (bridge.sourceToTarget.appendRight combinedRetained) := by
          unfold tailTargetSource
          rw [← mappedTailSourceEq]
          simp only [ItemSeq.renameWires_comp]
          rw [tailRenameEq]
        have materialEq :
            ((Region.ofItems itemTargetSource).renameWires
                (Region.conjoinLeftWire formalTargetWires itemRetained
                  tailRetained)).conjoin
              ((Region.ofItems tailTargetSource).renameWires
                (Region.conjoinRightWire formalTargetWires itemRetained
                  tailRetained)) =
            Region.ofItems combinedTargetSource := by
          rw [ofItemsRenameEq, ofItemsRenameEq, Region.ofItems_conjoin,
            itemItemsEq, tailItemsEq]
          unfold combinedTargetSource
          rw [ItemSeq.renameWires_append]
        let materialPresentation := RegionIso.adjoinAt combinedRetained .nil
          (RegionIso.ofEq materialEq)
        let closePresentation :=
          RegionIso.adjoinAtOfItems combinedRetained combinedTargetSource
        let chained := (((splitRename.trans children).trans flattened).trans
          materialPresentation).trans closePresentation
        exact ⟨by
          simpa only [itemRaw, tailRaw, itemTargetSource, tailTargetSource,
            combinedTargetSource, Transform.ItemsEdit.run, itemsEdit,
            combinedRetained] using chained⟩, by
        let itemArgumentItems :=
          (argumentItemsEdit itemFormalSites sourceValues
            (normalizationOperation patternWires) itemArgumentFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1
        let tailArgumentItems :=
          (argumentItemsEdit tailFormalSites sourceValues
            (normalizationOperation patternWires) tailArgumentFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1
        have combinedSource := sourceSideConjoin itemSourceSide tailSourceSide
        let flattened := RegionIso.conjoinAdjoinAt itemRetained tailRetained
          (Region.ofItems itemArgumentItems) (Region.ofItems tailArgumentItems)
        have ofItemsRenameEq : ∀ {sourceWires targetWires : List Sig}
            (source : ItemSeq sourceWires)
            (rename : WireRenaming sourceWires targetWires),
            (Region.ofItems source).renameWires rename =
              Region.ofItems (source.renameWires rename) := by
          intro sourceWires targetWires source rename
          unfold Region.ofItems Region.renameWires
          congr 1
          simp only [ItemSeq.renameWires_comp]
          apply congrArg (fun mapped => source.renameWires mapped)
          apply WireRenaming.ext
          intro signature wire
          simp [WireRenaming.comp, WireRenaming.appendRight]
        have materialEq :
            ((Region.ofItems itemArgumentItems).renameWires
                itemArgumentSourceRename).conjoin
              ((Region.ofItems tailArgumentItems).renameWires
                tailArgumentSourceRename) =
              Region.ofItems
                (argumentItemsEdit combinedSites sourceValues
                  (normalizationOperation patternWires) mappedArgumentFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
          rw [ofItemsRenameEq, ofItemsRenameEq,
            mappedItemSourceArgumentEq, mappedTailSourceArgumentEq,
            Region.ofItems_conjoin, combinedSourceArgumentEq]
        let materialPresentation := RegionIso.adjoinAt combinedRetained .nil
          (RegionIso.ofEq materialEq)
        have moved := sourceSideIso
          (RegionIso.ofEq
            (Region.singleton_conjoin_ofItems item tail).symm)
          (flattened.trans materialPresentation) combinedSource
        simpa only [combinedRetained, itemArgumentItems, tailArgumentItems,
          itemArgumentFrame, tailArgumentFrame, mappedArgumentFrame,
          authoritativeFrame] using moved,
        retainedAppend itemRetained tailRetained itemRetainedOk
          tailRetainedOk⟩
    case refine_4 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires itemArguments
        evidencePattern itemPattern itemFrame itemData atomHead atomPorts
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget
      let values := targetValues
      unfold TargetItem
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonAppend := commonEquiv.symm.toRenaming
      let mappedHead := commonAppend atomHead
      let mappedPorts := atomPorts.map fun wire => commonAppend wire
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton (.atom mappedHead mappedPorts)
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .atom (childFrame.sourceKeep mappedHead)
          (mappedPorts.map fun wire => childFrame.sourceKeep wire)
      let formalItemEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .atom mappedHead mappedPorts
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := ItemSites.atom
            (pattern := targetPattern)
            (frame := childFrame) mappedHead mappedPorts
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      let staged := Region.singleton (.atom atomHead atomPorts)
      have hosted : HostedStrict staged staged := by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simpa only [EqualityNormalization.StrictEquates] using
          EqualityNormalization.StrictEquates.refl occurrence
      let appendRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let stagedMapped := staged.renameWires appendRename
      have stagedMappedEq : stagedMapped = formalItemResult := by
        simp only [stagedMapped, staged, appendRename, formalItemResult,
          Region.singleton_renameWires, Item.renameWires, mappedHead,
          mappedPorts, commonAppend]
      let intoMapped : RegionIso commonEquiv.symm staged formalItemResult :=
        (by
          let renamed := RegionIso.renameWires staged WireRenaming.id
            appendRename commonEquiv.symm (by
              intro signature wire
              rfl)
          rw [Region.renameWires_id] at renamed
          have targetEq : staged.renameWires appendRename =
              formalItemResult := stagedMappedEq
          rw [targetEq] at renamed
          exact renamed)
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        intoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      let formalPresentation := closed.castAmbient ambientEq
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        by rfl, ?_⟩
      intro patternEq
      cases patternEq
      refine ⟨staged, hosted, sideRefl staged, ⟨formalPresentation⟩,
        ?_, ?_, retainedNil⟩
      ·
        intro bridge alignment
        let material : Region (formalTargetWires ++ []) :=
          Region.ofItems (formalSource.renameWires
            (bridge.sourceToTarget.appendRight []))
        have headEq : alignment.ambient.toRenaming
              (itemFrame.targetKeep atomHead) =
            (WireEquiv.appendNil formalTargetWires).toRenaming
              ((bridge.sourceToTarget.appendRight [])
                (childFrame.sourceKeep mappedHead)) := by
          rw [alignment.keep_commutes atomHead]
          rw [← bridge.keep_commutes atomHead]
          rw [show mappedHead = atomHead.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon atomHead]
          simp [childFrame, Transform.Frame.append,
            WireRenaming.appendRight]
        have portsEq :
            (atomPorts.map fun wire =>
              (alignment.ambient.toRenaming
                (itemFrame.targetKeep wire))) =
            (((mappedPorts.map fun wire => childFrame.sourceKeep wire).map
              fun wire => (bridge.sourceToTarget.appendRight []) wire).map
                (fun wire =>
                  (WireEquiv.appendNil formalTargetWires).toRenaming wire)) := by
          unfold mappedPorts
          rw [Vars.map_map, Vars.map_map, Vars.map_map]
          apply Vars.map_congr
          intro signature wire
          rw [alignment.keep_commutes]
          rw [← bridge.keep_commutes wire]
          rw [show commonAppend wire = wire.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon wire]
          simp [childFrame, Transform.Frame.append,
            WireRenaming.appendRight]
        have sourceEq :
            (Region.singleton (.atom (itemFrame.targetKeep atomHead)
              (atomPorts.map fun wire =>
                itemFrame.targetKeep wire))).renameWires
                alignment.ambient.toRenaming =
              material.renameWires
                (WireEquiv.appendNil formalTargetWires).toRenaming := by
          simp only [material, formalSource, formalItemSource, Region.ofItems,
            Region.singleton_renameWires, Region.renameWires,
            ItemSeq.renameWires, Item.renameWires, ItemSeq.append_nil,
            ItemSeq.renameWires_comp, WireRenaming.appendRight,
            Var.appendMap_left, WireEquiv.appendNil_apply]
          rw [headEq, Vars.map_map, portsEq]
          simp [Region.singleton, Region.ofItems, Vars.map_map,
            WireRenaming.appendRight, ItemSeq.renameWires,
            Item.renameWires]
        refine ⟨?_⟩
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run] using
          (RegionIso.ofEq sourceEq).trans
            ((RegionIso.adjoinAtNil material).trans
              (RegionIso.adjoinAtOfItems []
                (formalSource.renameWires
                  (bridge.sourceToTarget.appendRight []))))
      · let sourceMaterial : Region itemSourceWires :=
          Region.singleton (.atom (itemFrame.sourceKeep atomHead)
            (atomPorts.map fun wire => itemFrame.sourceKeep wire))
        let authoritativeFrame : Transform.Frame patternWires itemCommon
            itemSourceWires itemSourceWires := {
          sourceKeep := itemFrame.sourceKeep
          targetKeep := itemFrame.sourceKeep
          selected := itemFrame.selected
        }
        let targetMaterial := Region.ofItems
          (argumentItemsEdit formalSites sourceValues
            (normalizationOperation patternWires)
            (authoritativeFrame.append [])
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        have targetEq : sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            targetMaterial := by
          change sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            Region.ofItems (.cons
              (.atom ((authoritativeFrame.append []).sourceKeep mappedHead)
                (mappedPorts.map fun wire =>
                  (authoritativeFrame.append []).sourceKeep wire)) .nil)
          rw [Region.singleton_renameWires]
          change Region.singleton _ = Region.singleton _
          apply congrArg Region.singleton
          simp only [Item.renameWires]
          congr 1 <;>
            simp [authoritativeFrame, mappedHead, mappedPorts, commonAppend,
              commonEquiv,
              Transform.Frame.append, WireRenaming.appendRight,
              WireEquiv.appendNil_symm_apply, Vars.map_map]
        let sourcePresentation :=
          (RegionIso.adjoinAtNilRenamed sourceMaterial).trans
            (RegionIso.adjoinAt [] .nil (RegionIso.ofEq targetEq))
        exact sourceSideIso (RegionIso.refl _) sourcePresentation
          (sourceSideRefl sourceMaterial)
    case refine_5 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires evidencePattern
        itemPattern itemFrame itemData application siteData formalSourceWires
        formalTargetWires formalFrame formalData _closeCommon _closeTarget
      unfold TargetItem
      obtain ⟨retained, formalSource, formalResult, formalEvidence,
          formalSites, coherence, selectedSemantic⟩ :=
        selectedCase application siteData formalFrame formalData
      refine ⟨retained, formalSource, formalResult, formalEvidence,
        formalSites, coherence, ?_⟩
      intro patternEq
      cases patternEq
      exact selectedSemantic
    case refine_6 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires evidencePattern
        itemPattern itemFrame itemData identitySignature identityArity identityPorts
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget
      let values := targetValues
      unfold TargetItem
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonAppend := commonEquiv.symm.toRenaming
      let mappedPorts := fun position => commonAppend (identityPorts position)
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton
          (.identity identitySignature identityArity mappedPorts)
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .identity identitySignature identityArity
          (fun position => childFrame.sourceKeep (mappedPorts position))
      let formalItemEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .identity identitySignature identityArity mappedPorts
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := ItemSites.identity
            (pattern := targetPattern)
            (frame := childFrame) identitySignature identityArity mappedPorts
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      let staged := Region.singleton
        (.identity identitySignature identityArity identityPorts)
      have hosted : HostedStrict staged staged := by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simpa only [EqualityNormalization.StrictEquates] using
          EqualityNormalization.StrictEquates.refl occurrence
      let appendRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let stagedMapped := staged.renameWires appendRename
      have stagedMappedEq : stagedMapped = formalItemResult := by
        simp only [stagedMapped, staged, appendRename, formalItemResult,
          Region.singleton_renameWires, Item.renameWires, mappedPorts,
          commonAppend]
      let intoMapped : RegionIso commonEquiv.symm staged formalItemResult :=
        (by
          let renamed := RegionIso.renameWires staged WireRenaming.id
            appendRename commonEquiv.symm (by
              intro signature wire
              rfl)
          rw [Region.renameWires_id] at renamed
          have targetEq : staged.renameWires appendRename =
              formalItemResult := stagedMappedEq
          rw [targetEq] at renamed
          exact renamed)
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        intoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      let formalPresentation := closed.castAmbient ambientEq
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        by rfl, ?_⟩
      intro patternEq
      cases patternEq
      refine ⟨staged, hosted, sideRefl staged, ⟨formalPresentation⟩,
        ?_, ?_, retainedNil⟩
      · intro bridge alignment
        let material : Region (formalTargetWires ++ []) :=
          Region.ofItems (formalSource.renameWires
            (bridge.sourceToTarget.appendRight []))
        have portsEq : (
              fun position => alignment.ambient.toRenaming
                (itemFrame.targetKeep (identityPorts position))) =
            (fun position =>
              (WireEquiv.appendNil formalTargetWires).toRenaming
                ((bridge.sourceToTarget.appendRight [])
                  (childFrame.sourceKeep (mappedPorts position)))) := by
          funext position
          rw [alignment.keep_commutes]
          rw [← bridge.keep_commutes (identityPorts position)]
          rw [show mappedPorts position =
              (identityPorts position).appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon
              (identityPorts position)]
          simp [childFrame, Transform.Frame.append,
            WireRenaming.appendRight]
        have sourceEq :
            (Region.singleton (.identity identitySignature identityArity
              (fun position => itemFrame.targetKeep
                (identityPorts position)))).renameWires
                alignment.ambient.toRenaming =
              material.renameWires
                (WireEquiv.appendNil formalTargetWires).toRenaming := by
          simp only [material, formalSource, formalItemSource, Region.ofItems,
            Region.singleton_renameWires, Region.renameWires,
            ItemSeq.renameWires, Item.renameWires, ItemSeq.append_nil,
            ItemSeq.renameWires_comp, WireRenaming.appendRight,
            Var.appendMap_left, WireEquiv.appendNil_apply]
          rw [portsEq]
          simp [Region.singleton, Region.ofItems,
            WireRenaming.appendRight, ItemSeq.renameWires,
            Item.renameWires]
        refine ⟨?_⟩
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          WireEquiv.trans_refl] using
          (RegionIso.ofEq sourceEq).trans
            ((RegionIso.adjoinAtNil material).trans
              (RegionIso.adjoinAtOfItems []
                (formalSource.renameWires
                  (bridge.sourceToTarget.appendRight []))))
      · let sourceMaterial : Region itemSourceWires :=
          Region.singleton (.identity identitySignature identityArity
            (fun position => itemFrame.sourceKeep
              (identityPorts position)))
        let authoritativeFrame : Transform.Frame patternWires itemCommon
            itemSourceWires itemSourceWires := {
          sourceKeep := itemFrame.sourceKeep
          targetKeep := itemFrame.sourceKeep
          selected := itemFrame.selected
        }
        let targetMaterial := Region.ofItems
          (argumentItemsEdit formalSites sourceValues
            (normalizationOperation patternWires)
            (authoritativeFrame.append [])
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        have targetEq : sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            targetMaterial := by
          change sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            Region.ofItems (.cons
              (.identity identitySignature identityArity fun position =>
                (authoritativeFrame.append []).sourceKeep
                  (mappedPorts position)) .nil)
          rw [Region.singleton_renameWires]
          change Region.singleton _ = Region.singleton _
          apply congrArg Region.singleton
          simp only [Item.renameWires]
          congr 1
          funext position
          simp [authoritativeFrame, mappedPorts, commonAppend, commonEquiv,
            Transform.Frame.append, WireRenaming.appendRight,
            WireEquiv.appendNil_symm_apply]
        let sourcePresentation :=
          (RegionIso.adjoinAtNilRenamed sourceMaterial).trans
            (RegionIso.adjoinAt [] .nil (RegionIso.ofEq targetEq))
        exact sourceSideIso (RegionIso.refl _) sourcePresentation
          (sourceSideRefl sourceMaterial)
    case refine_7 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires evidencePattern
        itemPattern itemFrame itemData termOutput termFreeArity termPorts
        lambdaTerm formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget
      let values := targetValues
      unfold TargetItem
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonAppend := commonEquiv.symm.toRenaming
      let mappedOutput := commonAppend termOutput
      let mappedPorts := fun position => commonAppend (termPorts position)
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton
          (.term mappedOutput termFreeArity mappedPorts lambdaTerm)
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .term (childFrame.sourceKeep mappedOutput) termFreeArity
          (fun position => childFrame.sourceKeep (mappedPorts position))
          lambdaTerm
      let formalItemEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .term mappedOutput termFreeArity mappedPorts lambdaTerm
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData formalItemEvidence :=
        ItemSites.term (pattern := targetPattern) (frame := childFrame)
          mappedOutput termFreeArity mappedPorts lambdaTerm
      let formalSites : ItemsSites
          targetOperation childData formalEvidence :=
        .cons formalItemSites (.nil tailEvidence)
      let staged := Region.singleton
        (.term termOutput termFreeArity termPorts lambdaTerm)
      have hosted : HostedStrict staged staged := by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simpa only [EqualityNormalization.StrictEquates] using
          EqualityNormalization.StrictEquates.refl occurrence
      let appendRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let stagedMapped := staged.renameWires appendRename
      have stagedMappedEq : stagedMapped = formalItemResult := by
        simp only [stagedMapped, staged, appendRename, formalItemResult,
          Region.singleton_renameWires, Item.renameWires, mappedOutput,
          mappedPorts, commonAppend]
      let intoMapped : RegionIso commonEquiv.symm staged formalItemResult :=
        (by
          let renamed := RegionIso.renameWires staged WireRenaming.id
            appendRename commonEquiv.symm (by
              intro signature wire
              rfl)
          rw [Region.renameWires_id] at renamed
          have targetEq : staged.renameWires appendRename =
              formalItemResult := stagedMappedEq
          rw [targetEq] at renamed
          exact renamed)
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        intoMapped.trans ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      let formalPresentation := closed.castAmbient ambientEq
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        by rfl, ?_⟩
      intro patternEq
      cases patternEq
      refine ⟨staged, hosted, sideRefl staged, ⟨formalPresentation⟩,
        ?_, ?_, retainedNil⟩
      · intro bridge alignment
        let material : Region (formalTargetWires ++ []) :=
          Region.ofItems (formalSource.renameWires
            (bridge.sourceToTarget.appendRight []))
        have outputEq :
            alignment.ambient.toRenaming
                (itemFrame.targetKeep termOutput) =
              (WireEquiv.appendNil formalTargetWires).toRenaming
                ((bridge.sourceToTarget.appendRight [])
                  (childFrame.sourceKeep mappedOutput)) := by
          rw [alignment.keep_commutes]
          rw [← bridge.keep_commutes termOutput]
          rw [show mappedOutput = termOutput.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon termOutput]
          simp [childFrame, Transform.Frame.append,
            WireRenaming.appendRight]
        have portsEq :
            (fun position => alignment.ambient.toRenaming
              (itemFrame.targetKeep (termPorts position))) =
            (fun position =>
              (WireEquiv.appendNil formalTargetWires).toRenaming
                ((bridge.sourceToTarget.appendRight [])
                  (childFrame.sourceKeep (mappedPorts position)))) := by
          funext position
          rw [alignment.keep_commutes]
          rw [← bridge.keep_commutes (termPorts position)]
          rw [show mappedPorts position =
              (termPorts position).appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon
              (termPorts position)]
          simp [childFrame, Transform.Frame.append,
            WireRenaming.appendRight]
        have sourceEq :
            (Region.singleton (.term
              (itemFrame.targetKeep termOutput) termFreeArity
              (fun position => itemFrame.targetKeep (termPorts position))
              lambdaTerm)).renameWires alignment.ambient.toRenaming =
              material.renameWires
                (WireEquiv.appendNil formalTargetWires).toRenaming := by
          simp only [material, formalSource, formalItemSource, Region.ofItems,
            Region.singleton_renameWires, Region.renameWires,
            ItemSeq.renameWires, Item.renameWires, ItemSeq.append_nil,
            ItemSeq.renameWires_comp, WireRenaming.appendRight,
            Var.appendMap_left, WireEquiv.appendNil_apply]
          rw [outputEq, portsEq]
          simp [Region.singleton, Region.ofItems,
            WireRenaming.appendRight, ItemSeq.renameWires,
            Item.renameWires]
        refine ⟨?_⟩
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          WireEquiv.trans_refl] using
          (RegionIso.ofEq sourceEq).trans
            ((RegionIso.adjoinAtNil material).trans
              (RegionIso.adjoinAtOfItems []
                (formalSource.renameWires
                  (bridge.sourceToTarget.appendRight []))))
      · let sourceMaterial : Region itemSourceWires :=
          Region.singleton (.term (itemFrame.sourceKeep termOutput)
            termFreeArity
            (fun position => itemFrame.sourceKeep (termPorts position))
            lambdaTerm)
        let authoritativeFrame : Transform.Frame patternWires itemCommon
            itemSourceWires itemSourceWires := {
          sourceKeep := itemFrame.sourceKeep
          targetKeep := itemFrame.sourceKeep
          selected := itemFrame.selected
        }
        let targetMaterial := Region.ofItems
          (argumentItemsEdit formalSites sourceValues
            (normalizationOperation patternWires)
            (authoritativeFrame.append [])
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        have targetEq : sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            targetMaterial := by
          change sourceMaterial.renameWires
              (WireEquiv.appendNil itemSourceWires).symm.toRenaming =
            Region.ofItems (.cons
              (.term
                ((authoritativeFrame.append []).sourceKeep mappedOutput)
                termFreeArity
                (fun position =>
                  (authoritativeFrame.append []).sourceKeep
                    (mappedPorts position)) lambdaTerm) .nil)
          rw [Region.singleton_renameWires]
          change Region.singleton _ = Region.singleton _
          apply congrArg Region.singleton
          simp only [Item.renameWires]
          congr 1
          · simp [authoritativeFrame, mappedOutput, commonAppend,
              commonEquiv, Transform.Frame.append,
              WireRenaming.appendRight, WireEquiv.appendNil_symm_apply]
          · funext position
            simp [authoritativeFrame, mappedPorts, commonAppend,
              commonEquiv, Transform.Frame.append,
              WireRenaming.appendRight, WireEquiv.appendNil_symm_apply]
        let sourcePresentation :=
          (RegionIso.adjoinAtNilRenamed sourceMaterial).trans
            (RegionIso.adjoinAt [] .nil (RegionIso.ofEq targetEq))
        exact sourceSideIso (RegionIso.refl _) sourcePresentation
          (sourceSideRefl sourceMaterial)
    case refine_8 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires itemPattern
        itemFrame itemData body childResult childEvidence childSites
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget childIH
      let values := targetValues
      unfold TargetItem
      obtain ⟨childFormalSource, childFormalResult, childFormalEvidence,
          childFormalSites, childCoherence, childSemantic⟩ :=
        childIH
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let sourceEquiv := WireEquiv.appendNil formalSourceWires
      let sourceRename : WireRenaming formalSourceWires
          (formalSourceWires ++ []) := sourceEquiv.symm.toRenaming
      let targetEquiv := WireEquiv.appendNil formalTargetWires
      let targetAppend : WireRenaming formalTargetWires
          (formalTargetWires ++ []) := targetEquiv.symm.toRenaming
      let argumentEquiv := WireEquiv.appendNil itemSourceWires
      let argumentSourceRename : WireRenaming itemSourceWires
          (itemSourceWires ++ []) := argumentEquiv.symm.toRenaming
      let argumentFrame : Transform.Frame patternWires itemCommon
          itemSourceWires itemSourceWires := {
        sourceKeep := itemFrame.sourceKeep
        targetKeep := itemFrame.sourceKeep
        selected := itemFrame.selected
      }
      let mappedArgumentFrame := argumentFrame.append []
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      have keepCommutes : ∀ {signature} (wire : Var itemCommon signature),
          sourceRename (formalFrame.sourceKeep wire) =
            childFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        rw [show sourceRename (formalFrame.sourceKeep wire) =
            (formalFrame.sourceKeep wire).appendLeft [] by
          exact WireEquiv.appendNil_symm_apply formalSourceWires
            (formalFrame.sourceKeep wire)]
        rw [show commonRename wire = wire.appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemCommon wire]
        simp [childFrame, Transform.Frame.append,
          WireRenaming.appendRight]
      have selectedCommutes : sourceRename formalFrame.selected =
          childFrame.selected := by
        exact WireEquiv.appendNil_symm_apply formalSourceWires
          formalFrame.selected
      have targetKeepCommutes : ∀ {signature}
          (wire : Var itemCommon signature),
          targetAppend (formalFrame.targetKeep wire) =
            childFrame.targetKeep (commonRename wire) := by
        intro signature wire
        rw [show targetAppend (formalFrame.targetKeep wire) =
            (formalFrame.targetKeep wire).appendLeft [] by
          exact WireEquiv.appendNil_symm_apply formalTargetWires
            (formalFrame.targetKeep wire)]
        rw [show commonRename wire = wire.appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemCommon wire]
        simp [childFrame, Transform.Frame.append,
          WireRenaming.appendRight]
      have argumentKeepCommutes : ∀ {signature}
          (wire : Var itemCommon signature),
          argumentSourceRename (argumentFrame.sourceKeep wire) =
            mappedArgumentFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        rw [show argumentSourceRename (argumentFrame.sourceKeep wire) =
            (argumentFrame.sourceKeep wire).appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemSourceWires
            (argumentFrame.sourceKeep wire)]
        rw [show commonRename wire = wire.appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemCommon wire]
        simp [mappedArgumentFrame, argumentFrame, Transform.Frame.append,
          WireRenaming.appendRight]
      have argumentSelectedCommutes :
          argumentSourceRename argumentFrame.selected =
            mappedArgumentFrame.selected := by
        exact WireEquiv.appendNil_symm_apply itemSourceWires
          argumentFrame.selected
      obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
          mappedChildSites, mappedChildSourceEq,
          mappedChildArgumentEq,
          mappedChildSourceArgumentEq,
          ⟨mappedChildPresentation⟩,
          ⟨mappedChildEndpointPresentation⟩⟩ :=
        targetRegionReindex (mappedData := childData)
          (baseOperation := targetBaseOperation)
          (external := targetExternal)
          childFormalEvidence childFormalSites values sourceValues
          argumentFrame mappedArgumentFrame commonRename sourceRename
          targetAppend argumentSourceRename keepCommutes targetKeepCommutes
          selectedCommutes argumentKeepCommutes argumentSelectedCommutes
          targetNaturality
          (targetNaturality.appendNil formalFrame formalData)
      have mappedChildCoherence : mappedChildSource =
          (argumentRegionEdit mappedChildSites values
            (normalizationOperation targetArguments) childFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedChildSource = childFormalSource.renameWires sourceRename :=
            mappedChildSourceEq.symm
          _ = (argumentRegionEdit childFormalSites values
                (normalizationOperation targetArguments) formalFrame PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
            congrArg (fun region => region.renameWires sourceRename)
              childCoherence
          _ = _ := mappedChildArgumentEq
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .cut mappedChildSource
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton (.cut mappedChildResult)
      let formalItemEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .cut mappedChildEvidence
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := .cut mappedChildSites
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      have formalCoherence : formalSource =
          (argumentItemsEdit formalSites values
            (normalizationOperation targetArguments) childFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        unfold formalSource formalSites argumentItemsEdit formalItemSites
          argumentItemEdit
        exact congrArg (fun source => ItemSeq.cons (.cut source) .nil)
          mappedChildCoherence
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        formalCoherence, ?_⟩
      intro patternEq
      cases patternEq
      obtain ⟨childStaged, childHosted, childScope,
          ⟨childPresentation⟩, childEndpoint, childSourceSide⟩ :=
        childSemantic rfl
      let staged := Region.singleton (.cut childStaged)
      have liftHosted : ∀ (childBefore childAfter : Region itemCommon),
          HostedStrict childBefore childAfter →
            HostedStrict (Region.singleton (.cut childBefore))
              (Region.singleton (.cut childAfter)) := by
        intro childBefore childAfter childTransformation
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let appendNil : WireRenaming itemCommon (itemCommon ++ []) :=
          ⟨fun wire => wire.appendLeft []⟩
        let materialRename := Region.adjoinMaterialWire outer hostLocals []
        let childRename := WireRenaming.comp materialRename
          (WireRenaming.comp (rename.appendRight []) appendNil)
        let retained := hostItems.renameWires
          (Region.adjoinHostWire outer hostLocals [])
        let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
          .cut (hostLocals ++ []) retained .nil .hole
        have childRename_eq (region : Region itemCommon) :
            Region.renameWires materialRename
                (Region.renameWires (rename.appendRight [])
                  (Region.renameWires appendNil region)) =
              Region.renameWires childRename region := by
          rw [Region.renameWires_comp, Region.renameWires_comp]
          apply congrArg (fun map => Region.renameWires map region)
          apply WireRenaming.ext
          intro signature wire
          rfl
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childBefore)).renameWires rename)
        let sourceAfter := inner.fill
          (childBefore.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourceEq : sourceBefore = sourceAfter := by
          simp only [inner, retained, childRename, materialRename, appendNil,
            sourceBefore, sourceAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have sourceAfterCanonical : sourceAfter.Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let outerOccurrence : Occurrence sourceAfter source :=
          EqualityNormalization.presentationOccurrence occurrence
            sourceAfterCanonical sourceNonempty (by
              rw [← sourceEq]
              exact RegionIso.refl _)
        let childOccurrence := EqualityNormalization.Occurrence.nest
          outerOccurrence
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childAfter)).renameWires rename)
        let targetAfter := inner.fill
          (childAfter.renameWires childRename)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [inner, retained, childRename, materialRename,
            appendNil, targetBefore, targetAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have childTargetCanonical :
            (childOccurrence.context.fill
              (childAfter.renameWires childRename)).Canonical := by
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              targetReplacement.1
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (childAfter.renameWires childRename)) := by
          intro signature wire
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              targetAfterExternalTwoEnded wire
        let childOuter := outer ++ (hostLocals ++ [])
        let childEmptyEquiv := WireEquiv.appendNil childOuter
        let childAppend : WireRenaming childOuter (childOuter ++ []) :=
          childEmptyEquiv.symm.toRenaming
        let hostedChildRename := WireRenaming.comp childAppend childRename
        let emptyHostIso (region : Region itemCommon) :
            RegionIso (WireEquiv.refl childOuter)
              (region.renameWires childRename)
              (Region.adjoinAt [] .nil
                (region.renameWires hostedChildRename)) := by
          let directToCollapsed := RegionIso.renameWires region childRename
            (WireRenaming.comp childEmptyEquiv.toRenaming
              hostedChildRename)
            (WireEquiv.refl childOuter) (by
              intro signature wire
              exact (childEmptyEquiv.right_inv (childRename wire)).symm)
          let collapsedFromHosted :=
            (RegionIso.renameWiresComp region hostedChildRename
              childEmptyEquiv.toRenaming).symm
          exact (directToCollapsed.trans collapsedFromHosted).trans
            (RegionIso.adjoinAtNil
              (region.renameWires hostedChildRename))
        let sourceHosted := Region.adjoinAt [] .nil
          (childBefore.renameWires hostedChildRename)
        let sourcePresentation : RegionIso (WireEquiv.refl childOuter)
            (childBefore.renameWires childRename) sourceHosted :=
          emptyHostIso childBefore
        have sourceHostedCanonical : sourceHosted.Canonical :=
          sourcePresentation.canonical_iff.mp
            (childOccurrence.context.holeCanonical _
              childOccurrence.sourceCanonical)
        have sourceHostedNonempty : ∀ {signature}
            (wire : Var childOuter signature),
            (childBefore.renameWires childRename).incidencePaths
                wire.index.val ≠ [] ↔
              sourceHosted.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := sourcePresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        let presentedChildOccurrence : Occurrence sourceHosted source :=
          EqualityNormalization.presentationOccurrence childOccurrence
            sourceHostedCanonical sourceHostedNonempty sourcePresentation
        let targetHosted := Region.adjoinAt [] .nil
          (childAfter.renameWires hostedChildRename)
        let targetPresentation : RegionIso (WireEquiv.refl childOuter)
            (childAfter.renameWires childRename) targetHosted :=
          emptyHostIso childAfter
        have targetHostedCanonical : targetHosted.Canonical :=
          targetPresentation.canonical_iff.mp
            (childOccurrence.context.holeCanonical _ childTargetCanonical)
        have targetHostedNonempty : ∀ {signature}
            (wire : Var childOuter signature),
            (childAfter.renameWires childRename).incidencePaths
                wire.index.val ≠ [] ↔
              targetHosted.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := targetPresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        have targetHostedReplacement :=
          childOccurrence.context.replaceCanonical
            (childAfter.renameWires childRename) targetHosted
            childTargetCanonical targetHostedCanonical targetHostedNonempty
        let childTargetEndpoint := childOccurrence.interface.withBody
          (childOccurrence.context.fill
            (childAfter.renameWires childRename))
          childTargetCanonical childTargetExternalTwoEnded
        have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill targetHosted) :=
          childTargetEndpoint.externalTwoEnded_of_nonempty_iff _
            targetHostedReplacement.2
        have presentedTargetCanonical :
            (presentedChildOccurrence.context.fill targetHosted).Canonical := by
          exact targetHostedReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedChildOccurrence.interface.boundaryWire
            (presentedChildOccurrence.context.fill targetHosted) := by
          intro signature wire
          exact targetHostedExternalTwoEnded wire
        have childStrict := childTransformation childOuter [] hostedChildRename .nil
          presentedChildOccurrence presentedTargetCanonical
            presentedTargetExternalTwoEnded
        let hostedToDirect : OpenDiagramIso
            (presentedChildOccurrence.interface.withBody
              (presentedChildOccurrence.context.fill targetHosted)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (childAfter.renameWires childRename))
              childTargetCanonical childTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical
            childTargetCanonical presentedTargetExternalTwoEnded
            childTargetExternalTwoEnded
            (DiagramContext.fillIso childOccurrence.context
              targetPresentation.symm)
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          rw [← targetEq]
          exact RegionIso.refl _
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              targetReplacement.1 targetAfterExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
            targetAfterExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have directToOuter : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (childAfter.renameWires childRename))
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) := by
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        let finalIso := hostedToDirect.trans directToOuter
        exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
            finalIso,
          transGen_iso finalIso childStrict.2
            (OpenDiagramIso.refl source)⟩
      have hosted : HostedStrict
          (Region.singleton (.cut childResult)) staged := by
        simpa only [staged] using
          liftHosted childResult childStaged childHosted
      let stagedCollapse : RegionIso commonEquiv
          (childStaged.renameWires commonRename) childStaged := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires childStaged commonRename WireRenaming.id
            commonEquiv (by
              intro signature wire
              exact commonEquiv.right_inv wire)
      let resultForward : RegionIso commonEquiv.symm childFormalResult
          (childFormalResult.renameWires commonRename) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires childFormalResult WireRenaming.id
            commonRename commonEquiv.symm (by
              intro signature wire
              rfl)
      let renamedChildPresentationRaw :=
        (stagedCollapse.trans childPresentation).trans resultForward
      have renamedAmbientEq :
          ((commonEquiv.trans (WireEquiv.refl itemCommon)).trans
            commonEquiv.symm) = WireEquiv.refl (itemCommon ++ []) := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.left_inv wire
      let renamedChildPresentation :
          RegionIso (WireEquiv.refl (itemCommon ++ []))
            (childStaged.renameWires commonRename)
            (childFormalResult.renameWires commonRename) :=
        renamedChildPresentationRaw.castAmbient renamedAmbientEq
      let childIntoMapped : RegionIso (WireEquiv.refl (itemCommon ++ []))
          (childStaged.renameWires commonRename) mappedChildResult :=
        renamedChildPresentation.trans mappedChildPresentation
      let itemIntoMapped :=
        RegionIso.singletonCutCongr childIntoMapped
      let stagedIntoMapped : RegionIso commonEquiv.symm staged
          formalItemResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonRename commonEquiv.symm (by
            intro signature wire
            rfl)
        rw [Region.renameWires_id] at renamed
        let mappedStaged := Region.singleton
          (.cut (childStaged.renameWires commonRename))
        have targetEq : staged.renameWires commonRename = mappedStaged := by
          simp only [staged, mappedStaged, Region.singleton_renameWires,
            Item.renameWires]
        rw [targetEq] at renamed
        exact renamed.trans itemIntoMapped
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        stagedIntoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      refine ⟨staged, hosted, sideCut childScope,
        ⟨closed.castAmbient ambientEq⟩, ?_, ?_, retainedNil⟩
      · intro bridge alignment
        obtain ⟨childEndpointIso⟩ := childEndpoint bridge alignment
        let lifted := RegionIso.singletonCutCongr childEndpointIso
        let renamedFormalSource := formalSource.renameWires
          (bridge.sourceToTarget.appendRight [])
        let material := Region.ofItems renamedFormalSource
        let collapsedRename : WireRenaming formalSourceWires
            formalTargetWires :=
          WireRenaming.comp targetEquiv.toRenaming
            (WireRenaming.comp (bridge.sourceToTarget.appendRight [])
              sourceRename)
        have collapsedRenameEq : collapsedRename =
            bridge.sourceToTarget := by
          apply WireRenaming.ext
          intro signature wire
          simp [collapsedRename, sourceRename, sourceEquiv,
            WireRenaming.comp, WireRenaming.appendRight,
            WireEquiv.appendNil_symm_apply,
            WireEquiv.appendNil_apply]
          exact WireEquiv.appendNil_apply formalTargetWires
            (bridge.sourceToTarget wire)
        have childTransport :
            ((childFormalSource.renameWires sourceRename).renameWires
                (bridge.sourceToTarget.appendRight [])).renameWires
                  targetEquiv.toRenaming =
              childFormalSource.renameWires bridge.sourceToTarget := by
          simpa only [Region.renameWires_comp, collapsedRename] using
            congrArg (fun rename => childFormalSource.renameWires rename)
              collapsedRenameEq
        have targetEq :
            Region.singleton (.cut
                (childFormalSource.renameWires bridge.sourceToTarget)) =
              material.renameWires targetEquiv.toRenaming := by
          unfold material renamedFormalSource formalSource formalItemSource
          rw [← mappedChildSourceEq]
          simp only [ItemSeq.renameWires, Item.renameWires,
            Region.singleton, Region.ofItems, Region.renameWires]
          apply congrArg (Region.mk [])
          apply congrArg (fun item => ItemSeq.cons item .nil)
          apply congrArg Item.cut
          simp only [Region.renameWires_comp]
          apply congrArg (fun rename : WireRenaming formalSourceWires
            (formalTargetWires ++ []) =>
              childFormalSource.renameWires rename)
          apply WireRenaming.ext
          intro signature wire
          apply Var.eq_of_index_eq
          apply Fin.ext
          simp [sourceRename, sourceEquiv, targetEquiv,
            Region.singleton, Region.ofItems, Region.renameWires,
            ItemSeq.renameWires, Item.renameWires,
            Region.renameWires_comp, WireRenaming.comp,
            WireRenaming.appendRight, WireEquiv.appendNil_apply,
            WireEquiv.appendNil_symm_apply] <;> omega
        have sourceEq :
            (Region.singleton (.cut
              (regionEdit itemData childEvidence childSites).endpoint)).renameWires
                alignment.ambient.toRenaming =
              Region.singleton (.cut
                ((regionEdit itemData childEvidence childSites).endpoint.renameWires
                  alignment.ambient.toRenaming)) := by
          simp [Region.singleton_renameWires, Item.renameWires,
            WireRenaming.appendRight]
        refine ⟨?_⟩
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          WireEquiv.trans_refl] using
          (((RegionIso.ofEq sourceEq).trans lifted).trans
            (RegionIso.ofEq targetEq)).trans
            ((RegionIso.adjoinAtNil material).trans
              (RegionIso.adjoinAtOfItems [] renamedFormalSource))
      · let childSource :=
          (argumentRegionEdit childFormalSites sourceValues
            (normalizationOperation patternWires) argumentFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1
        let mappedSource :=
          (argumentRegionEdit mappedChildSites sourceValues
            (normalizationOperation patternWires) mappedArgumentFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1
        let sourceMaterial := Region.singleton (.cut childSource)
        let targetMaterial := Region.singleton (.cut mappedSource)
        have mappedEq : sourceMaterial.renameWires argumentSourceRename =
            targetMaterial := by
          simp only [sourceMaterial, targetMaterial,
            Region.singleton_renameWires, Item.renameWires]
          rw [mappedChildSourceArgumentEq]
        let presentation :=
          (RegionIso.adjoinAtNilRenamed sourceMaterial).trans
            (RegionIso.adjoinAt [] .nil (RegionIso.ofEq mappedEq))
        have moved := sourceSideIso (RegionIso.refl _) presentation
          (sourceSideCut childSourceSide)
        simpa [formalSites, formalItemSites, formalSource,
          formalItemSource, argumentItemsEdit, argumentItemEdit,
          childSource, mappedSource, targetMaterial] using moved
  obtain ⟨retained, formalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, semantic⟩ :=
    foldedFamilyWithPattern
  refine ⟨retained, formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, ?_⟩
  exact semantic rfl

/-- Accumulate the hosted transformation and literal target through one
authoritative traversal; callers provide endpoint validity when applying it. -/
theorem accumulateHostedTarget
    {targetArguments patternWires outer before after targetInserted
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires
      (outer ++ (before ++ after)) originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars pattern.external targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted
        targetArguments))
    (targetNaturality : DataNaturality targetBaseOperation)
    (selectedCase : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemOperation : Transform.Operation patternWires}
      {itemData : itemOperation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : itemOperation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := itemOperation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)))) :
    TargetItems
      (targetPattern := targetPattern)
      (targetOperation := targetBaseOperation)
      evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted
        targetArguments) targetData
      (fun retained _formalSource formalResult _formalEvidence _formalSites
          _coherence =>
        ∃ staged : Region (outer ++ (before ++ after)),
          HostedStrict result staged ∧
            Nonempty (RegionIso
              (WireEquiv.refl (outer ++ (before ++ after))) staged
              (Region.adjoinAt retained .nil formalResult))) := by
  have selectedWithUnit : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemOperation : Transform.Operation patternWires}
      {itemData : itemOperation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : itemOperation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := itemOperation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              True ∧
                Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                  (Region.adjoinAt retained .nil formalResult)) ∧
                  (∀ (bridge : TargetFrameBridge selectedTargetFrame
                        (fun _ _ => False) selectedTargetData)
                    (alignment : TargetAmbientBridge itemFrame
                      selectedTargetFrame (fun _ _ _ => True)
                      itemData selectedTargetData),
                    Nonempty (RegionIso
                      (WireEquiv.refl selectedTargetWires)
                      ((itemEdit itemData
                        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                          (pattern := pattern) (retain := itemFrame.sourceKeep)
                          (selected := itemFrame.selected) application)
                        (ItemSites.selectedAtom (operation := itemOperation)
                          (pattern := pattern) (frame := itemFrame)
                          application siteData)).endpoint.renameWires
                          alignment.ambient.toRenaming)
                      (.mk retained (formalSource.renameWires
                        (bridge.sourceToTarget.appendRight retained))))) ∧
                  True ∧ True) := by
    intro itemCommon itemSourceWires itemTargetWires itemFrame itemOperation
      itemData application siteData selectedTargetSourceWires
      selectedTargetWires selectedTargetFrame selectedTargetData
    obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
        coherence, staged, hosted, presentation⟩ :=
      selectedCase application siteData selectedTargetFrame selectedTargetData
    exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      coherence, staged, hosted, True.intro, presentation, by
        intro bridge _alignment
        exact False.elim bridge.data_selects, True.intro, True.intro⟩
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      coherence, staged, hosted, _unit, presentation, _endpoint,
      _sourceSide, _retained⟩ :=
    accumulateHostedTargetWith evidence sites targetValues targetData
      pattern.boundaryWire
      (fun {_} _ _ => True)
      (fun _ => True.intro)
      (fun _ _ _ _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ => True.intro)
      (fun {_} _ _ => True)
      (fun _ => True.intro)
      (fun _ _ _ _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ => True.intro)
      (fun _ _ _ => True.intro)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      targetNaturality (fun _ => True) True.intro
      (fun _ _ _ _ => True.intro) selectedWithUnit
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    coherence, staged, hosted, presentation⟩


end VisualProof.Rule.Completeness.Comprehension
