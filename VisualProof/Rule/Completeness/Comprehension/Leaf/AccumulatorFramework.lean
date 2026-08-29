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

end VisualProof.Rule.Completeness.Comprehension
