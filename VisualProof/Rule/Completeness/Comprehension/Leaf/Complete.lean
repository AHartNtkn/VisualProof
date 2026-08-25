import VisualProof.Rule.Completeness.Comprehension.Leaf.Accumulator
import VisualProof.Rule.Completeness.Comprehension.Leaf.IdentitySupport
import VisualProof.Rule.Completeness.Comprehension.Normalization.ArgumentsAt
import VisualProof.Rule.Completeness.Comprehension.Normalization.Sites
namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- Accumulate every selected application in one authoritative item sequence
into the literal positional-Formal edit at an arbitrary binder placement. -/
theorem accumulateAtomFormalAt
    {patternWires atomArguments common outer localBefore localAfter
      originalSourceWires originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (placement_eq : common = outer ++ (localBefore ++ localAfter))
    {originalFrame : Transform.Frame patternWires
      common originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (outer ++ (localBefore ++
            .rel (positionalAtomWires atomArguments) ::
              (localAfter ++ retained))),
        ∃ formalResult : Region
            (outer ++ (localBefore ++ (localAfter ++ retained))),
          ∃ formalEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalAtomPattern atomArguments)
                (Leaf.Formal.rootFrame
                  outer localBefore (localAfter ++ retained) [] atomArguments).sourceKeep
                (Leaf.Formal.rootFrame
                  outer localBefore (localAfter ++ retained) [] atomArguments).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation (Leaf.Formal.operation [] atomArguments)
                  pattern.external) PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (positionalAtomSelection head ports)
                    (normalizationOperation (positionalAtomWires atomArguments))
                    (Leaf.Formal.rootFrame
                      outer localBefore (localAfter ++ retained) [] atomArguments)
                    PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1,
                let output := itemsEdit
                  (operation := recordingOperation
                    (Leaf.Formal.operation [] atomArguments) pattern.external)
                  PUnit.unit formalEvidence formalSites
                let outputWiresEq :
                    (common ++ retained) =
                      (outer ++ (localBefore ++
                        (localAfter ++ retained))) := by
                  rw [placement_eq]
                  simp only [List.append_assoc]
                let outputAtCommon : Region
                    (common ++ retained) :=
                  output.endpoint.renameWires
                    (WireEquiv.ofEq outputWiresEq).symm.toRenaming
                HostedStrict result
                    (Region.adjoinAt retained .nil outputAtCommon) ∧
                  ScopePreservation result
                    (Region.adjoinAt retained .nil outputAtCommon) := by
  subst common
  let common := outer ++ (localBefore ++ localAfter)
  let initialFrame : Transform.Frame (positionalAtomWires atomArguments)
      common
      (outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) :: localAfter))
      common :=
    Transform.Frame.replace outer localBefore localAfter []
      (positionalAtomWires atomArguments)
  have folded :=
    accumulateHostedTargetWith evidence sites
      (positionalAtomSelection head ports)
      (outer := outer) (before := localBefore) (after := localAfter)
      (targetInserted := [])
      (targetPattern := positionalAtomPattern atomArguments)
      (targetBaseOperation := Leaf.Formal.operation [] atomArguments)
      PUnit.unit pattern.boundaryWire ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun _ _ => True) (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (formalDataNaturality atomArguments)
      (fun _ => True) True.intro (by intros; trivial)
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        cases selectedData
        obtain ⟨retained, formalSource, formalResult, formalEvidence,
            formalSites, coherence, staged, hosted, scope, presentation⟩ :=
          atomSelectedTargetItem body_eq application siteData selectedFrame
        exact ⟨retained, formalSource, formalResult, formalEvidence,
          formalSites, coherence, staged, hosted, scope, presentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects, True.intro, True.intro⟩)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩, _rawEndpoint, _rawSourceSide, _rawRetained⟩ := folded
  let canonicalFrame := Leaf.Formal.rootFrame outer localBefore
    (localAfter ++ retained) [] atomArguments
  have sourceWiresEq :
      ((outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) :: localAfter)) ++ retained) =
      (outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) ::
          (localAfter ++ retained))) := by
    simp only [List.append_assoc, List.cons_append]
  let sourceEquiv : WireEquiv
      ((outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) :: localAfter)) ++ retained)
      (outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) ::
          (localAfter ++ retained))) :=
    WireEquiv.ofEq sourceWiresEq
  have commonWiresEq :
      (common ++ retained) =
      (outer ++ (localBefore ++ (localAfter ++ retained))) := by
    simp only [common, List.append_assoc]
  let commonEquiv : WireEquiv
      (common ++ retained)
      (outer ++ (localBefore ++ (localAfter ++ retained))) :=
    WireEquiv.ofEq commonWiresEq
  let sourceRename := sourceEquiv.toRenaming
  let commonRename := commonEquiv.toRenaming
  have sourceRename_index {signature}
      (wire : Var
        ((outer ++ (localBefore ++
          .rel (positionalAtomWires atomArguments) :: localAfter)) ++ retained)
        signature) :
      (sourceRename wire).index.val = wire.index.val := by
    exact WireEquiv.ofEq_index_val sourceWiresEq wire
  have commonRename_index {signature}
      (wire : Var (common ++ retained) signature) :
      (commonRename wire).index.val = wire.index.val := by
    exact WireEquiv.ofEq_index_val commonWiresEq wire
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    refine Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire)) ?_ ?_ wire
    · intro inheritedSignature inherited
      refine Var.appendCases (left := outer)
        (right := localBefore ++ localAfter)
        (motive := fun inherited =>
          sourceRename ((initialFrame.append retained).sourceKeep
              (inherited.appendLeft retained)) =
            canonicalFrame.sourceKeep
              (commonRename (inherited.appendLeft retained))) ?_ ?_ inherited
      · intro outerSignature outerWire
        have commonStep : commonRename
            ((outerWire.appendLeft (localBefore ++ localAfter)).appendLeft
              retained) =
            outerWire.appendLeft
              (localBefore ++ (localAfter ++ retained)) := by
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [commonRename_index]
          simp
        rw [commonStep]
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [sourceRename_index]
        simp [initialFrame, canonicalFrame, positionalAtomWires,
          Leaf.Formal.rootFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight]
      · intro localSignature localWire
        refine Var.appendCases (left := localBefore) (right := localAfter)
          (motive := fun localWire =>
            sourceRename ((initialFrame.append retained).sourceKeep
                ((Var.appendRight outer localWire).appendLeft retained)) =
              canonicalFrame.sourceKeep (commonRename
                ((Var.appendRight outer localWire).appendLeft retained)))
          ?_ ?_ localWire
        · intro beforeSignature beforeWire
          have commonStep : commonRename
              ((Var.appendRight outer
                (beforeWire.appendLeft localAfter)).appendLeft retained) =
              Var.appendRight outer
                (beforeWire.appendLeft (localAfter ++ retained)) := by
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [commonRename_index]
            simp
          rw [commonStep]
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [sourceRename_index]
          simp [initialFrame, canonicalFrame, positionalAtomWires,
            Leaf.Formal.rootFrame, Transform.Frame.replace,
            Transform.Frame.append, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.appendRight]
        · intro afterSignature afterWire
          have commonStep : commonRename
              ((Var.appendRight outer
                (Var.appendRight localBefore afterWire)).appendLeft retained) =
              Var.appendRight outer
                (Var.appendRight localBefore
                  (afterWire.appendLeft retained)) := by
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [commonRename_index]
            simp
          rw [commonStep]
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [sourceRename_index]
          simp [initialFrame, canonicalFrame, positionalAtomWires,
            Leaf.Formal.rootFrame, Transform.Frame.replace,
            Transform.Frame.append, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.appendRight,
            Var.appendRight, Var.index]
    · intro retainedSignature retainedWire
      have commonStep : commonRename
          (Var.appendRight common retainedWire) =
          Var.appendRight outer
            (Var.appendRight localBefore
              (Var.appendRight localAfter retainedWire)) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [commonRename_index]
        simp [common]
        omega
      rw [commonStep]
      apply Var.eq_of_index_eq
      apply Fin.ext
      rw [sourceRename_index]
      simp [initialFrame, canonicalFrame, positionalAtomWires,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        Var.appendRight, Var.index]
      omega
  have initialTargetKeepIdentity :
      (initialFrame.append retained).targetKeep = WireRenaming.id := by
    have baseTargetKeepIdentity :
        initialFrame.targetKeep = WireRenaming.id := by
      apply WireRenaming.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer)
        (right := localBefore ++ localAfter)
        (motive := fun wire => initialFrame.targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id]
      · intro localSignature localWire
        apply Var.appendCases (left := localBefore) (right := localAfter)
          (motive := fun localWire =>
            initialFrame.targetKeep (Var.appendRight outer localWire) =
              Var.appendRight outer localWire)
        · intro beforeSignature beforeWire
          simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.id]
        · intro afterSignature afterWire
          simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.id, Var.appendRight]
    apply WireRenaming.ext
    intro wireSignature wire
    change initialFrame.targetKeep.appendRight retained wire = wire
    rw [baseTargetKeepIdentity]
    exact WireRenaming.appendRight_id_apply retained wire
  have canonicalTargetKeepIdentity :
      canonicalFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro wireSignature wire
    apply Var.appendCases (left := outer)
      (right := localBefore ++ (localAfter ++ retained))
      (motive := fun wire => canonicalFrame.targetKeep wire = wire)
    · intro inheritedSignature inherited
      simp [canonicalFrame, Leaf.Formal.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := localBefore)
        (right := localAfter ++ retained)
        (motive := fun localWire =>
          canonicalFrame.targetKeep (Var.appendRight outer localWire) =
            Var.appendRight outer localWire)
      · intro beforeSignature beforeWire
        simp [canonicalFrame, Leaf.Formal.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp [canonicalFrame, Leaf.Formal.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id, Var.appendRight]
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    rw [initialTargetKeepIdentity, canonicalTargetKeepIdentity]
    rfl
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [sourceRename_index]
    simp [initialFrame, canonicalFrame, positionalAtomWires,
      Leaf.Formal.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead, Var.index]
  let argumentFrame : Transform.Frame (positionalAtomWires atomArguments)
      (common ++ retained)
      ((outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) :: localAfter)) ++ retained)
      ((outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) :: localAfter)) ++ retained) := {
    sourceKeep := (initialFrame.append retained).sourceKeep
    targetKeep := (initialFrame.append retained).sourceKeep
    selected := (initialFrame.append retained).selected
  }
  let mappedArgumentFrame : Transform.Frame
      (positionalAtomWires atomArguments)
      (outer ++ (localBefore ++ (localAfter ++ retained)))
      (outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) ::
          (localAfter ++ retained)))
      (outer ++ (localBefore ++
        .rel (positionalAtomWires atomArguments) ::
          (localAfter ++ retained))) := {
    sourceKeep := canonicalFrame.sourceKeep
    targetKeep := canonicalFrame.sourceKeep
    selected := canonicalFrame.selected
  }
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, _formalArgumentDuplicate,
      ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (positionalAtomSelection head ports)
      (positionalAtomSelection head ports)
      argumentFrame mappedArgumentFrame
      commonRename sourceRename commonRename sourceRename
      keepCommutes targetKeepCommutes selectedCommutes
      keepCommutes selectedCommutes
      (formalDataNaturality atomArguments) True.intro
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (positionalAtomSelection head ports)
        (normalizationOperation (positionalAtomWires atomArguments))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (positionalAtomSelection head ports)
            (normalizationOperation (positionalAtomWires atomArguments))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let rawOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit rawFormalEvidence rawFormalSites
  obtain ⟨rawLeafHosted, rawLeafScope⟩ :=
    leafItemsEndpoint rawFormalEvidence rawFormalSites
      initialTargetKeepIdentity
      (fun {siteCommon siteSourceWires} {siteFrame} {siteData}
          siteTargetKeepEq application site => by
        have endpoint := positionalAtomLeafEndpoint atomArguments
          siteTargetKeepEq application site
        exact ⟨endpoint.1, endpoint.2.1⟩)
  have rawLeafReverse : HostedScope rawOutput.endpoint rawFormalResult := by
    intro target rename
    exact leafItemsReverseHostedScope rawFormalEvidence rawFormalSites
      initialTargetKeepIdentity
      (fun {siteCommon siteSourceWires} {siteFrame} {siteData}
          siteTargetKeepEq application site => by
        intro siteTarget siteRename
        exact (positionalAtomLeafEndpoint atomArguments
          siteTargetKeepEq application site).2.2 siteRename)
      rename
  let rawFormalRoot := Region.adjoinAt retained .nil rawFormalResult
  let rawOutputRoot := Region.adjoinAt retained .nil rawOutput.endpoint
  have liftedRawLeafHosted : HostedStrict rawFormalRoot rawOutputRoot := by
    simpa only [rawFormalRoot, rawOutputRoot] using
      HostedStrict.adjoinAt retained rawFormalResult rawOutput.endpoint
        rawLeafHosted
  have liftedRawLeafScope :
      ScopePreservation rawFormalRoot rawOutputRoot := by
    simpa only [rawFormalRoot, rawOutputRoot] using
      adjoinAt_preserves_scope retained .nil rawFormalResult
        rawOutput.endpoint rawLeafScope
  have liftedRawLeafReverse : HostedScope rawOutputRoot rawFormalRoot := by
    intro target rename
    exact HostedScope.adjoinAt retained rawOutput.endpoint rawFormalResult
      (fun childRename => rawLeafReverse childRename) rename
  have stagedToFormal : HostedStrict rawStaged rawFormalRoot := by
    simpa only [rawFormalRoot] using HostedStrict.ofIso rawPresentation
  have stagedReverse : HostedScope rawFormalRoot rawStaged := by
    intro target rename
    simpa only [rawFormalRoot] using
      HostedScope.ofIso rawPresentation.symm rename
  have resultToFormal : HostedStrict result rawFormalRoot := by
    exact HostedStrict.trans rawHosted stagedToFormal
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost
          (fun scopeRename => stagedReverse scopeRename)
          outer hostLocals rename hostItems)
  have resultToRawOutput : HostedStrict result rawOutputRoot := by
    exact HostedStrict.trans resultToFormal liftedRawLeafHosted
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost
          (fun scopeRename => liftedRawLeafReverse scopeRename)
          outer hostLocals rename hostItems)
  have resultToRawOutputScope :
      ScopePreservation result rawOutputRoot := by
    exact rawScope.trans
      ((ScopePreservation.ofIso rawPresentation).trans
        liftedRawLeafScope)
  let output := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let outputWiresEq :
      ((outer ++ (localBefore ++ localAfter)) ++ retained) =
        (outer ++ (localBefore ++ (localAfter ++ retained))) := by
    simp only [List.append_assoc]
  let outputAtCommon : Region
      ((outer ++ (localBefore ++ localAfter)) ++ retained) :=
    output.endpoint.renameWires
      (WireEquiv.ofEq outputWiresEq).symm.toRenaming
  let rawForward : RegionIso commonEquiv rawOutput.endpoint
      (rawOutput.endpoint.renameWires commonRename) := by
    simpa only [Region.renameWires_id] using
      RegionIso.renameWires rawOutput.endpoint WireRenaming.id commonRename
        commonEquiv (fun _ => rfl)
  let outputBack : RegionIso commonEquiv.symm output.endpoint
      outputAtCommon := by
    simpa only [outputAtCommon, outputWiresEq, commonEquiv,
      Region.renameWires_id] using
      RegionIso.renameWires output.endpoint WireRenaming.id
        commonEquiv.symm.toRenaming commonEquiv.symm (fun _ => rfl)
  let combined :=
    (rawForward.trans formalEndpointPresentation).trans outputBack
  have ambientEq :
      ((commonEquiv.trans (WireEquiv.refl
        (outer ++ (localBefore ++ (localAfter ++ retained))))).trans
          commonEquiv.symm) =
        WireEquiv.refl (common ++ retained) := by
    apply WireEquiv.ext
    intro signature wire
    exact commonEquiv.left_inv wire
  let outputPresentation : RegionIso (WireEquiv.refl (common ++ retained))
      rawOutput.endpoint outputAtCommon :=
    combined.castAmbient ambientEq
  let rootPresentation : RegionIso (WireEquiv.refl common)
      rawOutputRoot (Region.adjoinAt retained .nil outputAtCommon) := by
    simpa only [rawOutputRoot] using
      RegionIso.adjoinAt retained .nil outputPresentation
  have finalHosted : HostedStrict result
      (Region.adjoinAt retained .nil outputAtCommon) :=
    HostedStrict.iso (RegionIso.refl result) rootPresentation
      resultToRawOutput
  have finalScope : ScopePreservation result
      (Region.adjoinAt retained .nil outputAtCommon) :=
    resultToRawOutputScope.trans (ScopePreservation.ofIso rootPresentation)
  refine ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, ?_⟩
  simpa only [outputAtCommon, outputWiresEq, common] using
    And.intro finalHosted finalScope
/-- Accumulate every selected application in one authoritative item sequence
into the single literal positional-Formal edit consumed at the binder home. -/
theorem accumulateAtomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (positionalAtomWires atomArguments) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalAtomPattern atomArguments)
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).sourceKeep
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation (Leaf.Formal.operation [] atomArguments)
                  pattern.external) PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (positionalAtomSelection head ports)
                    (normalizationOperation (positionalAtomWires atomArguments))
                    (Leaf.Formal.rootFrame common [] retained []
                      atomArguments) PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1,
                let output := itemsEdit
                  (operation := recordingOperation
                    (Leaf.Formal.operation [] atomArguments) pattern.external)
                  PUnit.unit formalEvidence formalSites
                ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  refine Exists.elim
    (accumulateAtomFormalAt
      (outer := common) (localBefore := []) (localAfter := []) body_eq
      (by simp) evidence sites) ?_
  intro retained folded
  rcases folded with ⟨formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, coreHosted, coreScope⟩
  let output := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  let coreOutputWiresEq :
      (common ++ retained) = common ++ ([] ++ ([] ++ retained)) := by
    simp only [List.nil_append]
  let coreOutput := output.endpoint.renameWires
    (WireEquiv.ofEq coreOutputWiresEq).symm.toRenaming
  let coreExactOutput := Region.adjoinAt retained .nil coreOutput
  have coreScope' : ScopePreservation result coreExactOutput := by
    simpa only [coreExactOutput, coreOutput, output] using coreScope
  have coreHosted' : HostedStrict result coreExactOutput := by
    simpa only [coreExactOutput, coreOutput, output] using coreHosted
  have coreEquivEq : (WireEquiv.ofEq coreOutputWiresEq).symm =
      WireEquiv.refl (common ++ retained) := by
    apply WireEquiv.ext
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    exact WireEquiv.ofEq_index_val coreOutputWiresEq
      ((WireEquiv.ofEq coreOutputWiresEq).symm wire)
  have coreOutputEq : coreOutput = output.endpoint := by
    change output.endpoint.renameWires
      (WireEquiv.ofEq coreOutputWiresEq).symm.toRenaming = output.endpoint
    rw [coreEquivEq]
    exact Region.renameWires_id output.endpoint
  let outputPresentation : RegionIso (WireEquiv.refl common)
      coreExactOutput exactOutput :=
    RegionIso.adjoinAt retained .nil (RegionIso.ofEq coreOutputEq)
  have outputScope : ScopePreservation result exactOutput :=
    coreScope'.trans (ScopePreservation.ofIso outputPresentation)
  have outputHosted : HostedStrict result exactOutput :=
    HostedStrict.iso (RegionIso.refl result) outputPresentation coreHosted'
  have materialOutputCanonical : exactOutput.Canonical :=
    outputScope.canonical
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have outputReplacement := occurrence.context.replaceCanonical result
    exactOutput occurrence.sourceCanonical materialOutputCanonical
      outputScope.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill result) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have outputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill exactOutput) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ outputReplacement.2
  have strict := HostedStrict.atOccurrence outputHosted occurrence
    outputReplacement.1 outputExternalTwoEnded
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, outputReplacement.1, outputExternalTwoEnded, strict⟩

theorem accumulateIdentityAt
    {patternWires common outer localBefore localAfter
      originalSourceWires originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    (placement_eq : common = outer ++ (localBefore ++ localAfter))
    {originalFrame : Transform.Frame patternWires
      common originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (outer ++ (localBefore ++
            .rel (List.replicate arity signature) ::
              (localAfter ++ retained))),
        ∃ formalResult : Region
            (outer ++ (localBefore ++ (localAfter ++ retained))),
          ∃ formalEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalIdentityPattern signature arity)
                (Leaf.Identity.rootFrame
                  outer localBefore (localAfter ++ retained) signature arity).sourceKeep
                (Leaf.Identity.rootFrame
                  outer localBefore (localAfter ++ retained) signature arity).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation (Leaf.Identity.operation signature arity)
                  pattern.external) PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (Leaf.Identity.Vars.fromFn ports)
                    (normalizationOperation (List.replicate arity signature))
                    (Leaf.Identity.rootFrame
                      outer localBefore (localAfter ++ retained) signature arity)
                    PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1,
                let output := itemsEdit
                  (operation := recordingOperation
                    (Leaf.Identity.operation signature arity) pattern.external)
                  PUnit.unit formalEvidence formalSites
                let outputWiresEq :
                    (common ++ retained) =
                      (outer ++ (localBefore ++
                        (localAfter ++ retained))) := by
                  rw [placement_eq]
                  simp only [List.append_assoc]
                let outputAtCommon : Region
                    (common ++ retained) :=
                  output.endpoint.renameWires
                    (WireEquiv.ofEq outputWiresEq).symm.toRenaming
                HostedStrict result
                    (Region.adjoinAt retained .nil outputAtCommon) ∧
                  ScopePreservation result
                    (Region.adjoinAt retained .nil outputAtCommon) := by
  subst common
  let common := outer ++ (localBefore ++ localAfter)
  let initialFrame : Transform.Frame (List.replicate arity signature)
      common
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter))
      common :=
    Transform.Frame.replace outer localBefore localAfter []
      (List.replicate arity signature)
  have folded :=
    accumulateHostedTargetWith evidence sites
      (Leaf.Identity.Vars.fromFn ports)
      (outer := outer) (before := localBefore) (after := localAfter)
      (targetInserted := [])
      (targetPattern := positionalIdentityPattern signature arity)
      (targetBaseOperation := Leaf.Identity.operation signature arity)
      PUnit.unit pattern.boundaryWire ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun _ _ => True) (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (identityDataNaturality signature arity)
      (fun _ => True) True.intro (by intros; trivial)
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        obtain ⟨retained, formalSource, formalResult, formalEvidence,
            formalSites, coherence, staged, hosted, scope, presentation⟩ :=
          identitySelectedTargetItem body_eq application siteData selectedFrame
        exact ⟨retained, formalSource, formalResult, formalEvidence,
          formalSites, coherence, staged, hosted, scope, presentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects, True.intro, True.intro⟩)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩, _rawEndpoint, _rawSourceSide, _rawRetained⟩ := folded
  let canonicalFrame := Leaf.Identity.rootFrame outer localBefore
    (localAfter ++ retained) signature arity
  have sourceWiresEq :
      ((outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter)) ++ retained) =
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) ::
          (localAfter ++ retained))) := by
    simp only [List.append_assoc, List.cons_append]
  let sourceEquiv : WireEquiv
      ((outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter)) ++ retained)
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) ::
          (localAfter ++ retained))) :=
    WireEquiv.ofEq sourceWiresEq
  have commonWiresEq :
      (common ++ retained) =
      (outer ++ (localBefore ++ (localAfter ++ retained))) := by
    simp only [common, List.append_assoc]
  let commonEquiv : WireEquiv
      (common ++ retained)
      (outer ++ (localBefore ++ (localAfter ++ retained))) :=
    WireEquiv.ofEq commonWiresEq
  let sourceRename := sourceEquiv.toRenaming
  let commonRename := commonEquiv.toRenaming
  have sourceRename_index {wireSignature}
      (wire : Var
        ((outer ++ (localBefore ++
          .rel (List.replicate arity signature) :: localAfter)) ++ retained)
        wireSignature) :
      (sourceRename wire).index.val = wire.index.val := by
    exact WireEquiv.ofEq_index_val sourceWiresEq wire
  have commonRename_index {wireSignature}
      (wire : Var (common ++ retained) wireSignature) :
      (commonRename wire).index.val = wire.index.val := by
    exact WireEquiv.ofEq_index_val commonWiresEq wire
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    refine Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire)) ?_ ?_ wire
    · intro inheritedSignature inherited
      refine Var.appendCases (left := outer)
        (right := localBefore ++ localAfter)
        (motive := fun inherited =>
          sourceRename ((initialFrame.append retained).sourceKeep
              (inherited.appendLeft retained)) =
            canonicalFrame.sourceKeep
              (commonRename (inherited.appendLeft retained))) ?_ ?_ inherited
      · intro outerSignature outerWire
        have commonStep : commonRename
            ((outerWire.appendLeft (localBefore ++ localAfter)).appendLeft
              retained) =
            outerWire.appendLeft
              (localBefore ++ (localAfter ++ retained)) := by
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [commonRename_index]
          simp
        rw [commonStep]
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [sourceRename_index]
        simp [initialFrame, canonicalFrame,
          Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight]
      · intro localSignature localWire
        refine Var.appendCases (left := localBefore) (right := localAfter)
          (motive := fun localWire =>
            sourceRename ((initialFrame.append retained).sourceKeep
                ((Var.appendRight outer localWire).appendLeft retained)) =
              canonicalFrame.sourceKeep (commonRename
                ((Var.appendRight outer localWire).appendLeft retained)))
          ?_ ?_ localWire
        · intro beforeSignature beforeWire
          have commonStep : commonRename
              ((Var.appendRight outer
                (beforeWire.appendLeft localAfter)).appendLeft retained) =
              Var.appendRight outer
                (beforeWire.appendLeft (localAfter ++ retained)) := by
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [commonRename_index]
            simp
          rw [commonStep]
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [sourceRename_index]
          simp [initialFrame, canonicalFrame,
            Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.append, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.appendRight]
        · intro afterSignature afterWire
          have commonStep : commonRename
              ((Var.appendRight outer
                (Var.appendRight localBefore afterWire)).appendLeft retained) =
              Var.appendRight outer
                (Var.appendRight localBefore
                  (afterWire.appendLeft retained)) := by
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [commonRename_index]
            simp
          rw [commonStep]
          apply Var.eq_of_index_eq
          apply Fin.ext
          rw [sourceRename_index]
          simp [initialFrame, canonicalFrame,
            Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.append, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.appendRight,
            Var.appendRight, Var.index]
    · intro retainedSignature retainedWire
      have commonStep : commonRename
          (Var.appendRight common retainedWire) =
          Var.appendRight outer
            (Var.appendRight localBefore
              (Var.appendRight localAfter retainedWire)) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [commonRename_index]
        simp [common]
        omega
      rw [commonStep]
      apply Var.eq_of_index_eq
      apply Fin.ext
      rw [sourceRename_index]
      simp [initialFrame, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        Var.appendRight, Var.index]
      omega
  have initialTargetKeepIdentity :
      (initialFrame.append retained).targetKeep = WireRenaming.id := by
    have baseTargetKeepIdentity :
        initialFrame.targetKeep = WireRenaming.id := by
      apply WireRenaming.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer)
        (right := localBefore ++ localAfter)
        (motive := fun wire => initialFrame.targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id]
      · intro localSignature localWire
        apply Var.appendCases (left := localBefore) (right := localAfter)
          (motive := fun localWire =>
            initialFrame.targetKeep (Var.appendRight outer localWire) =
              Var.appendRight outer localWire)
        · intro beforeSignature beforeWire
          simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.id]
        · intro afterSignature afterWire
          simp [initialFrame, Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, WireRenaming.id, Var.appendRight]
    apply WireRenaming.ext
    intro wireSignature wire
    change initialFrame.targetKeep.appendRight retained wire = wire
    rw [baseTargetKeepIdentity]
    exact WireRenaming.appendRight_id_apply retained wire
  have canonicalTargetKeepIdentity :
      canonicalFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro wireSignature wire
    apply Var.appendCases (left := outer)
      (right := localBefore ++ (localAfter ++ retained))
      (motive := fun wire => canonicalFrame.targetKeep wire = wire)
    · intro inheritedSignature inherited
      simp [canonicalFrame, Leaf.Identity.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := localBefore)
        (right := localAfter ++ retained)
        (motive := fun localWire =>
          canonicalFrame.targetKeep (Var.appendRight outer localWire) =
            Var.appendRight outer localWire)
      · intro beforeSignature beforeWire
        simp [canonicalFrame, Leaf.Identity.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp [canonicalFrame, Leaf.Identity.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.id, Var.appendRight]
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    rw [initialTargetKeepIdentity, canonicalTargetKeepIdentity]
    rfl
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [sourceRename_index]
    simp [initialFrame, canonicalFrame,
      Leaf.Identity.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead, Var.index]
  let argumentFrame : Transform.Frame (List.replicate arity signature)
      (common ++ retained)
      ((outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter)) ++ retained)
      ((outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter)) ++ retained) := {
    sourceKeep := (initialFrame.append retained).sourceKeep
    targetKeep := (initialFrame.append retained).sourceKeep
    selected := (initialFrame.append retained).selected
  }
  let mappedArgumentFrame : Transform.Frame
      (List.replicate arity signature)
      (outer ++ (localBefore ++ (localAfter ++ retained)))
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) ::
          (localAfter ++ retained)))
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) ::
          (localAfter ++ retained))) := {
    sourceKeep := canonicalFrame.sourceKeep
    targetKeep := canonicalFrame.sourceKeep
    selected := canonicalFrame.selected
  }
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, _formalArgumentDuplicate,
      ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (Leaf.Identity.Vars.fromFn ports)
      (Leaf.Identity.Vars.fromFn ports)
      argumentFrame mappedArgumentFrame
      commonRename sourceRename commonRename sourceRename
      keepCommutes targetKeepCommutes selectedCommutes
      keepCommutes selectedCommutes
      (identityDataNaturality signature arity) True.intro
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (Leaf.Identity.Vars.fromFn ports)
        (normalizationOperation (List.replicate arity signature))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (Leaf.Identity.Vars.fromFn ports)
            (normalizationOperation (List.replicate arity signature))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let rawOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) pattern.external)
    PUnit.unit rawFormalEvidence rawFormalSites
  obtain ⟨rawLeafHosted, rawLeafScope⟩ :=
    leafItemsEndpoint rawFormalEvidence rawFormalSites
      initialTargetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalIdentityLeafEndpoint signature arity
          siteTargetKeepEq application site)
  have rawLeafReverse : HostedScope rawOutput.endpoint rawFormalResult := by
    intro target rename
    exact leafItemsReverseHostedScope rawFormalEvidence rawFormalSites
      initialTargetKeepIdentity
      (fun {siteCommon siteSourceWires} {siteFrame} {siteData}
          siteTargetKeepEq application site => by
        intro siteTarget siteRename
        rcases site with ⟨⟨identityPorts, applicationEq⟩,
          recordedApplication⟩
        subst application
        have targetEq :
            (recordingOperation
              (Leaf.Identity.operation signature arity) pattern.external).site
                siteFrame siteData (Leaf.Identity.Vars.fromFn identityPorts)
                ⟨⟨identityPorts, rfl⟩, recordedApplication⟩ =
              positionalIdentityApplication signature arity
                (Leaf.Identity.Vars.fromFn identityPorts) := by
          change Region.singleton (.identity signature arity
              (fun position => siteFrame.targetKeep
                (identityPorts position))) = _
          rw [siteTargetKeepEq]
          simp [positionalIdentityApplication, WireRenaming.id,
            Leaf.Identity.Vars.toFn_fromFn]
        rw [targetEq]
        simpa [positionalIdentityApplication,
          EqualityNormalization.instantiate_renameWires,
          Region.singleton_renameWires, Item.renameWires,
          Leaf.Identity.Vars.fromFn_map,
          Leaf.Identity.Vars.toFn_map,
          Leaf.Identity.Vars.toFn_fromFn] using
          positionalIdentityApplication_scope signature arity
            ((Leaf.Identity.Vars.fromFn identityPorts).map
              fun wire => siteRename wire))
      rename
  let rawFormalRoot := Region.adjoinAt retained .nil rawFormalResult
  let rawOutputRoot := Region.adjoinAt retained .nil rawOutput.endpoint
  have liftedRawLeafHosted : HostedStrict rawFormalRoot rawOutputRoot := by
    simpa only [rawFormalRoot, rawOutputRoot] using
      HostedStrict.adjoinAt retained rawFormalResult rawOutput.endpoint
        rawLeafHosted
  have liftedRawLeafScope :
      ScopePreservation rawFormalRoot rawOutputRoot := by
    simpa only [rawFormalRoot, rawOutputRoot] using
      adjoinAt_preserves_scope retained .nil rawFormalResult
        rawOutput.endpoint rawLeafScope
  have liftedRawLeafReverse : HostedScope rawOutputRoot rawFormalRoot := by
    intro target rename
    exact HostedScope.adjoinAt retained rawOutput.endpoint rawFormalResult
      (fun childRename => rawLeafReverse childRename) rename
  have stagedToFormal : HostedStrict rawStaged rawFormalRoot := by
    simpa only [rawFormalRoot] using HostedStrict.ofIso rawPresentation
  have stagedReverse : HostedScope rawFormalRoot rawStaged := by
    intro target rename
    simpa only [rawFormalRoot] using
      HostedScope.ofIso rawPresentation.symm rename
  have resultToFormal : HostedStrict result rawFormalRoot := by
    exact HostedStrict.trans rawHosted stagedToFormal
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost
          (fun scopeRename => stagedReverse scopeRename)
          outer hostLocals rename hostItems)
  have resultToRawOutput : HostedStrict result rawOutputRoot := by
    exact HostedStrict.trans resultToFormal liftedRawLeafHosted
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost
          (fun scopeRename => liftedRawLeafReverse scopeRename)
          outer hostLocals rename hostItems)
  have resultToRawOutputScope :
      ScopePreservation result rawOutputRoot := by
    exact rawScope.trans
      ((ScopePreservation.ofIso rawPresentation).trans
        liftedRawLeafScope)
  let output := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) pattern.external)
    PUnit.unit formalEvidence formalSites
  let outputWiresEq :
      ((outer ++ (localBefore ++ localAfter)) ++ retained) =
        (outer ++ (localBefore ++ (localAfter ++ retained))) := by
    simp only [List.append_assoc]
  let outputAtCommon : Region
      ((outer ++ (localBefore ++ localAfter)) ++ retained) :=
    output.endpoint.renameWires
      (WireEquiv.ofEq outputWiresEq).symm.toRenaming
  let rawForward : RegionIso commonEquiv rawOutput.endpoint
      (rawOutput.endpoint.renameWires commonRename) := by
    simpa only [Region.renameWires_id] using
      RegionIso.renameWires rawOutput.endpoint WireRenaming.id commonRename
        commonEquiv (fun _ => rfl)
  let outputBack : RegionIso commonEquiv.symm output.endpoint
      outputAtCommon := by
    simpa only [outputAtCommon, outputWiresEq, commonEquiv,
      Region.renameWires_id] using
      RegionIso.renameWires output.endpoint WireRenaming.id
        commonEquiv.symm.toRenaming commonEquiv.symm (fun _ => rfl)
  let combined :=
    (rawForward.trans formalEndpointPresentation).trans outputBack
  have ambientEq :
      ((commonEquiv.trans (WireEquiv.refl
        (outer ++ (localBefore ++ (localAfter ++ retained))))).trans
          commonEquiv.symm) =
        WireEquiv.refl (common ++ retained) := by
    apply WireEquiv.ext
    intro signature wire
    exact commonEquiv.left_inv wire
  let outputPresentation : RegionIso (WireEquiv.refl (common ++ retained))
      rawOutput.endpoint outputAtCommon :=
    combined.castAmbient ambientEq
  let rootPresentation : RegionIso (WireEquiv.refl common)
      rawOutputRoot (Region.adjoinAt retained .nil outputAtCommon) := by
    simpa only [rawOutputRoot] using
      RegionIso.adjoinAt retained .nil outputPresentation
  have finalHosted : HostedStrict result
      (Region.adjoinAt retained .nil outputAtCommon) :=
    HostedStrict.iso (RegionIso.refl result) rootPresentation
      resultToRawOutput
  have finalScope : ScopePreservation result
      (Region.adjoinAt retained .nil outputAtCommon) :=
    resultToRawOutputScope.trans (ScopePreservation.ofIso rootPresentation)
  refine ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, ?_⟩
  simpa only [outputAtCommon, outputWiresEq, common] using
    And.intro finalHosted finalScope


/-- Accumulate every selected application of an authoritative identity-headed
pattern into one literal IdentityLeaf edit consumed at the binder home. -/
theorem accumulateIdentity
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (List.replicate arity signature) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalIdentityPattern signature arity)
                (Leaf.Identity.rootFrame common [] retained signature arity).sourceKeep
                (Leaf.Identity.rootFrame common [] retained signature arity).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation
                  (Leaf.Identity.operation signature arity) pattern.external)
                PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (Leaf.Identity.Vars.fromFn ports)
                    (normalizationOperation
                      (List.replicate arity signature))
                    (Leaf.Identity.rootFrame common [] retained signature arity)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1,
              let primitiveSites := recordingItemsSitesTarget formalSites
              let output := itemsEdit
                (operation := Leaf.Identity.operation signature arity)
                PUnit.unit formalEvidence primitiveSites
              ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  refine Exists.elim
    (accumulateIdentityAt
      (outer := common) (localBefore := []) (localAfter := []) body_eq
      (by simp) evidence sites) ?_
  intro retained folded
  rcases folded with ⟨formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, coreHosted, coreScope⟩
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have recordedEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  let coreOutputWiresEq :
      (common ++ retained) = common ++ ([] ++ ([] ++ retained)) := by
    simp only [List.nil_append]
  let coreOutput := recordedOutput.endpoint.renameWires
    (WireEquiv.ofEq coreOutputWiresEq).symm.toRenaming
  let coreExactOutput := Region.adjoinAt retained .nil coreOutput
  have coreScope' : ScopePreservation result coreExactOutput := by
    simpa only [coreExactOutput, coreOutput, recordedOutput] using coreScope
  have coreHosted' : HostedStrict result coreExactOutput := by
    simpa only [coreExactOutput, coreOutput, recordedOutput] using coreHosted
  have coreEquivEq : (WireEquiv.ofEq coreOutputWiresEq).symm =
      WireEquiv.refl (common ++ retained) := by
    apply WireEquiv.ext
    intro wireSignature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    exact WireEquiv.ofEq_index_val coreOutputWiresEq
      ((WireEquiv.ofEq coreOutputWiresEq).symm wire)
  have coreOutputEq : coreOutput = recordedOutput.endpoint := by
    change recordedOutput.endpoint.renameWires
      (WireEquiv.ofEq coreOutputWiresEq).symm.toRenaming =
        recordedOutput.endpoint
    rw [coreEquivEq]
    exact Region.renameWires_id recordedOutput.endpoint
  let recordedPresentation : RegionIso (WireEquiv.refl common)
      coreExactOutput
      (Region.adjoinAt retained .nil recordedOutput.endpoint) :=
    RegionIso.adjoinAt retained .nil (RegionIso.ofEq coreOutputEq)
  let primitivePresentation : RegionIso (WireEquiv.refl common)
      (Region.adjoinAt retained .nil recordedOutput.endpoint)
      (Region.adjoinAt retained .nil output.endpoint) :=
    RegionIso.adjoinAt retained .nil
      (RegionIso.ofEq recordedEndpointEq)
  let outputPresentation := recordedPresentation.trans primitivePresentation
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  have outputScope : ScopePreservation result exactOutput :=
    coreScope'.trans (ScopePreservation.ofIso outputPresentation)
  have outputHosted : HostedStrict result exactOutput :=
    HostedStrict.iso (RegionIso.refl result) outputPresentation coreHosted'
  have materialOutputCanonical : exactOutput.Canonical :=
    outputScope.canonical
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have outputReplacement := occurrence.context.replaceCanonical result
    exactOutput occurrence.sourceCanonical materialOutputCanonical
      outputScope.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill result) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have outputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill exactOutput) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ outputReplacement.2
  have strict := HostedStrict.atOccurrence outputHosted occurrence
    outputReplacement.1 outputExternalTwoEnded
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, outputReplacement.1, outputExternalTwoEnded, strict⟩
theorem atomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.StrictDerives polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, positionalFormalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateAtomFormal body_eq evidence sites accumulatorOccurrence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Formal.operation [] atomArguments)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin := by
    exact itemsEdit_noSelectedPin primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  have exactOutputEq : Region.adjoinAt retained .nil recordedOutput.endpoint =
      Region.adjoinAt retained .nil output.endpoint :=
    congrArg (Region.adjoinAt retained .nil) outputEndpointEq
  have primitiveOutputCanonical :
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)).Canonical := by
    rw [← exactOutputEq]
    exact outputCanonical
  have primitiveOutputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      accumulatorOccurrence.interface.boundaryWire
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)) := by
    intro signature wire
    rw [← exactOutputEq]
    exact outputExternalTwoEnded wire
  have primitiveStrict : EqualityNormalization.StrictEquates
      accumulatorOccurrence (Region.adjoinAt retained .nil output.endpoint)
      primitiveOutputCanonical primitiveOutputExternalTwoEnded := by
    let endpointIso : OpenDiagramIso
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil recordedOutput.endpoint))
          outputCanonical outputExternalTwoEnded)
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil output.endpoint))
          primitiveOutputCanonical primitiveOutputExternalTwoEnded) :=
      OpenDiagram.withBody_iso outputCanonical primitiveOutputCanonical
        outputExternalTwoEnded primitiveOutputExternalTwoEnded
        (DiagramContext.fillIso accumulatorOccurrence.context
          (RegionIso.ofEq exactOutputEq))
    exact EqualityNormalization.StrictEquates.targetIso strict endpointIso
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := positionalAtomSelection head ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegionAt
    (outer := common) (localBefore := []) (localAfter := retained)
    formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (positionalAtomWires atomArguments) :: retained)
      positionalFormalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Formal.rootFrame common [] retained [] atomArguments) := by
    exact Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (positionalFormalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : positionalFormalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        positionalFormalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
              simpa [Leaf.Formal.rootFrame, Transform.Frame.replace,
                Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared primitiveOutputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Formal.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact primitiveOutputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro signature wire
      have paths := positionalLocalValidity.2 wire
      have paths' : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, List.nil_append,
          positionalAtomWires] using paths
      simpa only [paths'])
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact primitiveOutputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro signature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt (outer := common) (localBefore := [])
        (localAfter := retained) formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (positionalAtomWires atomArguments) (common ++ retained)
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained))
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (positionalAtomWires atomArguments)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (positionalAtomWires atomArguments))
      (Leaf.Formal.rootFrame common [] retained [] atomArguments)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (positionalAtomWires atomArguments))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : positionalFormalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (positionalAtomWires atomArguments))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (positionalAtomWires atomArguments) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAllAt
      (outer := common) (localBefore := []) (localAfter := retained)
      formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := primitiveStrict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded primitiveOutputCanonical
        primitiveOutputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := primitiveOutputCanonical
    preparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    rawPreparedCanonical := primitiveOutputCanonical
    rawPreparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsFormal (before := []) (after := atomArguments)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalAtomWires] using
          preparation)

/-- The direct authoritative identity branch: accumulate every selected site
into one literal IdentityLeaf edit, prepare its deterministic endpoint, and
run the single directed primitive at the binder home. -/
theorem identityLeaf
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.StrictDerives polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, formalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateIdentity body_eq evidence sites accumulatorOccurrence
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := Leaf.Identity.Vars.fromFn ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegionAt
    (outer := common) (localBefore := []) (localAfter := retained)
    formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (List.replicate arity signature) :: retained) formalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Identity.rootFrame common [] retained signature arity) :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (formalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : formalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        formalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
          simpa [Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared outputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Identity.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact outputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro wireSignature wire
      have paths := positionalLocalValidity.2 wire
      have paths' : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, List.nil_append] using paths
      simpa only [paths'])
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact outputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro wireSignature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt (outer := common) (localBefore := [])
        (localAfter := retained) formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (List.replicate arity signature) (common ++ retained)
        (common ++ (.rel (List.replicate arity signature) :: retained))
        (common ++ (.rel (List.replicate arity signature) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (List.replicate arity signature)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (List.replicate arity signature))
      (Leaf.Identity.rootFrame common [] retained signature arity)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (List.replicate arity signature))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by intro wireSignature wire; rfl) (by rfl)
    have normalizedCoherence : formalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (List.replicate arity signature))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (List.replicate arity signature) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAllAt
      (outer := common) (localBefore := []) (localAfter := retained)
      formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := strict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded outputCanonical
        outputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := outputCanonical
    preparedExternalTwoEnded := outputExternalTwoEnded
    rawPreparedCanonical := outputCanonical
    rawPreparedExternalTwoEnded := outputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsIdentity (signature := signature) (arity := arity)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalPending] using preparation)

/-- Compile the support-completed singleton-atom pattern at an arbitrary
binder placement directly into the caller's exact pending region. -/
theorem supportAtomFormalAt
    {wires atomArguments structuralOuter structuralBefore structuralAfter :
      List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel wires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (supportAtomMaterial head ports)
          (supportAtomMaterial_canonical head ports))
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter wires)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter wires)
        items result)
    (sites : ItemsSites (operation := normalizationOperation wires)
      (frame := normalizationFrame structuralOuter structuralBefore
        structuralAfter wires) PUnit.unit evidence)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel wires :: structuralAfter) items)) :
    request.Result := by
  let targetFrame := Leaf.Formal.rootFrame structuralOuter structuralBefore
    structuralAfter [] atomArguments
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      formalCoherence, staged, hosted, stagedScope, ⟨stagedPresentation⟩,
      _endpointPresentation, sourceCleanup, retainedEq⟩ :=
    accumulateHostedTargetWith
      (outer := structuralOuter) (before := structuralBefore)
      (after := structuralAfter) (targetInserted := []) evidence sites
      (positionalAtomSelection head ports) PUnit.unit
      (EqualityNormalization.formalPorts wires)
      ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun before after => HostedStrict before after ∧
        HostedScope before after)
      (fun region => ⟨HostedStrict.refl region,
        fun rename => ScopePreservation.refl _⟩)
      (fun locals before after transformation =>
        ⟨HostedStrict.adjoinAt locals before after transformation.1,
          HostedScope.adjoinAt locals before after transformation.2⟩)
      (fun first second =>
        ⟨HostedStrict.conjoin _ _ _ _ first.1 second.1, by
          intro target rename
          simpa only [Region.renameWires_conjoin] using
            ScopePreservation.conjoin (first.2 rename) (second.2 rename)⟩)
      (fun transformation =>
        ⟨HostedStrict.cut _ _ transformation.1, by
          intro target rename
          simpa only [Region.singleton_renameWires, Item.renameWires] using
            ScopePreservation.cut (transformation.2 rename)⟩)
      (fun sourceIso targetIso transformation =>
        ⟨HostedStrict.iso sourceIso targetIso transformation.1, by
          intro target rename
          exact ((HostedScope.ofIso sourceIso) rename).trans
            ((transformation.2 rename).trans
              ((HostedScope.ofIso targetIso) rename))⟩)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (formalDataNaturality atomArguments)
      (fun retained => retained = []) rfl
      (fun first second firstEq secondEq => by
        simp only [firstEq, secondEq, List.nil_append])
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame _ => by
        obtain ⟨selectedRetained, selectedSource, selectedResult,
            selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
            selectedHosted, selectedScope, selectedPresentation,
            selectedRetainedEq, selectedCleanup⟩ :=
          supportAtomSelectedTargetItem head ports application siteData
            selectedFrame
        exact ⟨selectedRetained, selectedSource, selectedResult,
          selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
          selectedHosted, selectedScope, selectedPresentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects,
          selectedCleanup, selectedRetainedEq⟩)
  subst retained
  let common := structuralOuter ++ (structuralBefore ++ structuralAfter)
  let positionalSourceWires := structuralOuter ++
    (structuralBefore ++ .rel (positionalAtomWires atomArguments) ::
      structuralAfter)
  let authoritativeSourceWires := structuralOuter ++
    (structuralBefore ++ .rel wires :: structuralAfter)
  let commonRename : WireRenaming (common ++ []) common :=
    (WireEquiv.appendNil common).toRenaming
  let positionalSourceRename : WireRenaming
      (positionalSourceWires ++ []) positionalSourceWires :=
    (WireEquiv.appendNil positionalSourceWires).toRenaming
  let authoritativeSourceRename : WireRenaming
      (authoritativeSourceWires ++ []) authoritativeSourceWires :=
    (WireEquiv.appendNil authoritativeSourceWires).toRenaming
  let authoritativeFrame : Transform.Frame wires common
      authoritativeSourceWires authoritativeSourceWires :=
    Transform.Frame.replace structuralOuter structuralBefore structuralAfter
      [.rel wires] wires
  have sourceKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
        targetFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
          positionalSourceRename
            ((targetFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => positionalSourceRename
          ((targetFrame.append []).sourceKeep value)) liftEq.symm
      _ = positionalSourceRename
          ((targetFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.sourceKeep baseWire := by
        simpa only [positionalSourceRename] using
          WireEquiv.appendNil_apply positionalSourceWires
            (targetFrame.sourceKeep baseWire)
      _ = targetFrame.sourceKeep (commonRename wire) := rfl
  have targetKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      commonRename ((targetFrame.append []).targetKeep wire) =
        targetFrame.targetKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      commonRename ((targetFrame.append []).targetKeep wire) =
          commonRename ((targetFrame.append []).targetKeep
            (baseWire.appendLeft [])) :=
        congrArg (fun value => commonRename
          ((targetFrame.append []).targetKeep value)) liftEq.symm
      _ = commonRename ((targetFrame.targetKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.targetKeep baseWire := by
        simpa only [commonRename] using WireEquiv.appendNil_apply common
          (targetFrame.targetKeep baseWire)
      _ = targetFrame.targetKeep (commonRename wire) := rfl
  have selectedCommutes :
      positionalSourceRename (targetFrame.append []).selected =
        targetFrame.selected := by
    simpa only [positionalSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply positionalSourceWires
        targetFrame.selected
  have argumentKeepCommutes : ∀ {signature}
      (wire : Var (common ++ []) signature),
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
        authoritativeFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
          authoritativeSourceRename
            ((authoritativeFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep value)) liftEq.symm
      _ = authoritativeSourceRename
          ((authoritativeFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = authoritativeFrame.sourceKeep baseWire := by
        simpa only [authoritativeSourceRename] using
          WireEquiv.appendNil_apply authoritativeSourceWires
            (authoritativeFrame.sourceKeep baseWire)
      _ = authoritativeFrame.sourceKeep (commonRename wire) := rfl
  have argumentSelectedCommutes :
      authoritativeSourceRename (authoritativeFrame.append []).selected =
        authoritativeFrame.selected := by
    simpa only [authoritativeSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply authoritativeSourceWires
        authoritativeFrame.selected
  obtain ⟨flatFormalSource, flatFormalResult, flatFormalEvidence,
      flatFormalSites, flatSourceEq, flatPositionalEq, flatAuthoritativeEq,
      ⟨flatResultIso⟩, ⟨flatEndpointIso⟩⟩ :=
    targetItemsReindex
      (baseOperation := Leaf.Formal.operation [] atomArguments)
      (external := wires) (mappedFrame := targetFrame)
      (mappedData := PUnit.unit) formalEvidence formalSites
      (positionalAtomSelection head ports)
      (EqualityNormalization.formalPorts wires)
      (authoritativeFrame.append []) authoritativeFrame
      commonRename positionalSourceRename commonRename
      authoritativeSourceRename sourceKeepCommutes targetKeepCommutes
      selectedCommutes argumentKeepCommutes argumentSelectedCommutes
      (formalDataNaturality atomArguments) True.intro
  let oldLocals := structuralBefore ++ structuralAfter
  let pendingLocals := structuralBefore ++ .rel wires :: structuralAfter
  let pending : Region structuralOuter := .mk pendingLocals items
  let authoritativeItems :=
    (argumentItemsEdit flatFormalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) authoritativeFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1
  let authoritativePending := argumentNormalizedRegionAt
    (outer := structuralOuter) (localBefore := structuralBefore)
    (localAfter := structuralAfter) flatFormalSites
    (EqualityNormalization.formalPorts wires)
  let rawAuthoritativeItems :=
    (argumentItemsEdit formalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) (authoritativeFrame.append [])
      PUnit.unit (fun _ _ _ => PUnit.unit)).1
  let rawAuthoritative := Region.ofItems rawAuthoritativeItems
  let flatAuthoritative := Region.ofItems authoritativeItems
  have renamedAuthoritativeEq :
      rawAuthoritative.renameWires authoritativeSourceRename =
        flatAuthoritative := by
    simpa only [rawAuthoritative, flatAuthoritative, authoritativeItems,
      rawAuthoritativeItems, Region.ofItems_renameWires] using
        congrArg Region.ofItems flatAuthoritativeEq
  let cleanupPresentation : RegionIso
      (WireEquiv.refl authoritativeSourceWires)
      (Region.adjoinAt [] .nil rawAuthoritative)
      flatAuthoritative :=
    (RegionIso.adjoinAtNil rawAuthoritative).symm.trans
      (RegionIso.ofEq renamedAuthoritativeEq)
  have sourceCleanupFlat :
      HostedStrict (Region.ofItems items) flatAuthoritative ∧
        HostedScope (Region.ofItems items) flatAuthoritative := by
    refine ⟨HostedStrict.iso (RegionIso.refl _) cleanupPresentation
        sourceCleanup.1, ?_⟩
    intro target rename
    exact (sourceCleanup.2 rename).trans
      ((HostedScope.ofIso cleanupPresentation) rename)
  have cleanupHosted : HostedStrict pending authoritativePending := by
    have lifted := HostedStrict.adjoinAt pendingLocals
      (Region.ofItems items) flatAuthoritative sourceCleanupFlat.1
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems pendingLocals items).symm
      (by
        simpa only [authoritativePending, argumentNormalizedRegionAt,
          authoritativeItems] using
            RegionIso.adjoinAtOfItems pendingLocals authoritativeItems)
      lifted
  have cleanupHostedScope : HostedScope pending authoritativePending := by
    have lifted : HostedScope
        (Region.adjoinAt pendingLocals .nil (Region.ofItems items))
        (Region.adjoinAt pendingLocals .nil flatAuthoritative) := by
      intro target rename
      exact HostedScope.adjoinAt pendingLocals
        (Region.ofItems items) flatAuthoritative sourceCleanupFlat.2 rename
    intro target rename
    exact ((HostedScope.ofIso
        (RegionIso.adjoinAtOfItems pendingLocals items).symm) rename).trans
      ((lifted rename).trans
        ((HostedScope.ofIso (by
          simpa only [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems] using
              RegionIso.adjoinAtOfItems pendingLocals authoritativeItems))
          rename))
  have cleanupScope : ScopePreservation pending authoritativePending := by
    simpa only [Region.renameWires_id] using
      cleanupHostedScope WireRenaming.id
  have pendingCanonical :
      (request.occurrence.context.fill pending).Canonical := by
    simpa only [pending, pendingLocals] using request.pendingCanonical
  have pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill pending) := by
    intro signature wire
    simpa only [pending, pendingLocals] using
      request.pendingExternalTwoEnded wire
  have authoritativeValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context pending
    authoritativePending pendingCanonical pendingExternalTwoEnded cleanupScope
  have cleanupTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending pending authoritativeValidity.1
      authoritativeValidity.2 pendingCanonical pendingExternalTwoEnded :=
    telescopeOfHostedExact cleanupHosted.symm request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativeValidity.1 authoritativeValidity.2 pendingCanonical
      pendingExternalTwoEnded request.continuation.1
  have authoritativeContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending request.endpoint authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    telescopeTrans cleanupTelescope (by simpa only [pending, pendingLocals] using
      request.continuation)
  let positionalValues := positionalAtomSelection head ports
  have flatFormalCoherence : flatFormalSource =
      (argumentItemsEdit flatFormalSites positionalValues
        (normalizationOperation (positionalAtomWires atomArguments))
        targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    have mappedCoherence : formalSource.renameWires positionalSourceRename =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (positionalAtomWires atomArguments))
          (targetFrame.append []) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1.renameWires
            positionalSourceRename :=
      congrArg (fun source => source.renameWires positionalSourceRename)
        formalCoherence
    exact flatSourceEq.symm.trans (mappedCoherence.trans flatPositionalEq)
  let positionalPending : Region structuralOuter :=
    .mk (structuralBefore ++
      .rel (positionalAtomWires atomArguments) :: structuralAfter)
      flatFormalSource
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt
        (outer := structuralOuter) (localBefore := structuralBefore)
        (localAfter := structuralAfter) flatFormalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (positionalAtomWires atomArguments)
        (structuralOuter ++ (structuralBefore ++ structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (positionalAtomWires atomArguments) :: structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (positionalAtomWires atomArguments) :: structuralAfter)) :=
      Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [.rel (positionalAtomWires atomArguments)]
        (positionalAtomWires atomArguments)
    have sourceIndependent := argumentItemsEdit_source_independent
      flatFormalSites positionalValues
      (normalizationOperation (positionalAtomWires atomArguments))
      targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (positionalAtomWires atomArguments))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : flatFormalSource =
        (argumentItemsEdit flatFormalSites positionalValues
          (normalizationOperation (positionalAtomWires atomArguments))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      flatFormalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (structuralBefore ++
        .rel (positionalAtomWires atomArguments) :: structuralAfter))
      normalizedCoherence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) wires)
    PUnit.unit flatFormalEvidence flatFormalSites
  let primitiveSites := recordingItemsSitesTarget flatFormalSites
  let output := itemsEdit
    (operation := Leaf.Formal.operation [] atomArguments)
    PUnit.unit flatFormalEvidence primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq flatFormalSites
  have targetKeepIdentity : targetFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := structuralOuter)
      (right := structuralBefore ++ structuralAfter)
      (motive := fun wire => targetFrame.targetKeep wire = wire)
    · intro outerSignature outerWire
      simp [targetFrame, Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := structuralBefore)
        (right := structuralAfter)
        (motive := fun localWire =>
          targetFrame.targetKeep
              (Var.appendRight structuralOuter localWire) =
            Var.appendRight structuralOuter localWire)
      · intro beforeSignature beforeWire
        simp [targetFrame, Leaf.Formal.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp [targetFrame, Leaf.Formal.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendRight]
  obtain ⟨recordedLeafHosted, recordedLeafScope⟩ :=
    leafItemsEndpoint flatFormalEvidence flatFormalSites targetKeepIdentity
      (fun siteTargetKeepEq application site => by
        have endpoint := positionalAtomLeafEndpoint atomArguments
          siteTargetKeepEq application site
        exact ⟨endpoint.1, endpoint.2.1⟩)
  have recordedLeafReverse : HostedScope recordedOutput.endpoint
      flatFormalResult := by
    intro target rename
    exact leafItemsReverseHostedScope flatFormalEvidence flatFormalSites
      targetKeepIdentity
      (fun siteTargetKeepEq application site => by
        intro siteTarget siteRename
        exact (positionalAtomLeafEndpoint atomArguments
          siteTargetKeepEq application site).2.2 siteRename)
      rename
  have leafHosted : HostedStrict flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafHosted
  have leafScope : ScopePreservation flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafScope
  have leafReverse : HostedScope output.endpoint flatFormalResult := by
    intro target rename
    rw [← outputEndpointEq]
    exact recordedLeafReverse rename
  let stagedToFlatFormal : RegionIso (WireEquiv.refl common) staged
      flatFormalResult :=
    stagedPresentation.trans
      ((RegionIso.adjoinAtNil formalResult).symm.trans flatResultIso)
  have resultToFormal : HostedStrict result flatFormalResult :=
    HostedStrict.iso (RegionIso.refl result) stagedToFlatFormal hosted
  have resultToOutput : HostedStrict result output.endpoint :=
    HostedStrict.trans resultToFormal leafHosted
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost leafReverse outer hostLocals rename hostItems)
  have resultToOutputScope : ScopePreservation result output.endpoint :=
    stagedScope.trans
      ((ScopePreservation.ofIso stagedToFlatFormal).trans leafScope)
  let instantiated := Region.adjoinAt oldLocals .nil result
  let prepared := Region.adjoinAt oldLocals .nil output.endpoint
  have instantiatedToPrepared : HostedStrict instantiated prepared := by
    simpa only [instantiated, prepared] using
      HostedStrict.adjoinAt oldLocals result output.endpoint resultToOutput
  have instantiatedToPreparedScope : ScopePreservation instantiated prepared :=
    adjoinAt_preserves_scope oldLocals .nil result output.endpoint
      resultToOutputScope
  have instantiatedCanonical :
      (request.occurrence.context.fill instantiated).Canonical := by
    simpa only [instantiated, oldLocals] using request.instantiatedCanonical
  have instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill instantiated) := by
    intro signature wire
    simpa only [instantiated, oldLocals] using
      request.instantiatedExternalTwoEnded wire
  have preparedValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context instantiated
    prepared instantiatedCanonical instantiatedExternalTwoEnded
    instantiatedToPreparedScope
  have preparationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      instantiated prepared instantiatedCanonical instantiatedExternalTwoEnded
      preparedValidity.1 preparedValidity.2 :=
    telescopeOfHostedExact instantiatedToPrepared request.polarity
      request.occurrence.interface request.occurrence.context
      instantiatedCanonical instantiatedExternalTwoEnded preparedValidity.1
      preparedValidity.2 request.continuation.1
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    request.occurrence.context.holeCanonical authoritativePending
      authoritativeValidity.1
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths flatFormalSites
    (EqualityNormalization.formalPorts wires)
    (normalizationOperation wires) authoritativeFrame PUnit.unit
    (fun _ _ _ => PUnit.unit) authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant targetFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := flatFormalSites.source_selectedPaths formalInvariant 0
  let selectedLocalIndex : Fin pendingLocals.length :=
    ⟨structuralBefore.length, by
      simp [pendingLocals]⟩
  have authoritativeRoot :=
    authoritativeLocalCanonical.1 selectedLocalIndex
  have selectedRooted : RegionPath.RootedTwo
      (flatFormalSource.incidencePaths
        (structuralOuter.length + structuralBefore.length) 0) := by
    have pathEq : flatFormalSource.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 =
        authoritativePending.items.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 := by
      calc
        flatFormalSource.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 =
            flatFormalSites.selectedPaths 0 := by
          simpa [targetFrame, Leaf.Formal.rootFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead]
            using formalPaths
        _ = authoritativePending.items.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems, authoritativeFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead,
            normalizationFrame] using authoritativePaths
    rw [pathEq]
    simpa [authoritativePending, selectedLocalIndex, pendingLocals] using
      authoritativeRoot
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let rawPrepared := Region.adjoinAt oldLocals .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact request.occurrence.context.holeCanonical prepared preparedValidity.1
  have positionalLocalValidity := Leaf.Formal.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical :
      (request.occurrence.context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.1
  have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill rawPrepared) := by
    intro signature wire
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.2 wire
  let rawToPositionalScope : ScopePreservation rawPrepared positionalPending := {
    canonical := fun _ => positionalLocalValidity.1
    incidenceNonempty := fun wire => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      simpa only [paths]
    rootedTwo := fun wire rooted => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      rw [← paths]
      exact rooted
  }
  have positionalValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context rawPrepared
    positionalPending rawPreparedFilledCanonical rawPreparedFilledExternal
    rawToPositionalScope
  have normalizationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      positionalPending request.endpoint positionalValidity.1
      positionalValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    argumentNormalizationTelescopeAllAt
      (outer := structuralOuter) (localBefore := structuralBefore)
      (localAfter := structuralAfter) flatFormalSites positionalValues
      request.occurrence.interface request.occurrence.context positionalEq
      positionalValidity.1 positionalValidity.2 authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded request.polarity request.continuation.1
      authoritativeContinuation
  let formalRequest : Telescope.Request instantiated positionalPending := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := positionalValidity.1
    pendingExternalTwoEnded := positionalValidity.2
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  let preparation : formalRequest.Preparation prepared := {
    prepared := prepared
    preparedCanonical := preparedValidity.1
    preparedExternalTwoEnded := preparedValidity.2
    rawPreparedCanonical := preparedValidity.1
    rawPreparedExternalTwoEnded := preparedValidity.2
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [formalRequest] using preparationTelescope
  }
  exact itemsFormal (before := []) (after := atomArguments)
    (localBefore := structuralBefore) (localAfter := structuralAfter)
    flatFormalEvidence primitiveSites formalRequest (by
      simpa only [prepared, oldLocals, output] using preparation)


theorem supportIdentityFormalAt
    {wires structuralOuter structuralBefore structuralAfter :
      List Sig}
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel wires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (supportIdentityMaterial signature arity ports)
          (supportIdentityMaterial_canonical signature arity ports))
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter wires)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter wires)
        items result)
    (sites : ItemsSites (operation := normalizationOperation wires)
      (frame := normalizationFrame structuralOuter structuralBefore
        structuralAfter wires) PUnit.unit evidence)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel wires :: structuralAfter) items)) :
    request.Result := by
  let targetFrame := Leaf.Identity.rootFrame structuralOuter structuralBefore
    structuralAfter signature arity
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      formalCoherence, staged, hosted, stagedScope, ⟨stagedPresentation⟩,
      _endpointPresentation, sourceCleanup, retainedEq⟩ :=
    accumulateHostedTargetWith
      (outer := structuralOuter) (before := structuralBefore)
      (after := structuralAfter) (targetInserted := []) evidence sites
      (Leaf.Identity.Vars.fromFn ports) PUnit.unit
      (EqualityNormalization.formalPorts wires)
      ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun before after => HostedStrict before after ∧
        HostedScope before after)
      (fun region => ⟨HostedStrict.refl region,
        fun rename => ScopePreservation.refl _⟩)
      (fun locals before after transformation =>
        ⟨HostedStrict.adjoinAt locals before after transformation.1,
          HostedScope.adjoinAt locals before after transformation.2⟩)
      (fun first second =>
        ⟨HostedStrict.conjoin _ _ _ _ first.1 second.1, by
          intro target rename
          simpa only [Region.renameWires_conjoin] using
            ScopePreservation.conjoin (first.2 rename) (second.2 rename)⟩)
      (fun transformation =>
        ⟨HostedStrict.cut _ _ transformation.1, by
          intro target rename
          simpa only [Region.singleton_renameWires, Item.renameWires] using
            ScopePreservation.cut (transformation.2 rename)⟩)
      (fun sourceIso targetIso transformation =>
        ⟨HostedStrict.iso sourceIso targetIso transformation.1, by
          intro target rename
          exact ((HostedScope.ofIso sourceIso) rename).trans
            ((transformation.2 rename).trans
              ((HostedScope.ofIso targetIso) rename))⟩)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (identityDataNaturality signature arity)
      (fun retained => retained = []) rfl
      (fun first second firstEq secondEq => by
        simp only [firstEq, secondEq, List.nil_append])
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame _ => by
        obtain ⟨selectedRetained, selectedSource, selectedResult,
            selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
            selectedHosted, selectedScope, selectedPresentation,
            selectedRetainedEq, selectedCleanup⟩ :=
          supportIdentitySelectedTargetItem signature arity ports application siteData
            selectedFrame
        exact ⟨selectedRetained, selectedSource, selectedResult,
          selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
          selectedHosted, selectedScope, selectedPresentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects,
          selectedCleanup, selectedRetainedEq⟩)
  subst retained
  let common := structuralOuter ++ (structuralBefore ++ structuralAfter)
  let positionalSourceWires := structuralOuter ++
    (structuralBefore ++ .rel (List.replicate arity signature) ::
      structuralAfter)
  let authoritativeSourceWires := structuralOuter ++
    (structuralBefore ++ .rel wires :: structuralAfter)
  let commonRename : WireRenaming (common ++ []) common :=
    (WireEquiv.appendNil common).toRenaming
  let positionalSourceRename : WireRenaming
      (positionalSourceWires ++ []) positionalSourceWires :=
    (WireEquiv.appendNil positionalSourceWires).toRenaming
  let authoritativeSourceRename : WireRenaming
      (authoritativeSourceWires ++ []) authoritativeSourceWires :=
    (WireEquiv.appendNil authoritativeSourceWires).toRenaming
  let authoritativeFrame : Transform.Frame wires common
      authoritativeSourceWires authoritativeSourceWires :=
    Transform.Frame.replace structuralOuter structuralBefore structuralAfter
      [.rel wires] wires
  have sourceKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
        targetFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
          positionalSourceRename
            ((targetFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => positionalSourceRename
          ((targetFrame.append []).sourceKeep value)) liftEq.symm
      _ = positionalSourceRename
          ((targetFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.sourceKeep baseWire := by
        simpa only [positionalSourceRename] using
          WireEquiv.appendNil_apply positionalSourceWires
            (targetFrame.sourceKeep baseWire)
      _ = targetFrame.sourceKeep (commonRename wire) := rfl
  have targetKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      commonRename ((targetFrame.append []).targetKeep wire) =
        targetFrame.targetKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      commonRename ((targetFrame.append []).targetKeep wire) =
          commonRename ((targetFrame.append []).targetKeep
            (baseWire.appendLeft [])) :=
        congrArg (fun value => commonRename
          ((targetFrame.append []).targetKeep value)) liftEq.symm
      _ = commonRename ((targetFrame.targetKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.targetKeep baseWire := by
        simpa only [commonRename] using WireEquiv.appendNil_apply common
          (targetFrame.targetKeep baseWire)
      _ = targetFrame.targetKeep (commonRename wire) := rfl
  have selectedCommutes :
      positionalSourceRename (targetFrame.append []).selected =
        targetFrame.selected := by
    simpa only [positionalSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply positionalSourceWires
        targetFrame.selected
  have argumentKeepCommutes : ∀ {signature}
      (wire : Var (common ++ []) signature),
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
        authoritativeFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
          authoritativeSourceRename
            ((authoritativeFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep value)) liftEq.symm
      _ = authoritativeSourceRename
          ((authoritativeFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = authoritativeFrame.sourceKeep baseWire := by
        simpa only [authoritativeSourceRename] using
          WireEquiv.appendNil_apply authoritativeSourceWires
            (authoritativeFrame.sourceKeep baseWire)
      _ = authoritativeFrame.sourceKeep (commonRename wire) := rfl
  have argumentSelectedCommutes :
      authoritativeSourceRename (authoritativeFrame.append []).selected =
        authoritativeFrame.selected := by
    simpa only [authoritativeSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply authoritativeSourceWires
        authoritativeFrame.selected
  obtain ⟨flatFormalSource, flatFormalResult, flatFormalEvidence,
      flatFormalSites, flatSourceEq, flatPositionalEq, flatAuthoritativeEq,
      ⟨flatResultIso⟩, ⟨flatEndpointIso⟩⟩ :=
    targetItemsReindex
      (baseOperation := Leaf.Identity.operation signature arity)
      (external := wires) (mappedFrame := targetFrame)
      (mappedData := PUnit.unit) formalEvidence formalSites
      (Leaf.Identity.Vars.fromFn ports)
      (EqualityNormalization.formalPorts wires)
      (authoritativeFrame.append []) authoritativeFrame
      commonRename positionalSourceRename commonRename
      authoritativeSourceRename sourceKeepCommutes targetKeepCommutes
      selectedCommutes argumentKeepCommutes argumentSelectedCommutes
      (identityDataNaturality signature arity) True.intro
  let oldLocals := structuralBefore ++ structuralAfter
  let pendingLocals := structuralBefore ++ .rel wires :: structuralAfter
  let pending : Region structuralOuter := .mk pendingLocals items
  let authoritativeItems :=
    (argumentItemsEdit flatFormalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) authoritativeFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1
  let authoritativePending := argumentNormalizedRegionAt
    (outer := structuralOuter) (localBefore := structuralBefore)
    (localAfter := structuralAfter) flatFormalSites
    (EqualityNormalization.formalPorts wires)
  let rawAuthoritativeItems :=
    (argumentItemsEdit formalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) (authoritativeFrame.append [])
      PUnit.unit (fun _ _ _ => PUnit.unit)).1
  let rawAuthoritative := Region.ofItems rawAuthoritativeItems
  let flatAuthoritative := Region.ofItems authoritativeItems
  have renamedAuthoritativeEq :
      rawAuthoritative.renameWires authoritativeSourceRename =
        flatAuthoritative := by
    simpa only [rawAuthoritative, flatAuthoritative, authoritativeItems,
      rawAuthoritativeItems, Region.ofItems_renameWires] using
        congrArg Region.ofItems flatAuthoritativeEq
  let cleanupPresentation : RegionIso
      (WireEquiv.refl authoritativeSourceWires)
      (Region.adjoinAt [] .nil rawAuthoritative)
      flatAuthoritative :=
    (RegionIso.adjoinAtNil rawAuthoritative).symm.trans
      (RegionIso.ofEq renamedAuthoritativeEq)
  have sourceCleanupFlat :
      HostedStrict (Region.ofItems items) flatAuthoritative ∧
        HostedScope (Region.ofItems items) flatAuthoritative := by
    refine ⟨HostedStrict.iso (RegionIso.refl _) cleanupPresentation
        sourceCleanup.1, ?_⟩
    intro target rename
    exact (sourceCleanup.2 rename).trans
      ((HostedScope.ofIso cleanupPresentation) rename)
  have cleanupHosted : HostedStrict pending authoritativePending := by
    have lifted := HostedStrict.adjoinAt pendingLocals
      (Region.ofItems items) flatAuthoritative sourceCleanupFlat.1
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems pendingLocals items).symm
      (by
        simpa only [authoritativePending, argumentNormalizedRegionAt,
          authoritativeItems] using
            RegionIso.adjoinAtOfItems pendingLocals authoritativeItems)
      lifted
  have cleanupHostedScope : HostedScope pending authoritativePending := by
    have lifted : HostedScope
        (Region.adjoinAt pendingLocals .nil (Region.ofItems items))
        (Region.adjoinAt pendingLocals .nil flatAuthoritative) := by
      intro target rename
      exact HostedScope.adjoinAt pendingLocals
        (Region.ofItems items) flatAuthoritative sourceCleanupFlat.2 rename
    intro target rename
    exact ((HostedScope.ofIso
        (RegionIso.adjoinAtOfItems pendingLocals items).symm) rename).trans
      ((lifted rename).trans
        ((HostedScope.ofIso (by
          simpa only [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems] using
              RegionIso.adjoinAtOfItems pendingLocals authoritativeItems))
          rename))
  have cleanupScope : ScopePreservation pending authoritativePending := by
    simpa only [Region.renameWires_id] using
      cleanupHostedScope WireRenaming.id
  have pendingCanonical :
      (request.occurrence.context.fill pending).Canonical := by
    simpa only [pending, pendingLocals] using request.pendingCanonical
  have pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill pending) := by
    intro signature wire
    simpa only [pending, pendingLocals] using
      request.pendingExternalTwoEnded wire
  have authoritativeValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context pending
    authoritativePending pendingCanonical pendingExternalTwoEnded cleanupScope
  have cleanupTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending pending authoritativeValidity.1
      authoritativeValidity.2 pendingCanonical pendingExternalTwoEnded :=
    telescopeOfHostedExact cleanupHosted.symm request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativeValidity.1 authoritativeValidity.2 pendingCanonical
      pendingExternalTwoEnded request.continuation.1
  have authoritativeContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending request.endpoint authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    telescopeTrans cleanupTelescope (by simpa only [pending, pendingLocals] using
      request.continuation)
  let positionalValues := Leaf.Identity.Vars.fromFn ports
  have flatFormalCoherence : flatFormalSource =
      (argumentItemsEdit flatFormalSites positionalValues
        (normalizationOperation (List.replicate arity signature))
        targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    have mappedCoherence : formalSource.renameWires positionalSourceRename =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (List.replicate arity signature))
          (targetFrame.append []) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1.renameWires
            positionalSourceRename :=
      congrArg (fun source => source.renameWires positionalSourceRename)
        formalCoherence
    exact flatSourceEq.symm.trans (mappedCoherence.trans flatPositionalEq)
  let positionalPending : Region structuralOuter :=
    .mk (structuralBefore ++
      .rel (List.replicate arity signature) :: structuralAfter)
      flatFormalSource
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt
        (outer := structuralOuter) (localBefore := structuralBefore)
        (localAfter := structuralAfter) flatFormalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (List.replicate arity signature)
        (structuralOuter ++ (structuralBefore ++ structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (List.replicate arity signature) :: structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (List.replicate arity signature) :: structuralAfter)) :=
      Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [.rel (List.replicate arity signature)]
        (List.replicate arity signature)
    have sourceIndependent := argumentItemsEdit_source_independent
      flatFormalSites positionalValues
      (normalizationOperation (List.replicate arity signature))
      targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (List.replicate arity signature))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : flatFormalSource =
        (argumentItemsEdit flatFormalSites positionalValues
          (normalizationOperation (List.replicate arity signature))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      flatFormalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (structuralBefore ++
        .rel (List.replicate arity signature) :: structuralAfter))
      normalizedCoherence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) wires)
    PUnit.unit flatFormalEvidence flatFormalSites
  let primitiveSites := recordingItemsSitesTarget flatFormalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit flatFormalEvidence primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq flatFormalSites
  have targetKeepIdentity : targetFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := structuralOuter)
      (right := structuralBefore ++ structuralAfter)
      (motive := fun wire => targetFrame.targetKeep wire = wire)
    · intro outerSignature outerWire
      simp [targetFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := structuralBefore)
        (right := structuralAfter)
        (motive := fun localWire =>
          targetFrame.targetKeep
              (Var.appendRight structuralOuter localWire) =
            Var.appendRight structuralOuter localWire)
      · intro beforeSignature beforeWire
        simp [targetFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp [targetFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendRight]
  obtain ⟨recordedLeafHosted, recordedLeafScope⟩ :=
    leafItemsEndpoint flatFormalEvidence flatFormalSites targetKeepIdentity
      (fun siteTargetKeepEq application site => by
        have endpoint := positionalIdentityLeafEndpoint signature arity
          siteTargetKeepEq application site
        exact ⟨endpoint.1, endpoint.2⟩)
  have recordedLeafReverse : HostedScope recordedOutput.endpoint
      flatFormalResult := by
    intro target rename
    exact leafItemsReverseHostedScope flatFormalEvidence flatFormalSites
      targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalIdentityLeafEndpoint_reverseHostedScope signature arity
          siteTargetKeepEq application site)
      rename
  have leafHosted : HostedStrict flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafHosted
  have leafScope : ScopePreservation flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafScope
  have leafReverse : HostedScope output.endpoint flatFormalResult := by
    intro target rename
    rw [← outputEndpointEq]
    exact recordedLeafReverse rename
  let stagedToFlatFormal : RegionIso (WireEquiv.refl common) staged
      flatFormalResult :=
    stagedPresentation.trans
      ((RegionIso.adjoinAtNil formalResult).symm.trans flatResultIso)
  have resultToFormal : HostedStrict result flatFormalResult :=
    HostedStrict.iso (RegionIso.refl result) stagedToFlatFormal hosted
  have resultToOutput : HostedStrict result output.endpoint :=
    HostedStrict.trans resultToFormal leafHosted
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost leafReverse outer hostLocals rename hostItems)
  have resultToOutputScope : ScopePreservation result output.endpoint :=
    stagedScope.trans
      ((ScopePreservation.ofIso stagedToFlatFormal).trans leafScope)
  let instantiated := Region.adjoinAt oldLocals .nil result
  let prepared := Region.adjoinAt oldLocals .nil output.endpoint
  have instantiatedToPrepared : HostedStrict instantiated prepared := by
    simpa only [instantiated, prepared] using
      HostedStrict.adjoinAt oldLocals result output.endpoint resultToOutput
  have instantiatedToPreparedScope : ScopePreservation instantiated prepared :=
    adjoinAt_preserves_scope oldLocals .nil result output.endpoint
      resultToOutputScope
  have instantiatedCanonical :
      (request.occurrence.context.fill instantiated).Canonical := by
    simpa only [instantiated, oldLocals] using request.instantiatedCanonical
  have instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill instantiated) := by
    intro signature wire
    simpa only [instantiated, oldLocals] using
      request.instantiatedExternalTwoEnded wire
  have preparedValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context instantiated
    prepared instantiatedCanonical instantiatedExternalTwoEnded
    instantiatedToPreparedScope
  have preparationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      instantiated prepared instantiatedCanonical instantiatedExternalTwoEnded
      preparedValidity.1 preparedValidity.2 :=
    telescopeOfHostedExact instantiatedToPrepared request.polarity
      request.occurrence.interface request.occurrence.context
      instantiatedCanonical instantiatedExternalTwoEnded preparedValidity.1
      preparedValidity.2 request.continuation.1
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    request.occurrence.context.holeCanonical authoritativePending
      authoritativeValidity.1
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths flatFormalSites
    (EqualityNormalization.formalPorts wires)
    (normalizationOperation wires) authoritativeFrame PUnit.unit
    (fun _ _ _ => PUnit.unit) authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant targetFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := flatFormalSites.source_selectedPaths formalInvariant 0
  let selectedLocalIndex : Fin pendingLocals.length :=
    ⟨structuralBefore.length, by
      simp [pendingLocals]⟩
  have authoritativeRoot :=
    authoritativeLocalCanonical.1 selectedLocalIndex
  have selectedRooted : RegionPath.RootedTwo
      (flatFormalSource.incidencePaths
        (structuralOuter.length + structuralBefore.length) 0) := by
    have pathEq : flatFormalSource.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 =
        authoritativePending.items.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 := by
      calc
        flatFormalSource.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 =
            flatFormalSites.selectedPaths 0 := by
          simpa [targetFrame, Leaf.Identity.rootFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead]
            using formalPaths
        _ = authoritativePending.items.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems, authoritativeFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead,
            normalizationFrame] using authoritativePaths
    rw [pathEq]
    simpa [authoritativePending, selectedLocalIndex, pendingLocals] using
      authoritativeRoot
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let rawPrepared := Region.adjoinAt oldLocals .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact request.occurrence.context.holeCanonical prepared preparedValidity.1
  have positionalLocalValidity := Leaf.Identity.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical :
      (request.occurrence.context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.1
  have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill rawPrepared) := by
    intro signature wire
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.2 wire
  let rawToPositionalScope : ScopePreservation rawPrepared positionalPending := {
    canonical := fun _ => positionalLocalValidity.1
    incidenceNonempty := fun wire => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      simpa only [paths]
    rootedTwo := fun wire rooted => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      rw [← paths]
      exact rooted
  }
  have positionalValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context rawPrepared
    positionalPending rawPreparedFilledCanonical rawPreparedFilledExternal
    rawToPositionalScope
  have normalizationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      positionalPending request.endpoint positionalValidity.1
      positionalValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    argumentNormalizationTelescopeAllAt
      (outer := structuralOuter) (localBefore := structuralBefore)
      (localAfter := structuralAfter) flatFormalSites positionalValues
      request.occurrence.interface request.occurrence.context positionalEq
      positionalValidity.1 positionalValidity.2 authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded request.polarity request.continuation.1
      authoritativeContinuation
  let formalRequest : Telescope.Request instantiated positionalPending := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := positionalValidity.1
    pendingExternalTwoEnded := positionalValidity.2
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  let preparation : formalRequest.Preparation prepared := {
    prepared := prepared
    preparedCanonical := preparedValidity.1
    preparedExternalTwoEnded := preparedValidity.2
    rawPreparedCanonical := preparedValidity.1
    rawPreparedExternalTwoEnded := preparedValidity.2
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [formalRequest] using preparationTelescope
  }
  exact itemsIdentity (signature := signature) (arity := arity)
    (localBefore := structuralBefore) (localAfter := structuralAfter)
    flatFormalEvidence primitiveSites formalRequest (by
      simpa only [prepared, oldLocals, output] using preparation)

end VisualProof.Rule.Completeness.Comprehension
