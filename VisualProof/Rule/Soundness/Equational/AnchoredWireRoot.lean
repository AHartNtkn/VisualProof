import VisualProof.Rule.Soundness.Equational.AnchoredWireRoute

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

theorem anchoredWireSplitRaw_bindersCover
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    {rels : RelCtx} (binders : ConcreteElaboration.BinderContext input.val rels)
    (region : Fin input.val.regionCount)
    (cover : ConcreteElaboration.BinderContext.Covers
      (d := input.val) binders region) :
    ConcreteElaboration.BinderContext.Covers
      (d := anchoredWireSplitRaw input wire endpoints target term)
      binders region := by
  intro binder parent arity binderKind encloses
  apply cover binder parent arity
  · simpa only [anchoredWireSplitRaw_regions] using binderKind
  · exact (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      binder region).mp encloses

def anchoredWireSplitRaw_binderEnumeration
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    {rels : RelCtx} (binders : ConcreteElaboration.BinderContext input.val rels)
    (region : Fin input.val.regionCount)
    (enumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val binders region) :
    ConcreteElaboration.BinderContext.Enumeration
      (anchoredWireSplitRaw input wire endpoints target term) binders region where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := by
    intro index
    obtain ⟨parent, kind⟩ := enumeration.bubble index
    exact ⟨parent, by simpa only [anchoredWireSplitRaw_regions] using kind⟩
  encloses := by
    intro index
    exact (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      (enumeration.binder index) region).mpr (enumeration.encloses index)
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

/-- A complete semantic kernel at one certified availability region. -/
def AnchoredAvailableKernel
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature) :
    Prop :=
  ∀ {rels : RelCtx} (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (bindersCover : binders.Covers available)
    (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val binders available)
    (originalExact : (original.extend available).Exact available)
    (expandedExact : (expanded.extend available).Exact available)
    (sourceBody : Region signature original.length rels)
    (targetBody : Region signature expanded.length rels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
      (fuel + 1) available original binders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (anchoredWireSplitRaw input wire endpoints target term)
      (fuel + 1) available expanded binders = some targetBody)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin original.length → model.Carrier)
    (targetOuter : Fin expanded.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    sourceOuter ∘ collapse.indexMap = targetOuter →
      (denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody)

theorem anchoredWireSplitRaw_certified_available_kernel
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs wire
      { node := witness, port := .output })
    (witnessKept : { node := witness, port := CPort.output } ∉ endpoints)
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature)
    (wireEnclosesAvailable :
      input.val.Encloses (input.val.wires wire).scope available)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {witnessPath targetPath : List Nat}
    (witnessRoute : Diagram.Splice.RegionRoute input.val available witnessRegion
      witnessPath)
    (witnessZero : witnessRoute.HasCutDepth 0)
    (sameDepth : concreteCutDepth input.val available =
      concreteCutDepth input.val witnessRegion)
    (targetRoute : Diagram.Splice.RegionRoute input.val available target
      targetPath) :
    AnchoredAvailableKernel input wire endpoints target available term
      targetWellFormed := by
  let targetChecked : CheckedDiagram signature :=
    ⟨anchoredWireSplitRaw input wire endpoints target term, targetWellFormed⟩
  have targetWitnessEncloses : targetChecked.val.Encloses available witnessRegion :=
    (anchoredWireSplitRaw_encloses_iff input wire endpoints target term
      available witnessRegion).mpr
      (regionRoute_encloses input.val input.property witnessRoute)
  obtain ⟨targetWitnessPath, ⟨targetWitnessRoute⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses targetChecked.val available
      witnessRegion targetWitnessEncloses
  obtain ⟨targetWitnessDepth, targetWitnessDepthProof⟩ :=
    targetWitnessRoute.hasCutDepth_exists targetWellFormed
  have depthPreserve : ∀ fuel (region : Fin input.val.regionCount),
      concreteCutDepthAux targetChecked.val fuel region =
        concreteCutDepthAux input.val fuel region := by
    intro fuel
    induction fuel with
    | zero => intro region; rfl
    | succ fuel ih =>
        intro region
        simp only [concreteCutDepthAux]
        rw [show targetChecked.val.regions region = input.val.regions region by
          simp [targetChecked, anchoredWireSplitRaw_regions]]
        cases kind : input.val.regions region with
        | sheet => rfl
        | cut parent => simp only [ih]
        | bubble parent arity => simp only [ih]
  have targetSameDepth : concreteCutDepth targetChecked.val available =
      concreteCutDepth targetChecked.val witnessRegion := by
    unfold concreteCutDepth
    rw [depthPreserve, depthPreserve]
    exact sameDepth
  have targetDepthZero := CongruenceSoundness.route_cutDepth_zero_of_equal
    targetChecked targetWitnessRoute targetWitnessDepth targetWitnessDepthProof
    targetSameDepth
  subst targetWitnessDepth
  have targetWitnessShape : targetChecked.val.nodes witness.castSucc =
      .term witnessRegion 0 term := by
    simpa [targetChecked, witnessShape] using
      anchoredWireSplitRaw_oldNode input wire endpoints target term witness
  have targetWitnessOccurs : targetChecked.val.EndpointOccurs wire.castSucc
      { node := witness.castSucc, port := .output } := by
    simpa using (anchoredWireSplitRaw_old_oldEndpointOccurs_iff input wire wire
      endpoints target term { node := witness, port := .output }).mpr
        ⟨witnessOccurs, fun _ => witnessKept⟩
  intro rels fuel original expanded collapse binders bindersCover
    binderEnumeration originalExact expandedExact sourceBody targetBody
    sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
    outerAgrees
  simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
  cases sourceItemsResult :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (original.extend available) binders
        (ConcreteElaboration.localOccurrences input.val available) with
  | none => simp [sourceItemsResult] at sourceCompiled
  | some sourceItems =>
    simp [sourceItemsResult] at sourceCompiled
    subst sourceBody
    cases targetItemsResult :
        ConcreteElaboration.compileOccurrencesWith? signature targetChecked.val
          (ConcreteElaboration.compileRegion? signature targetChecked.val fuel)
          (expanded.extend available) binders
          (ConcreteElaboration.localOccurrences targetChecked.val available) with
    | none => simp [targetChecked, targetItemsResult] at targetCompiled
    | some targetItems =>
      simp [targetChecked, targetItemsResult] at targetCompiled
      subst targetBody
      apply anchoredWireSplitRaw_available_route_equiv input wire endpoints target
        term selectedOccurs targetWellFormed wireEnclosesAvailable
        wireEnclosesTarget targetRoute fuel original expanded collapse binders
        originalExact expandedExact sourceItems targetItems sourceItemsResult
        (by simpa [targetChecked] using targetItemsResult) model named sourceOuter
        targetOuter relEnv outerAgrees
      · intro sourceLocal sourceDenotes
        apply anchoredWireSplit_witness_value_of_zero_route input wire witness
          witnessRegion term witnessShape witnessOccurs witnessRoute witnessZero
          original binders fuel sourceItems sourceItemsResult originalExact
          bindersCover binderEnumeration model named sourceOuter sourceLocal relEnv
        simpa [ConcreteElaboration.extendedEnvironment, splitExtendedEnv] using
          sourceDenotes
      · intro targetLocal targetDenotes
        apply anchoredWireSplit_witness_value_of_zero_route targetChecked
          wire.castSucc witness.castSucc witnessRegion term targetWitnessShape
          targetWitnessOccurs targetWitnessRoute targetWitnessDepthProof expanded binders
          fuel targetItems (by simpa [targetChecked] using targetItemsResult)
          expandedExact (anchoredWireSplitRaw_bindersCover input wire endpoints
            target term binders available bindersCover)
          (anchoredWireSplitRaw_binderEnumeration input wire endpoints target term
            binders available binderEnumeration)
          model named
          targetOuter targetLocal relEnv
        simpa [ConcreteElaboration.extendedEnvironment, splitExtendedEnv] using
          targetDenotes

theorem anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target region : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (regionNe : region ≠ target)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (originalExact : (original.extend region).Exact region)
    (expandedExact : (expanded.extend region).Exact region)
    (sourceBefore : ItemSeq signature (original.extend region).length rels)
    (sourceFocus : Item signature (original.extend region).length rels)
    (sourceAfter : ItemSeq signature (original.extend region).length rels)
    (targetBefore : ItemSeq signature (expanded.extend region).length rels)
    (targetFocus : Item signature (expanded.extend region).length rels)
    (targetAfter : ItemSeq signature (expanded.extend region).length rels)
    (beforeEq : sourceBefore = targetBefore.renameWires
      (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap)
    (afterEq : sourceAfter = targetAfter.renameWires
      (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin original.length → model.Carrier)
    (targetOuter : Fin expanded.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (focusEquiv : ∀ sourceRaw targetRaw,
      sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
        originalExact).indexMap = targetRaw →
      (denoteItem model named sourceRaw relEnv sourceFocus ↔
        denoteItem model named targetRaw relEnv targetFocus)) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val original region
          (sourceBefore.append (.cons sourceFocus sourceAfter))) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (anchoredWireSplitRaw input wire endpoints target term) expanded region
          (targetBefore.append (.cons targetFocus targetAfter))) := by
  constructor
  · intro sourceDenotes
    unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
    simp only [denoteRegion_mk] at sourceDenotes ⊢
    obtain ⟨sourceLocal, sourceCast⟩ := sourceDenotes
    let targetLocal := splitTargetLocalEnv collapse wireEnclosesTarget region
      expandedExact originalExact sourceOuter sourceLocal
    refine ⟨targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCast ⊢
    let sourceRaw := splitExtendedEnv original region sourceOuter sourceLocal
    let targetRaw := splitExtendedEnv expanded region targetOuter targetLocal
    have sourceRawItems := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original region))
      (extendWireEnv sourceOuter sourceLocal) relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))).mp sourceCast
    change denoteItemSeq model named sourceRaw relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter)) at sourceRawItems
    have envCollapse := splitExtendedEnv_collapse collapse wireEnclosesTarget
      region expandedExact originalExact sourceOuter sourceLocal
    rw [outerAgrees] at envCollapse
    change sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
      originalExact).indexMap = targetRaw at envCollapse
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded region))
      (extendWireEnv targetOuter targetLocal) relEnv
      (targetBefore.append (.cons targetFocus targetAfter))).mpr
    change denoteItemSeq model named targetRaw relEnv
      (targetBefore.append (.cons targetFocus targetAfter))
    rw [denoteItemSeq_frame] at sourceRawItems ⊢
    have targetBeforeDenotes : denoteItemSeq model named targetRaw relEnv
        targetBefore := by
      rw [beforeEq] at sourceRawItems
      rw [← envCollapse]
      exact (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetBefore).mp
            sourceRawItems.1
    have targetAfterDenotes : denoteItemSeq model named targetRaw relEnv
        targetAfter := by
      rw [afterEq] at sourceRawItems
      rw [← envCollapse]
      exact (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetAfter).mp
            sourceRawItems.2.2
    exact ⟨targetBeforeDenotes,
      (focusEquiv sourceRaw targetRaw envCollapse).mp sourceRawItems.2.1,
      targetAfterDenotes⟩
  · intro targetDenotes
    unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
    simp only [denoteRegion_mk] at targetDenotes ⊢
    obtain ⟨targetLocal, targetCast⟩ := targetDenotes
    let sourceLocal := splitSourceLocalEnvOfNe input wire endpoints target region
      term regionNe targetLocal
    refine ⟨sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetCast ⊢
    let sourceRaw := splitExtendedEnv original region sourceOuter sourceLocal
    let targetRaw := splitExtendedEnv expanded region targetOuter targetLocal
    have targetRawItems := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded region))
      (extendWireEnv targetOuter targetLocal) relEnv
      (targetBefore.append (.cons targetFocus targetAfter))).mp targetCast
    change denoteItemSeq model named targetRaw relEnv
      (targetBefore.append (.cons targetFocus targetAfter)) at targetRawItems
    have envCollapse := splitExtendedEnv_uncollapse_of_ne collapse
      wireEnclosesTarget region regionNe expandedExact originalExact sourceOuter
      targetOuter outerAgrees targetLocal
    change sourceRaw ∘ (collapse.extend wireEnclosesTarget region expandedExact
      originalExact).indexMap = targetRaw at envCollapse
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original region))
      (extendWireEnv sourceOuter sourceLocal) relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))).mpr
    change denoteItemSeq model named sourceRaw relEnv
      (sourceBefore.append (.cons sourceFocus sourceAfter))
    rw [denoteItemSeq_frame] at targetRawItems ⊢
    have sourceBeforeDenotes : denoteItemSeq model named sourceRaw relEnv
        sourceBefore := by
      rw [beforeEq]
      apply (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetBefore).mpr
      rw [envCollapse]
      exact targetRawItems.1
    have sourceAfterDenotes : denoteItemSeq model named sourceRaw relEnv
        sourceAfter := by
      rw [afterEq]
      apply (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget region expandedExact
          originalExact).indexMap sourceRaw relEnv targetAfter).mpr
      rw [envCollapse]
      exact targetRawItems.2.2
    exact ⟨sourceBeforeDenotes,
      (focusEquiv sourceRaw targetRaw envCollapse).mpr targetRawItems.2.1,
      sourceAfterDenotes⟩

/-- Any complete availability kernel lifts through every unchanged compiler
frame between the root and that region. -/
theorem anchoredWireSplitRaw_compileRegion_route_to_available
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target available : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {start : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val start available path)
    {availableTargetPath : List Nat}
    (availableRoute : Diagram.Splice.RegionRoute input.val available target
      availableTargetPath)
    (site : AnchoredAvailableKernel input wire endpoints target available term
      targetWellFormed) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (original : ConcreteElaboration.WireContext input.val)
      (expanded : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term))
      (collapse : SplitContextCollapse input wire endpoints target term
        expanded original)
      (binders : ConcreteElaboration.BinderContext input.val rels)
      (bindersCover : binders.Covers start)
      (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
        input.val binders start)
      (originalExact : (original.extend start).Exact start)
      (expandedExact : (expanded.extend start).Exact start)
      (sourceBody : Region signature original.length rels)
      (targetBody : Region signature expanded.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
        (fuel + 1) start original binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (fuel + 1) start expanded binders = some targetBody)
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceOuter : Fin original.length → model.Carrier)
      (targetOuter : Fin expanded.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels)
      (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter),
      denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody := by
  induction route with
  | here => exact site
  | @step start child available rest hparent position hposition tail ih =>
      intro rels fuel original expanded collapse binders bindersCover
        binderEnumeration originalExact
        expandedExact sourceBody targetBody sourceCompiled targetCompiled model
        named sourceOuter targetOuter relEnv outerAgrees
      have startNe : start ≠ target := by
        intro equality
        subst start
        have targetEnclosesAvailable :=
          ConcreteElaboration.checked_encloses_trans input.property
            (split_direct_child_encloses hparent)
            (regionRoute_encloses input.val input.property tail)
        have availableEnclosesTarget :=
          regionRoute_encloses input.val input.property availableRoute
        have equal := ConcreteElaboration.checked_encloses_antisymm input.property
          targetEnclosesAvailable availableEnclosesTarget
        subst available
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property hparent) (regionRoute_encloses input.val input.property tail)
      have startNeAvailable : start ≠ available := by
        intro equality
        subst start
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property hparent) (regionRoute_encloses input.val input.property tail)
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val start child position hposition
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (original.extend start) binders
            (ConcreteElaboration.localOccurrences input.val start) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (anchoredWireSplitRaw input wire endpoints target term)
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints target term) fuel)
              (expanded.extend start) binders
              (ConcreteElaboration.localOccurrences
                (anchoredWireSplitRaw input wire endpoints target term) start) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          have targetLocalEq :
              ConcreteElaboration.localOccurrences
                  (anchoredWireSplitRaw input wire endpoints target term) start =
                (before ++ .child child :: after).map
                  (splitOldOccurrence input) := by
            rw [anchoredWireSplitRaw_localOccurrences_of_ne input wire endpoints
              target start term startNe, localEq]
          have sourceFramed := sourceItemsResult
          rw [localEq] at sourceFramed
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input.val fuel)
              (original.extend start) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed := targetItemsResult
          rw [targetLocalEq, List.map_append, List.map_cons] at targetFramed
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints target term) fuel)
              (expanded.extend start) binders
              (before.map (splitOldOccurrence input))
              (after.map (splitOldOccurrence input))
              (splitOldOccurrence input (.child child)) targetItems targetFramed
          cases fuel with
          | zero =>
              cases kind : input.val.regions child <;>
                simp [ConcreteElaboration.compileOccurrenceWith?, kind,
                  ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            have beforeMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints target start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent
              (tail.trans availableRoute)
              (childFuel + 1) original expanded collapse binders originalExact
              expandedExact before (by
                intro occurrence member
                rw [localEq]
                simp [member]) beforeAway
            rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
            have beforeEq : sourceBefore = targetBefore.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj beforeMap
            have afterMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints target start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent
              (tail.trans availableRoute)
              (childFuel + 1) original expanded collapse binders originalExact
              expandedExact after (by
                intro occurrence member
                rw [localEq]
                simp [member]) afterAway
            rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
            have afterEq : sourceAfter = targetAfter.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj afterMap
            have childOriginalExact := originalExact.extend_child input.property hparent
            have targetParent :
                ((anchoredWireSplitRaw input wire endpoints target term).regions
                  child).parent? = some start := by
              simpa only [anchoredWireSplitRaw_regions] using hparent
            have childExpandedExact :=
              expandedExact.extend_child targetWellFormed targetParent
            cases childKind : input.val.regions child with
            | sheet => simp [childKind, CRegion.parent?] at hparent
            | cut childParent =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start) binders with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints target term)
                      (childFuel + 1) child (expanded.extend start) binders with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  rw [sourceItemsEq, targetItemsEq]
                  apply anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne input
                    wire endpoints target start term startNe wireEnclosesTarget
                    original expanded collapse originalExact expandedExact
                    sourceBefore (.cut sourceChild) sourceAfter targetBefore
                    (.cut targetChild) targetAfter beforeEq afterEq model named
                    sourceOuter targetOuter relEnv outerAgrees
                  intro sourceRaw targetRaw agrees
                  have childEquiv := ih availableRoute site childFuel
                    (original.extend start)
                    (expanded.extend start)
                    (collapse.extend wireEnclosesTarget start expandedExact
                      originalExact) binders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      bindersCover childKind)
                    (binderEnumeration.cutChild input.property childKind)
                    childOriginalExact childExpandedExact
                    sourceChild targetChild sourceChildResult targetChildResult
                    model named sourceRaw targetRaw relEnv agrees
                  exact not_congr childEquiv
            | bubble childParent arity =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start)
                    (binders.push child arity) with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                change (ConcreteElaboration.compileRegion? signature
                    (anchoredWireSplitRaw input wire endpoints target term)
                    (childFuel + 1) child (expanded.extend start)
                    (binders.push child arity)).bind
                      (fun body => some (Item.bubble arity body)) =
                    some targetFocus at targetFocusCompiled
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints target term)
                      (childFuel + 1) child (expanded.extend start)
                      (binders.push child arity) with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  rw [sourceItemsEq, targetItemsEq]
                  apply anchoredWireSplitRaw_finishRegion_frame_equiv_of_ne input
                    wire endpoints target start term startNe wireEnclosesTarget
                    original expanded collapse originalExact expandedExact
                    sourceBefore (.bubble arity sourceChild) sourceAfter
                    targetBefore (.bubble arity targetChild) targetAfter
                    beforeEq afterEq model named sourceOuter targetOuter relEnv
                    outerAgrees
                  intro sourceRaw targetRaw agrees
                  constructor
                  · rintro ⟨relation, sourceChildDenotes⟩
                    have childEquiv := ih availableRoute site childFuel
                      (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        bindersCover childKind)
                      (binderEnumeration.bubbleChild input.property childKind)
                      childOriginalExact childExpandedExact sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw (relation, relEnv) agrees
                    exact ⟨relation, childEquiv.mp sourceChildDenotes⟩
                  · rintro ⟨relation, targetChildDenotes⟩
                    have childEquiv := ih availableRoute site childFuel
                      (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        bindersCover childKind)
                      (binderEnumeration.bubbleChild input.property childKind)
                      childOriginalExact childExpandedExact sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw (relation, relEnv) agrees
                    exact ⟨relation, childEquiv.mpr targetChildDenotes⟩

end AnchoredWireSoundness

end VisualProof.Rule
