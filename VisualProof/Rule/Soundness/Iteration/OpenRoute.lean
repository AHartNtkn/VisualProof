import VisualProof.Rule.Soundness.Iteration.CanonicalContraction

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

/-- Transport only the list index of an intrinsic path.  The focused
coordinate data is unchanged because the path list is routing evidence, not
part of the focused region itself. -/
def Region.ContextPath.castPath
    {root : Region signature wires rels} {sourcePath targetPath : List Nat}
    (equality : sourcePath = targetPath)
    (witness : Region.ContextPath root sourcePath) :
    Region.ContextPath root targetPath :=
  equality ▸ witness

@[simp] theorem Region.ContextPath.castPath_toFocus_holeWires
    {root : Region signature wires rels} {sourcePath targetPath : List Nat}
    (equality : sourcePath = targetPath)
    (witness : Region.ContextPath root sourcePath) :
    (Region.ContextPath.castPath equality witness).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst targetPath
  rfl

@[simp] theorem Region.ContextPath.castPath_toFocus_holeRels
    {root : Region signature wires rels} {sourcePath targetPath : List Nat}
    (equality : sourcePath = targetPath)
    (witness : Region.ContextPath root sourcePath) :
    (Region.ContextPath.castPath equality witness).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst targetPath
  rfl

theorem Region.ContextPath.castPath_fill
    {root : Region signature wires rels} {sourcePath targetPath : List Nat}
    (equality : sourcePath = targetPath)
    (witness : Region.ContextPath root sourcePath)
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness := Region.ContextPath.castPath equality witness
    targetWitness.toFocus.context.fill
        ((Region.ContextPath.castPath_toFocus_holeRels equality witness).symm ▸
          replacement.castWiresEq
            (Region.ContextPath.castPath_toFocus_holeWires equality
              witness).symm) =
      witness.toFocus.context.fill replacement := by
  subst targetPath
  rfl

theorem Region.ContextPath.fill_of_eq
    {root : Region signature wires rels} {path : List Nat}
    {source target : Region.ContextPath root path}
    (equality : source = target)
    (replacement : Region signature source.toFocus.holeWires
      source.toFocus.holeRels) :
    target.toFocus.context.fill
        ((congrArg (fun witness => witness.toFocus.holeRels)
            equality) ▸
          replacement.castWiresEq
            (congrArg (fun witness => witness.toFocus.holeWires)
              equality)) =
      source.toFocus.context.fill replacement := by
  subst target
  rfl

def Region.transportEq
    (wireEquality : sourceWires = targetWires)
    (relsEquality : sourceRels = targetRels)
    (region : Region signature sourceWires sourceRels) :
    Region signature targetWires targetRels :=
  relsEquality ▸ region.castWiresEq wireEquality

@[simp] theorem Region.transportEq_trans
    (firstWire : sourceWires = middleWires)
    (secondWire : middleWires = targetWires)
    (firstRels : sourceRels = middleRels)
    (secondRels : middleRels = targetRels)
    (region : Region signature sourceWires sourceRels) :
    Region.transportEq secondWire secondRels
        (Region.transportEq firstWire firstRels region) =
      Region.transportEq (firstWire.trans secondWire)
        (firstRels.trans secondRels) region := by
  subst middleWires
  subst targetWires
  subst middleRels
  subst targetRels
  rfl

theorem Region.transportEq_proof_irrel
    (firstWire secondWire : sourceWires = targetWires)
    (firstRels secondRels : sourceRels = targetRels)
    (region : Region signature sourceWires sourceRels) :
    Region.transportEq firstWire firstRels region =
      Region.transportEq secondWire secondRels region := by
  subst targetWires
  subst targetRels
  rfl

/-- Filling a nested intrinsic path is the same operation as filling the
inner context and then the outer context. -/
theorem Region.ContextPath.nest_fill
    {root : Region signature wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath)
    (replacement : Region signature inner.toFocus.holeWires
      inner.toFocus.holeRels) :
    (outer.nest inner).toFocus.context.fill
        ((outer.nest_toFocus_holeRels inner).symm ▸
          replacement.castWiresEq
            (outer.nest_toFocus_holeWires inner).symm) =
      outer.toFocus.context.fill
        (inner.toFocus.context.fill replacement) := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction =>
      simpa only [Region.ContextPath.nest, Region.ContextPath.toFocus,
        DiagramContext.fill] using congrArg
          (fun child => Region.mk _ (focus.before.append
            (ItemSeq.cons (.cut child) focus.after)))
          (induction inner replacement)
  | bubble focus atIndex isBubble nested induction =>
      simpa only [Region.ContextPath.nest, Region.ContextPath.toFocus,
        DiagramContext.fill] using congrArg
          (fun child => Region.mk _ (focus.before.append
            (ItemSeq.cons (.bubble _ child) focus.after)))
          (induction inner replacement)

/-- The anchor-relative witness retained by the open contraction certificate,
when nested under the root-to-anchor compiler path, is exactly the
authoritative coalesced-open compiler witness at the executor's target. -/
structure ProperIterationOpenTargetAlignment
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) where
  full : Region.ContextPath
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).elaborate.body
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).path
  full_eq_target : full =
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).intrinsicPath
  holeWires_eq : full.toFocus.holeWires =
    certificate.witness.toFocus.holeWires
  holeRels_eq : full.toFocus.holeRels =
    certificate.witness.toFocus.holeRels

/-- The proper iteration target remains nested in the coalesced frame. -/
theorem ProperIterationOpenAnchorContraction.target_ne_root_fact
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) :
    target ≠ (iterationInput input selection target).coalesceFrameRaw.root := by
  exact certificate.target_ne_root

/-- Coordinate transport from the executor's coalesced-open target focus to
the contraction certificate's route-relative focus. -/
noncomputable def ProperIterationOpenTargetAlignment.sourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot}
    (alignment : ProperIterationOpenTargetAlignment certificate) :
    FiniteEquiv
      (Fin (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires)
      (Fin certificate.witness.toFocus.holeWires) :=
  (FiniteEquiv.finCast (congrArg
    (fun witness => witness.toFocus.holeWires)
    alignment.full_eq_target).symm).trans
    (FiniteEquiv.finCast alignment.holeWires_eq)

def ProperIterationOpenTargetAlignment.sourceRelsEq
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    {certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot}
    (alignment : ProperIterationOpenTargetAlignment certificate) :
    (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).focus.holeRels = certificate.witness.toFocus.holeRels :=
  (congrArg (fun witness => witness.toFocus.holeRels)
    alignment.full_eq_target).symm.trans alignment.holeRels_eq

/-- Exact inherited-wire transport from the canonical coalesced-open target
leaf to the route-relative terminal leaf retained by the contraction. -/
noncomputable def ProperIterationOpenAnchorContraction.terminalSourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) :
    FiniteEquiv
      (Fin (Splice.Input.compiledSpliceCoalescedOpenView
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).focus.holeWires)
      (Fin certificate.witness.toFocus.holeWires) :=
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot certificate.target_ne_root
  let terminalEquiv :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf certificate.witness
      certificate.sourceTerminalLeaf
  (FiniteEquiv.finCast sourceLeaf.inheritedLength.symm).trans
    (terminalEquiv.trans
      (FiniteEquiv.finCast certificate.sourceTerminalLeaf.inheritedLength))

/-- The terminal compiler coordinate retained by the contraction is exactly
the intrinsic hole coordinate of the executor's root-to-target context. -/
theorem ProperIterationOpenAnchorContraction.terminalSourceWire_eq_sourceWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot)
    (alignment : ProperIterationOpenTargetAlignment certificate) :
    certificate.terminalSourceWire = alignment.sourceWire := by
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot certificate.target_ne_root
  let terminalEquiv :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf certificate.witness
      certificate.sourceTerminalLeaf
  have listsEq : certificate.sourceTerminalLeaf.inheritedWires =
      sourceLeaf.inheritedWires :=
    certificate.sourceTerminalWires_eq.symm.trans
      certificate.sourceTerminalCanonical
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  let sourceIndex := Fin.cast sourceLeaf.inheritedLength.symm index
  let certificateIndex := Fin.cast
    (congrArg List.length listsEq).symm sourceIndex
  have terminalSpec :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
      sourceView.intrinsicPath sourceLeaf certificate.witness
      certificate.sourceTerminalLeaf
      sourceIndex
  have reference := List.get_of_eq listsEq certificateIndex
  have terminalGet : certificate.sourceTerminalLeaf.inheritedWires.get
        (terminalEquiv sourceIndex) =
      certificate.sourceTerminalLeaf.inheritedWires.get certificateIndex :=
    terminalSpec.trans (by
      simpa [sourceIndex, certificateIndex, List.get_eq_getElem] using
        reference.symm)
  have nodup := certificate.sourceTerminalLeaf.wiresExact.nodup
  rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at nodup
  have indexEq := (List.getElem_inj nodup.1).mp terminalGet
  have terminalVal :
      (terminalEquiv sourceIndex).val =
        index.val := by
    simpa [terminalEquiv, sourceIndex, certificateIndex] using indexEq
  change (certificate.terminalSourceWire index).val =
    (alignment.sourceWire index).val
  simpa [ProperIterationOpenAnchorContraction.terminalSourceWire,
    ProperIterationOpenTargetAlignment.sourceWire, terminalEquiv,
    FiniteEquiv.trans] using terminalVal

/-- Filling the contraction's anchor-relative replacement reconstructs the
same complete source body as filling the executor's canonical target context
with that replacement in target coordinates. -/
theorem ProperIterationOpenAnchorContraction.modifiedBody_eq_targetFill
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot)
    (alignment : ProperIterationOpenTargetAlignment certificate) :
    let anchorView := iterationCoalescedOpenAnchorView input selection target
      hadmissible sourceBoundary sourceRoot
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot
    let replacementAtSource : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels :=
      alignment.sourceRelsEq.symm ▸
        certificate.replacement.renameWires alignment.sourceWire.symm
    anchorView.focus.context.fill
        (certificate.witness.toFocus.context.fill certificate.replacement) =
      sourceView.focus.context.fill replacementAtSource := by
  dsimp only
  rcases alignment with ⟨alignmentFull, alignmentTarget,
    alignmentWires, alignmentRels⟩
  let anchorView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let nested := anchorView.intrinsicPath.nest certificate.witness
  have pathEq : anchorView.path ++ certificate.path = sourceView.path :=
    iterationCoalescedOpenAnchorRoute_targetPath input selection target
      hadmissible sourceBoundary sourceRoot certificate.route
  let full := Region.ContextPath.castPath pathEq nested
  have fullEq : full = alignmentFull :=
    Region.ContextPath.unique full alignmentFull
  have fullHoleWires : full.toFocus.holeWires =
      certificate.witness.toFocus.holeWires := by
    simp [full, nested]
    rfl
  have fullHoleRels : full.toFocus.holeRels =
      certificate.witness.toFocus.holeRels := by
    simp [full, nested]
    rfl
  have alignmentHoleWires : alignmentWires =
      (congrArg (fun witness => witness.toFocus.holeWires)
        fullEq.symm).trans fullHoleWires := Subsingleton.elim _ _
  have alignmentHoleRels : alignmentRels =
      (congrArg (fun witness => witness.toFocus.holeRels)
        fullEq.symm).trans fullHoleRels := Subsingleton.elim _ _
  let nestedReplacement : Region signature nested.toFocus.holeWires
      nested.toFocus.holeRels :=
    Region.transportEq
      (anchorView.intrinsicPath.nest_toFocus_holeWires
        certificate.witness).symm
      (anchorView.intrinsicPath.nest_toFocus_holeRels
        certificate.witness).symm certificate.replacement
  let fullReplacement : Region signature full.toFocus.holeWires
      full.toFocus.holeRels :=
    Region.transportEq
      (Region.ContextPath.castPath_toFocus_holeWires pathEq nested).symm
      (Region.ContextPath.castPath_toFocus_holeRels pathEq nested).symm
      nestedReplacement
  have fullFill : full.toFocus.context.fill fullReplacement =
      anchorView.focus.context.fill
        (certificate.witness.toFocus.context.fill
          certificate.replacement) := by
    have castFill := Region.ContextPath.castPath_fill pathEq nested
      nestedReplacement
    have nestedFill := Region.ContextPath.nest_fill
      anchorView.intrinsicPath certificate.witness certificate.replacement
    simpa only [fullReplacement, nestedReplacement, Region.transportEq,
      full, nested] using
      castFill.trans nestedFill
  let alignmentReplacement : Region signature
      alignmentFull.toFocus.holeWires alignmentFull.toFocus.holeRels :=
    Region.transportEq alignmentWires.symm alignmentRels.symm
      certificate.replacement
  have alignmentFill : alignmentFull.toFocus.context.fill
      alignmentReplacement = full.toFocus.context.fill fullReplacement := by
    have transported := Region.ContextPath.fill_of_eq fullEq fullReplacement
    have replacementEq : alignmentReplacement =
        Region.transportEq
          (congrArg (fun witness => witness.toFocus.holeWires) fullEq)
          (congrArg (fun witness => witness.toFocus.holeRels) fullEq)
          fullReplacement := by
      change Region.transportEq alignmentWires.symm alignmentRels.symm
          certificate.replacement =
        Region.transportEq
          (congrArg (fun witness => witness.toFocus.holeWires) fullEq)
          (congrArg (fun witness => witness.toFocus.holeRels) fullEq)
          (Region.transportEq
            (Region.ContextPath.castPath_toFocus_holeWires pathEq nested).symm
            (Region.ContextPath.castPath_toFocus_holeRels pathEq nested).symm
            (Region.transportEq
              (anchorView.intrinsicPath.nest_toFocus_holeWires
                certificate.witness).symm
              (anchorView.intrinsicPath.nest_toFocus_holeRels
                certificate.witness).symm certificate.replacement))
      simp only [Region.transportEq_trans]
      exact Region.transportEq_proof_irrel _ _ _ _ certificate.replacement
    rw [replacementEq]
    exact transported
  let targetWireEq := congrArg
    (fun witness => witness.toFocus.holeWires) alignmentTarget
  let targetRelsEq := congrArg
    (fun witness => witness.toFocus.holeRels) alignmentTarget
  let targetReplacement : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    Region.transportEq targetWireEq targetRelsEq alignmentReplacement
  have sourceWireInv :
      (ProperIterationOpenTargetAlignment.sourceWire
        (⟨alignmentFull, alignmentTarget, alignmentWires,
          alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm =
        FiniteEquiv.finCast (alignmentWires.symm.trans targetWireEq) := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  have targetReplacementEq : targetReplacement =
      (ProperIterationOpenTargetAlignment.sourceRelsEq
          (⟨alignmentFull, alignmentTarget, alignmentWires,
            alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm ▸
        certificate.replacement.renameWires
          (ProperIterationOpenTargetAlignment.sourceWire
            (⟨alignmentFull, alignmentTarget, alignmentWires,
              alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm := by
    rw [sourceWireInv]
    simp only [FiniteEquiv.finCast]
    have renamedAsTransport :
        ((ProperIterationOpenTargetAlignment.sourceRelsEq
          (⟨alignmentFull, alignmentTarget, alignmentWires,
            alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm ▸
          certificate.replacement.renameWires
            (Fin.cast (alignmentWires.symm.trans targetWireEq))) =
          Region.transportEq (alignmentWires.symm.trans targetWireEq)
            ((ProperIterationOpenTargetAlignment.sourceRelsEq
              (⟨alignmentFull, alignmentTarget, alignmentWires,
                alignmentRels⟩ : ProperIterationOpenTargetAlignment
                  certificate)).symm) certificate.replacement := by
      exact congrArg
        (fun region =>
          (ProperIterationOpenTargetAlignment.sourceRelsEq
            (⟨alignmentFull, alignmentTarget, alignmentWires,
              alignmentRels⟩ : ProperIterationOpenTargetAlignment
                certificate)).symm ▸ region)
        (Region.castWiresEq_eq_renameWires
          (alignmentWires.symm.trans targetWireEq)
          certificate.replacement).symm
    calc
      targetReplacement = Region.transportEq
          (alignmentWires.symm.trans targetWireEq)
          ((ProperIterationOpenTargetAlignment.sourceRelsEq
            (⟨alignmentFull, alignmentTarget, alignmentWires,
              alignmentRels⟩ : ProperIterationOpenTargetAlignment
                certificate)).symm) certificate.replacement := by
        dsimp only [targetReplacement]
        simp only [alignmentReplacement, Region.transportEq_trans]
        exact Region.transportEq_proof_irrel _ _ _ _ certificate.replacement
      _ = _ := renamedAsTransport.symm
  have targetFillRaw := Region.ContextPath.fill_of_eq alignmentTarget
    alignmentReplacement
  have targetFill : sourceView.focus.context.fill
        ((ProperIterationOpenTargetAlignment.sourceRelsEq
            (⟨alignmentFull, alignmentTarget, alignmentWires,
              alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm ▸
          certificate.replacement.renameWires
            (ProperIterationOpenTargetAlignment.sourceWire
              (⟨alignmentFull, alignmentTarget, alignmentWires,
                alignmentRels⟩ : ProperIterationOpenTargetAlignment certificate)).symm) =
      alignmentFull.toFocus.context.fill alignmentReplacement := by
    rw [← targetReplacementEq]
    exact targetFillRaw
  exact fullFill.symm.trans (alignmentFill.symm.trans targetFill.symm)

/-- The contraction certificate and the executor's canonical coalesced-open
compiler choose the same concrete outer-wire map at the insertion site. -/
theorem ProperIterationOpenAnchorContraction.actualWire_eq_compilerOuterWire
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot certificate.target_ne_root
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    certificate.terminalSourceWire.trans certificate.actualWire =
      Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.target_ne_root
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let terminalEquiv :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf certificate.witness
      certificate.sourceTerminalLeaf
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf)
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  apply (List.getElem_inj (by
    have nodup := host.compilerLeaf.wiresExact.nodup
    rw [ConcreteElaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1)).mp
  change host.compilerLeaf.inheritedWires.get
      (Fin.cast host.compilerLeaf.inheritedLength.symm
        ((certificate.terminalSourceWire.trans certificate.actualWire)
          index)) =
    host.compilerLeaf.inheritedWires.get
      (Fin.cast host.compilerLeaf.inheritedLength.symm
        (canonicalWire index))
  have certificateSpec := certificate.actualWireSpec
    (certificate.terminalSourceWire index)
  have terminalSpec :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
      sourceView.intrinsicPath sourceLeaf certificate.witness
      certificate.sourceTerminalLeaf
      (Fin.cast sourceLeaf.inheritedLength.symm index)
  have canonicalSpec := compilerLeafOuterWire_sameSite_spec
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      index
  have certificateTerminal :
      host.compilerLeaf.inheritedWires.get
          (Fin.cast host.compilerLeaf.inheritedLength.symm
            (certificate.actualWire (certificate.terminalSourceWire index))) =
        certificate.sourceTerminalLeaf.inheritedWires.get
          (Fin.cast certificate.sourceTerminalLeaf.inheritedLength.symm
            (certificate.terminalSourceWire index)) := by
    simpa [certificate.sourceTerminalWires_eq] using certificateSpec
  have terminalCoordinate :
      certificate.sourceTerminalLeaf.inheritedWires.get
          (Fin.cast certificate.sourceTerminalLeaf.inheritedLength.symm
            (certificate.terminalSourceWire index)) =
        sourceLeaf.inheritedWires.get
          (Fin.cast sourceLeaf.inheritedLength.symm index) := by
    simpa [ProperIterationOpenAnchorContraction.terminalSourceWire,
      terminalEquiv, FiniteEquiv.trans] using terminalSpec
  simpa [canonicalWire, FiniteEquiv.trans] using
    certificateTerminal.trans (terminalCoordinate.trans canonicalSpec.symm)

private theorem pulledCastWires_eq
    {sourceRels hostRels : Theory.RelCtx}
    (hrels : sourceRels = hostRels)
    {sourceWires hostWires normalizedWires : Nat}
    (hlen : hostWires = normalizedWires)
    (raw : Region signature hostWires hostRels)
    (sourceHostWire : FiniteEquiv (Fin sourceWires) (Fin hostWires))
    (canonicalWire : FiniteEquiv (Fin sourceWires) (Fin normalizedWires))
    (wireEq : canonicalWire =
      sourceHostWire.trans (FiniteEquiv.finCast hlen)) :
    (hrels.symm ▸ raw.castWiresEq hlen).renameWires canonicalWire.symm =
      (hrels.symm ▸ raw).renameWires sourceHostWire.symm := by
  subst hostRels
  subst normalizedWires
  subst canonicalWire
  rfl

private theorem spliceAt_castOuter
    {sourceOuter targetOuter localWires materialWires : Nat}
    (equality : sourceOuter = targetOuter)
    (items : ItemSeq signature (sourceOuter + localWires) rels)
    (material : Region signature materialWires materialRels)
    (wire : Fin materialWires → Fin (sourceOuter + localWires))
    (relation : RelationRenaming materialRels rels) :
    Region.spliceAt localWires
        (items.castWiresEq
          (congrArg (fun outer => outer + localWires) equality))
        material
        (fun index => Fin.cast
          (congrArg (fun outer => outer + localWires) equality) (wire index))
        relation =
      (Region.spliceAt localWires items material wire relation).castWiresEq
        equality := by
  subst targetOuter
  rfl

/-- Pulling iteration's host-normalized executable splice back through the
canonical coalesced-open compiler wire is definitionally the source actual
used by the generic splice semantics. -/
theorem iterationActualSplice_pulled_eq_compiled
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hnested : target ≠
      (iterationInput input selection target).coalesceFrameRaw.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (hrels : (Splice.Input.compiledSpliceCoalescedOpenView
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).focus.holeRels =
        (Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot hnested
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let sourceHostInherited :=
      Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
    let canonicalWire := Splice.Input.compilerLeafOuterWire
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
        sourceHostInherited
    let actual : Region signature host.focus.holeWires host.focus.holeRels :=
      iterationActualSpliceOfNonempty input selection target hadmissible
        hnonempty
    (hrels.symm ▸ actual).renameWires canonicalWire.symm =
        Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
          spliceInput.plugLayout hadmissible sourceBoundary sourceRoot hnested
          hnonempty hrels := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot hnested
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let sourceHostInherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
  let sourceHostWire :=
    (Splice.Input.compilerLeafOuterWire sourceView.intrinsicPath sourceLeaf
      host.intrinsicPath host.compilerLeaf sourceHostInherited).trans
      (FiniteEquiv.finCast host.compilerLeaf.inheritedLength).symm
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      sourceHostInherited
  let material := ConcreteElaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let rawSource := Region.spliceAt
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
    (host.compilerLeaf.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site))
    material
    (fun index => Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site)
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index))
    (spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty)
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty
  have actualEq : iterationActualSpliceOfNonempty input selection target
      hadmissible hnonempty =
        rawSource.castWiresEq host.compilerLeaf.inheritedLength := by
    let localWires := (ConcreteElaboration.exactScopeWires
      spliceInput.coalesceFrameRaw spliceInput.site).length
    let items := host.compilerLeaf.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site)
    let wire := fun index => Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires spliceInput.site)
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index)
    simpa [iterationActualSpliceOfNonempty, spliceInput, host, pattern,
      rawSource, localWires, items, wire,
      Region.castWiresEq_proof_irrel] using
      (spliceAt_castOuter (signature := signature)
        host.compilerLeaf.inheritedLength items material wire
        (spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
          hnonempty))
  have wireEq : canonicalWire = sourceHostWire.trans
      (FiniteEquiv.finCast host.compilerLeaf.inheritedLength) := by
    apply FiniteEquiv.ext
    intro index
    rfl
  change (hrels.symm ▸ actual).renameWires canonicalWire.symm =
    (hrels.symm ▸ rawSource).renameWires sourceHostWire.symm
  rw [show actual = rawSource.castWiresEq
    host.compilerLeaf.inheritedLength from actualEq]
  exact pulledCastWires_eq hrels host.compilerLeaf.inheritedLength rawSource
    sourceHostWire canonicalWire wireEq

private theorem castBack_renameRelations_eq
    {sourceRels targetRels : Theory.RelCtx}
    (hrels : sourceRels = targetRels)
    (region : Region signature wires sourceRels) :
    hrels.symm ▸
        region.renameRelations (Splice.Input.relationRenamingOfEq hrels) =
      region := by
  subst targetRels
  simp [Splice.Input.relationRenamingOfEq, Region.renameRelations_id]

private def RegionIso.castTargetEq
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region signature sourceWires rels}
    {target target' : Region signature targetWires rels}
    (equality : target = target')
    (iso : RegionIso signature wire rels source target) :
    RegionIso signature wire rels source target' := by
  subst target'
  exact iso

/-- The route-relative logical replacement, transported to the canonical
coalesced-open target focus, is intrinsically the exact source region used by
the executable splice. -/
theorem ProperIterationOpenAnchorContraction.replacementAtSource_iso_compiled
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot)
    (alignment : ProperIterationOpenTargetAlignment certificate) :
    let spliceInput := iterationInput input selection target
    let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
      hadmissible sourceBoundary sourceRoot
    let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
      hadmissible sourceBoundary sourceRoot certificate.target_ne_root
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let canonicalWire := Splice.Input.compilerLeafOuterWire
      sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          sourceView.intrinsicPath sourceLeaf host.intrinsicPath
            host.compilerLeaf)
    let sourceRelsEq := alignment.sourceRelsEq
    let hrels := sourceRelsEq.trans certificate.actualRelsEq
    let replacementAtSource : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels :=
      sourceRelsEq.symm ▸
        certificate.replacement.renameWires
          certificate.terminalSourceWire.symm
    RegionIso signature (canonicalWire.trans canonicalWire.symm)
      sourceView.focus.holeRels replacementAtSource
      (Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
        spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
        certificate.target_ne_root hnonempty hrels) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.target_ne_root
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let sourceRelsEq := alignment.sourceRelsEq
  let hrels := sourceRelsEq.trans certificate.actualRelsEq
  let sourceWire := certificate.terminalSourceWire
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath
          host.compilerLeaf)
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfNonempty input selection target hadmissible
      hnonempty
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸
      certificate.replacement.renameWires sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.target_ne_root hnonempty hrels
  have replacementToRaw := RegionIso.transportedReplacement_to_actual
    sourceRelsEq certificate.actualRelsEq sourceWire.symm
      certificate.actualWire certificate.replacement actual
      certificate.actualIso
  have wireEq : sourceWire.trans certificate.actualWire = canonicalWire := by
    simpa [sourceWire, canonicalWire, sourceView, sourceLeaf, host,
      spliceInput] using
        certificate.actualWire_eq_compilerOuterWire
  have sourceSymm : sourceWire.symm.symm = sourceWire := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [sourceSymm] at replacementToRaw
  rw [wireEq] at replacementToRaw
  have compiledToRaw := RegionIso.pulledBack_to_actual hrels canonicalWire
    actual
  have pulledEq : (hrels.symm ▸ actual).renameWires canonicalWire.symm =
      compiledActual := by
    simpa [spliceInput, sourceView, sourceLeaf, host, hrels, actual,
      compiledActual, canonicalWire] using
      iterationActualSplice_pulled_eq_compiled input selection target
        hadmissible sourceBoundary sourceRoot certificate.target_ne_root
        hnonempty hrels
  dsimp only at compiledToRaw
  have renamedPulledEq := congrArg
    (fun region : Region signature sourceView.focus.holeWires
        sourceView.focus.holeRels =>
      region.renameRelations (Splice.Input.relationRenamingOfEq hrels))
    pulledEq
  have compiledToRaw' : RegionIso signature canonicalWire
      host.focus.holeRels
      (compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels)) actual := by
    rw [← pulledEq]
    exact compiledToRaw
  have combined := replacementToRaw.trans compiledToRaw'.symm
  have normalized := RegionIso.of_renamed_relEq hrels
    (canonicalWire.trans canonicalWire.symm) replacementAtSource
    (compiledActual.renameRelations
      (Splice.Input.relationRenamingOfEq hrels))
      (by simpa [replacementAtSource, sourceRelsEq, sourceWire, hrels] using
        combined)
  have castBack : hrels.symm ▸
      compiledActual.renameRelations
        (Splice.Input.relationRenamingOfEq hrels) = compiledActual :=
    castBack_renameRelations_eq hrels compiledActual
  simpa [spliceInput, sourceView, sourceLeaf, host, canonicalWire,
    sourceRelsEq, hrels, replacementAtSource, compiledActual] using
    RegionIso.castTargetEq castBack normalized

/-- Complete exact target alignment chosen from the certificate's retained
concrete route. -/
theorem properIterationOpenTargetAlignment_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot) :
    Nonempty (ProperIterationOpenTargetAlignment certificate) := by
  let anchorView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let targetView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let nested := anchorView.intrinsicPath.nest certificate.witness
  have pathEq : anchorView.path ++ certificate.path = targetView.path :=
    iterationCoalescedOpenAnchorRoute_targetPath input selection target
      hadmissible sourceBoundary sourceRoot certificate.route
  let full : Region.ContextPath
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).elaborate.body targetView.path :=
    Region.ContextPath.castPath pathEq nested
  have fullEq : full = targetView.intrinsicPath :=
    Region.ContextPath.unique full targetView.intrinsicPath
  have holeWiresEq : full.toFocus.holeWires =
      certificate.witness.toFocus.holeWires := by
    simp [full, nested]
    rfl
  have holeRelsEq : full.toFocus.holeRels =
      certificate.witness.toFocus.holeRels := by
    simp [full, nested]
    rfl
  exact ⟨{
    full := full
    full_eq_target := fullEq
    holeWires_eq := holeWiresEq
    holeRels_eq := holeRelsEq
  }⟩

/-- Proper nested iteration with a nonempty binder spine is an equivalence
between the canonical coalesced source and the exact executable splice source.
This is the ordered-open semantic result consumed by receipt soundness. -/
theorem properIterationOpen_compiledSource_equiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationOpenAnchorContraction input selection target
      hadmissible hnonempty sourceBoundary sourceRoot)
    (alignment : ProperIterationOpenTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    denoteOpen model named
        (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (iterationInput input selection target) hadmissible sourceBoundary
          sourceRoot).elaborate args ↔
      denoteOpen model named
        (Splice.Input.compiledSpliceNestedSourceOfNonempty
          (iterationInput input selection target)
          (iterationInput input selection target).plugLayout hadmissible
          sourceBoundary sourceRoot certificate.target_ne_root hnonempty) args := by
  let spliceInput := iterationInput input selection target
  let source := (Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot).elaborate
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView spliceInput
    hadmissible sourceBoundary sourceRoot
  let sourceLeaf := Splice.Input.compiledSpliceCoalescedNestedLeaf spliceInput
    hadmissible sourceBoundary sourceRoot certificate.target_ne_root
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let canonicalWire := Splice.Input.compilerLeafOuterWire
    sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        sourceView.intrinsicPath sourceLeaf host.intrinsicPath host.compilerLeaf)
  let sourceRelsEq := alignment.sourceRelsEq
  let hrels := sourceRelsEq.trans certificate.actualRelsEq
  let replacementAtSource : Region signature sourceView.focus.holeWires
      sourceView.focus.holeRels :=
    sourceRelsEq.symm ▸
      certificate.replacement.renameWires alignment.sourceWire.symm
  let compiledActual :=
    Splice.Input.compiledSpliceCoalescedActualOfNonempty spliceInput
      spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
      certificate.target_ne_root hnonempty hrels
  let anchorView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let modifiedBody := anchorView.focus.context.fill
    (certificate.witness.toFocus.context.fill certificate.replacement)
  let compiledBody := sourceView.focus.context.fill compiledActual
  have replacementIso : RegionIso signature
      (canonicalWire.trans canonicalWire.symm) sourceView.focus.holeRels
      replacementAtSource compiledActual := by
    have core := certificate.replacementAtSource_iso_compiled alignment
    simpa [spliceInput, sourceView, sourceLeaf, host, canonicalWire,
      sourceRelsEq, hrels, replacementAtSource, compiledActual,
      certificate.terminalSourceWire_eq_sourceWire alignment] using core
  have replacementEquiv : ∀
      (environment : Fin sourceView.focus.holeWires → model.Carrier)
      (relations : RelEnv model.Carrier sourceView.focus.holeRels),
      denoteRegion model named environment relations replacementAtSource ↔
        denoteRegion model named environment relations compiledActual := by
    intro environment relations
    apply replacementIso.denotation model named environment environment
      relations
    intro index
    change environment (canonicalWire.symm (canonicalWire index)) =
      environment index
    exact congrArg environment (canonicalWire.left_inv index)
  have bodyEq := certificate.modifiedBody_eq_targetFill alignment
  have bodyEquiv : ∀ environment : Fin source.externalClasses →
      model.Carrier,
      denoteRegion (relCtx := []) model named environment PUnit.unit
          modifiedBody ↔
        denoteRegion (relCtx := []) model named environment PUnit.unit
          compiledBody := by
    intro environment
    dsimp only [modifiedBody, compiledBody]
    rw [bodyEq]
    exact DiagramContext.fill_equiv sourceView.focus.context
      replacementAtSource compiledActual model named environment PUnit.unit
      replacementEquiv
  have whole := certificate.wholeOpen_equiv model named args
  have replacements :
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody) args ↔
        denoteOpen model named (Splice.replaceOpenBody source compiledBody)
          args := by
    constructor
    · exact Splice.denote_replaceOpenBody_mono source modifiedBody compiledBody
        model named args (fun environment => (bodyEquiv environment).mp)
    · exact Splice.denote_replaceOpenBody_mono source compiledBody modifiedBody
        model named args (fun environment => (bodyEquiv environment).mpr)
  obtain ⟨_terminalRels, terminalBinders⟩ :=
    Splice.Input.compiledSpliceCoalescedHost_terminalLexical spliceInput
      hadmissible sourceBoundary sourceRoot certificate.target_ne_root
  have actualIso := Splice.Input.compiledSpliceNestedActualIsoOfNonempty
    spliceInput spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
    certificate.target_ne_root hnonempty hrels terminalBinders
  exact whole.trans (replacements.trans
    (by simpa [Splice.Input.compiledSpliceNestedCoalescedActualOpenOfNonempty,
      source, sourceView, compiledBody, compiledActual, spliceInput] using
      actualIso.denoteOpen_iff model named args))

/-- Result-facing form of proper nested nonempty iteration.  The theorem
retains the caller's ordered boundary and compares directly with the canonical
checked output open diagram of the successful splice. -/
theorem properIterationOpen_output_equiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {result : CheckedDiagram signature}
    (hsplice : Splice.Input.spliceChecked signature
      (iterationInput input selection target) = .ok result)
    {sourceBoundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (certificate : ProperIterationOpenAnchorContraction input selection target
      (Splice.Input.spliceChecked_sound hsplice).2.1 hnonempty sourceBoundary
      sourceRoot)
    (alignment : ProperIterationOpenTargetAlignment certificate)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin sourceBoundary.length → model.Carrier) :
    let source : OpenProofState signature := {
      diagram := input
      boundary := sourceBoundary
      boundary_root_scoped := sourceRoot
    }
    let output := Splice.Input.PlugLayout.checkedOutputOpenRoot
      (iterationInput input selection target)
      (iterationInput input selection target).plugLayout
      (Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary sourceRoot
    source.denote model named args ↔
      output.denote model named
        (args ∘ Fin.cast (by
          change (sourceBoundary.map _).length = sourceBoundary.length
          exact List.length_map (as := sourceBoundary) _)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let hadmissible := (Splice.Input.spliceChecked_sound hsplice).2.1
  let source : OpenProofState signature := {
    diagram := input
    boundary := sourceBoundary
    boundary_root_scoped := sourceRoot
  }
  let coalesced := Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
    hadmissible sourceBoundary sourceRoot
  let output := Splice.Input.PlugLayout.checkedOutputOpenRoot spliceInput
    spliceInput.plugLayout hadmissible sourceBoundary sourceRoot
  let coalescedArity : coalesced.val.boundary.length =
      sourceBoundary.length := by
    change (sourceBoundary.map _).length = sourceBoundary.length
    exact List.length_map (as := sourceBoundary) _
  let compilerArgs : Fin coalesced.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast coalescedArity
  have frameIso := iterationCoalescedOpenIso input selection target
    sourceBoundary
  have frameEquiv := frameIso.denote_iff coalesced.property
    source.asCheckedOpen.property model named compilerArgs
  have sourceToCoalesced : source.denote model named args ↔
      coalesced.denote model named compilerArgs := by
    symm
    simpa [source, coalesced, compilerArgs, coalescedArity,
      CheckedOpenDiagram.denote, OpenProofState.denote, Function.comp_def] using
      frameEquiv
  have contraction := properIterationOpen_compiledSource_equiv certificate
    alignment model named compilerArgs
  have hsite : spliceInput.site ≠ spliceInput.frame.val.root := by
    simpa [spliceInput, Splice.Input.coalesceFrameRaw] using
      certificate.target_ne_root
  have executable := Splice.Input.spliceChecked_open_denotation_iff
    spliceInput hsplice sourceBoundary sourceRoot model named compilerArgs
  dsimp only at executable
  rw [denoteOpen_castArity] at executable
  exact sourceToCoalesced.trans (contraction.trans
    (by simpa [spliceInput, hadmissible, coalesced, output, compilerArgs,
      coalescedArity, Splice.Input.compiledSpliceSourceOpen,
      hsite, hnonempty, CheckedOpenDiagram.denote,
      Function.comp_def] using executable))

end VisualProof.Rule.IterationSoundness
