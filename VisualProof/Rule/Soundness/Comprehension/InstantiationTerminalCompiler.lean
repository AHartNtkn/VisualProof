import VisualProof.Rule.Soundness.Comprehension.InstantiationTargetInvariant

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A denoting focused compiler block after a nonempty-spine splice contains
the terminal pattern block prepared by the authoritative splice compiler. -/
theorem terminalPrepared_denotes_of_output
    (input : Concrete.Splice.Input )
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (host : Concrete.Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (denotes : denoteItemSeq model  env relEnv outputLeaf.items) :
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let sourceEnv := targetEnv ∘ combined
    let terminalRelations : RelationRenaming
        patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
      fun relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation)
    let patternPrepared :=
      (patternLeaf.items.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        terminalRelations
    denoteItemSeq model  sourceEnv relEnv patternPrepared := by
  dsimp only
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  let patternPrepared :=
    (patternLeaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations terminalRelations
  have targetDenotes : denoteItemSeq model  targetEnv relEnv
      (outputLeaf.items.castWiresEq targetEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires,
      denoteItemSeq_renameWires]
    simpa [targetEnv, targetEq, Function.comp_def] using denotes
  have itemsIso := layout.compiledSiteItemsIsoOfNonempty  input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty
  have preparedDenotes : denoteItemSeq model  sourceEnv relEnv
      (hostPrepared.append patternPrepared) := by
    apply (itemsIso.denotation model  sourceEnv targetEnv relEnv ?_).mpr
    · exact targetDenotes
    · intro index
      rfl
  rw [denoteItemSeq_append] at preparedDenotes
  exact preparedDenotes.2

/-- Converse seam transport for the nonempty-spine branch.  Once the retained
host conjunction and the terminal comprehension conjunction denote under the
single prepared seam environment, the authoritative post-splice compiler
block denotes.  This is the constructive half needed when replaying an
instantiation trace forward beneath an intervening cut. -/
theorem output_denotes_of_host_and_terminalPrepared
    (input : Concrete.Splice.Input )
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (host : Concrete.Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (hostDenotes :
      let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
        outputWitness outputLeaf hnonempty
      let targetEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let sourceEnv := targetEnv ∘ combined
      let hostPrepared :=
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfNonempty hadmissible host))
          |>.renameRelations
            (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf)
      denoteItemSeq model  sourceEnv relEnv hostPrepared)
    (terminalDenotes :
      let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
        outputWitness outputLeaf hnonempty
      let targetEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let sourceEnv := targetEnv ∘ combined
      let terminalRelations : RelationRenaming
          patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
        fun relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation)
      let patternPrepared :=
        (patternLeaf.items.renameWires
          (layout.patternSeamPreparedWireOfNonempty hadmissible host
            patternWitness patternLeaf hnonempty)).renameRelations
          terminalRelations
      denoteItemSeq model  sourceEnv relEnv patternPrepared) :
    denoteItemSeq model  env relEnv outputLeaf.items := by
  dsimp only at hostDenotes terminalDenotes
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  let patternPrepared :=
    (patternLeaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations terminalRelations
  have preparedDenotes : denoteItemSeq model  sourceEnv relEnv
      (hostPrepared.append patternPrepared) := by
    rw [denoteItemSeq_append]
    exact ⟨hostDenotes, terminalDenotes⟩
  have itemsIso := layout.compiledSiteItemsIsoOfNonempty  input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty
  have targetCastDenotes : denoteItemSeq model  targetEnv relEnv
      (outputLeaf.items.castWiresEq targetEq) := by
    exact (itemsIso.denotation model  sourceEnv targetEnv relEnv
      (fun _ => rfl)).mp preparedDenotes
  rw [ItemSeq.castWiresEq_eq_renameWires,
    denoteItemSeq_renameWires] at targetCastDenotes
  simpa [targetEnv, targetEq, Function.comp_def] using targetCastDenotes

/-- Native-context form of `terminalPrepared_denotes_of_output`: both seam
renamings are interpreted by environment pullback. -/
theorem terminalItems_denotes_of_output
    (input : Concrete.Splice.Input )
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (host : Concrete.Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (denotes : denoteItemSeq model  env relEnv outputLeaf.items) :
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let sourceEnv := targetEnv ∘ combined
    let terminalRelations : RelationRenaming
        patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
      fun relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation)
    denoteItemSeq model
      (sourceEnv ∘ layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)
      (RelEnv.pullback terminalRelations relEnv) patternLeaf.items := by
  dsimp only
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  have prepared := terminalPrepared_denotes_of_output input layout hadmissible
    host patternWitness patternLeaf outputWitness outputLeaf hnonempty model
     env relEnv denotes
  change denoteItemSeq model  sourceEnv relEnv
      ((patternLeaf.items.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        terminalRelations) at prepared
  rw [denoteItemSeq_renameRelations model  terminalRelations
    (RelEnv.pullback terminalRelations relEnv) relEnv
    (RelEnv.pullback_agrees terminalRelations relEnv)] at prepared
  rw [denoteItemSeq_renameWires] at prepared
  exact prepared

end InstantiationSemantic

end VisualProof.Rule
