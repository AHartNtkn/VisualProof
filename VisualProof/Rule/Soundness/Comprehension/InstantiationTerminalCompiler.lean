import VisualProof.Rule.Soundness.Comprehension.InstantiationTargetInvariant

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A denoting focused compiler block after a nonempty-spine splice contains
the terminal pattern block prepared by the authoritative splice compiler. -/
theorem terminalPrepared_denotes_of_output
    {signature : List Nat}
    (input : Splice.Input signature)
    (layout : Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (host : Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEq := ConcreteElaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
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
    denoteItemSeq model named sourceEnv relEnv patternPrepared := by
  dsimp only
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
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
  have targetDenotes : denoteItemSeq model named targetEnv relEnv
      (outputLeaf.items.castWiresEq targetEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires,
      denoteItemSeq_renameWires]
    simpa [targetEnv, targetEq, Function.comp_def] using denotes
  have itemsIso := layout.compiledSiteItemsIsoOfNonempty signature input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty
  have preparedDenotes : denoteItemSeq model named sourceEnv relEnv
      (hostPrepared.append patternPrepared) := by
    apply (itemsIso.denotation model named sourceEnv targetEnv relEnv ?_).mpr
    · exact targetDenotes
    · intro index
      rfl
  rw [denoteItemSeq_append] at preparedDenotes
  exact preparedDenotes.2

end InstantiationSemantic

end VisualProof.Rule
