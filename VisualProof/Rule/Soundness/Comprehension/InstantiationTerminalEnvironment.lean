import VisualProof.Rule.Soundness.Comprehension.InstantiationProxyRelations

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The terminal body's canonical boundary-class valuation is exactly the
valuation read by the authoritative splice seam at each inherited wire. -/
theorem patternTerminalInheritedEnvironment_seam
    {signature : List Nat}
    (input : Splice.Input signature)
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
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → D)
    (fallback : D)
    (index : Fin patternLeaf.inheritedWires.length) :
    let context := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let values := Splice.Input.siteQuotientEnvironment input context
      outputLeaf.wiresExact env fallback
    let assignment := input.patternAttachmentAssignment.map values
    let external := Splice.Input.PlugLayout.exposedWireIndex input
      (patternLeaf.inheritedWires.get index)
      ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness patternLeaf
        hnonempty (patternLeaf.inheritedWires.get index)).1
          (List.get_mem _ index))
    assignment.classes external =
      env (input.plugLayout.patternSeamWireMapOfNonempty hadmissible host patternWitness
        patternLeaf outputWitness outputLeaf hnonempty
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length index))) := by
  dsimp only
  let context := outputLeaf.inheritedWires.extend
    (input.plugLayout.frameRegion input.site)
  let external := Splice.Input.PlugLayout.exposedWireIndex input
    (patternLeaf.inheritedWires.get index)
    ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness patternLeaf
      hnonempty (patternLeaf.inheritedWires.get index)).1
        (List.get_mem _ index))
  let sourceIndex : Fin (patternLeaf.inheritedWires.extend
      input.binderSpine.bodyContainer).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length index)
  let targetIndex := input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
    patternWitness patternLeaf outputWitness outputLeaf hnonempty sourceIndex
  have sourceWire :
      (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).get sourceIndex =
      patternLeaf.inheritedWires.get index := by
    exact Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer
      patternLeaf.inheritedWires input.binderSpine.bodyContainer index
  have targetWire : context.get targetIndex =
      input.plugLayout.frameWire (input.plugLayout.exposedAttachment external) := by
    rw [input.plugLayout.patternSeamWireMapOfNonempty_spec hadmissible host patternWitness
      patternLeaf outputWitness outputLeaf hnonempty sourceIndex]
    rw [sourceWire]
    exact input.plugLayout.patternPlugWire_terminal_inherited patternWitness patternLeaf
      hnonempty index
  have valueEq := Splice.Input.siteQuotientEnvironment_eq input context
    outputLeaf.wiresExact env fallback (input.plugLayout.exposedAttachment external)
    ((input.plugLayout.frameWire_visible_at_region_iff input.site
      (input.plugLayout.exposedAttachment external)).2
        (input.quotientAttachment_visible hadmissible
          (input.plugLayout.exposedPosition external)))
    targetIndex targetWire
  simpa [context, external, sourceIndex, targetIndex,
    Splice.Input.patternAttachmentAssignment, BoundaryAssignment.map,
    Splice.Input.PlugLayout.exposedAttachment, Function.comp_def] using valueEq

/-- Splitting the terminal compiler context into its inherited and local parts
recovers exactly the complete environment transported through the splice seam. -/
theorem patternTerminalExtendedEnvironment_seam
    {signature : List Nat}
    (input : Splice.Input signature)
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
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → D)
    (fallback : D) :
    let context := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let values := Splice.Input.siteQuotientEnvironment input context
      outputLeaf.wiresExact env fallback
    let assignment := input.patternAttachmentAssignment.map values
    let inheritedEnv : Fin patternLeaf.inheritedWires.length → D := fun index =>
      assignment.classes (Splice.Input.PlugLayout.exposedWireIndex input
        (patternLeaf.inheritedWires.get index)
        ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness
          patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
            (List.get_mem _ index)))
    let localEnv : Fin (ConcreteElaboration.exactScopeWires
        input.pattern.val.diagram input.binderSpine.bodyContainer).length → D :=
      fun index =>
        env (input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
          patternWitness patternLeaf outputWitness outputLeaf hnonempty
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
            (Fin.natAdd patternLeaf.inheritedWires.length index)))
    ConcreteElaboration.extendedEnvironment patternLeaf.inheritedWires
        input.binderSpine.bodyContainer inheritedEnv localEnv =
      env ∘ input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
        patternWitness patternLeaf outputWitness outputLeaf hnonempty := by
  dsimp only
  funext sourceIndex
  let lengthEq := ConcreteElaboration.WireContext.length_extend
    patternLeaf.inheritedWires input.binderSpine.bodyContainer
  let split : Fin (patternLeaf.inheritedWires.length +
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length) := Fin.cast lengthEq sourceIndex
  have recover : Fin.cast lengthEq.symm split = sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have castRecover : Fin.cast lengthEq
        (Fin.cast lengthEq.symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length inherited)) =
        Fin.castAdd
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length inherited := by
      apply Fin.ext
      rfl
    simp only [ConcreteElaboration.extendedEnvironment, Function.comp_apply]
    rw [castRecover]
    simp only [extendWireEnv, Fin.addCases_left]
    exact patternTerminalInheritedEnvironment_seam input hadmissible host
      patternWitness patternLeaf outputWitness outputLeaf hnonempty env fallback
      inherited
  · have castRecover : Fin.cast lengthEq
        (Fin.cast lengthEq.symm
          (Fin.natAdd patternLeaf.inheritedWires.length localIndex)) =
        Fin.natAdd patternLeaf.inheritedWires.length localIndex := by
      apply Fin.ext
      rfl
    simp only [ConcreteElaboration.extendedEnvironment, Function.comp_apply]
    rw [castRecover]
    simp [extendWireEnv]

/-- A denoting post-splice compiler leaf therefore supplies the native terminal
body under the canonical ordered boundary assignment. -/
theorem patternTerminalRegion_denotes_of_output
    {signature : List Nat}
    (input : Splice.Input signature)
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
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    let context := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let values := Splice.Input.siteQuotientEnvironment input context
      outputLeaf.wiresExact env fallback
    let assignment := input.patternAttachmentAssignment.map values
    let inheritedEnv : Fin patternLeaf.inheritedWires.length → model.Carrier :=
      fun index =>
        assignment.classes (Splice.Input.PlugLayout.exposedWireIndex input
          (patternLeaf.inheritedWires.get index)
          ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness
            patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
              (List.get_mem _ index)))
    let terminalRelations : RelationRenaming
        patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
      fun relation =>
        input.plugLayout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (input.plugLayout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation)
    denoteRegion model named inheritedEnv
      (RelEnv.pullback terminalRelations relEnv)
      (ConcreteElaboration.finishRegion input.pattern.val.diagram
        patternLeaf.inheritedWires input.binderSpine.bodyContainer
        patternLeaf.items) := by
  dsimp only
  let context := outputLeaf.inheritedWires.extend
    (input.plugLayout.frameRegion input.site)
  let values := Splice.Input.siteQuotientEnvironment input context
    outputLeaf.wiresExact env fallback
  let assignment := input.patternAttachmentAssignment.map values
  let inheritedEnv : Fin patternLeaf.inheritedWires.length → model.Carrier :=
    fun index =>
      assignment.classes (Splice.Input.PlugLayout.exposedWireIndex input
        (patternLeaf.inheritedWires.get index)
        ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness
          patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
            (List.get_mem _ index)))
  let localEnv : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length →
      model.Carrier := fun index =>
    env (input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
      patternWitness patternLeaf outputWitness outputLeaf hnonempty
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
        (Fin.natAdd patternLeaf.inheritedWires.length index)))
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun relation =>
      input.plugLayout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (input.plugLayout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  have nativeItems := terminalItems_denotes_of_output input input.plugLayout
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty model named env relEnv denotes
  have seamItems : denoteItemSeq model named
      (env ∘ input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
        patternWitness patternLeaf outputWitness outputLeaf hnonempty)
      (RelEnv.pullback terminalRelations relEnv) patternLeaf.items := by
    simpa [terminalRelations,
      Splice.Input.PlugLayout.patternSeamWireMapOfNonempty,
      Function.comp_def] using nativeItems
  have environmentEq := patternTerminalExtendedEnvironment_seam input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf hnonempty
    env fallback
  change ConcreteElaboration.extendedEnvironment patternLeaf.inheritedWires
      input.binderSpine.bodyContainer inheritedEnv localEnv =
    env ∘ input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
      patternWitness patternLeaf outputWitness outputLeaf hnonempty
    at environmentEq
  rw [← environmentEq] at seamItems
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  refine ⟨localEnv, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires, denoteItemSeq_renameWires]
  exact seamItems

end InstantiationSemantic

end VisualProof.Rule
