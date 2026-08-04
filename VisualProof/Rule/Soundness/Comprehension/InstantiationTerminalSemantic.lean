import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A native terminal relation environment realizes one target-indexed family
of the host relations certified by the binder spine. -/
def TerminalRelationsMatch
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    {model : Lambda.LambdaModel}
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (relEnv : RelEnv model.Carrier
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels) : Prop :=
  ∀ {arity : Nat} (relation : RelVar
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels arity),
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let proxy : Fin payload.binderSpine.proxyCount := Classical.choose
      (spliceInput.plugLayout.terminalBodyBinder_is_proxy pattern.witness
        pattern.leaf hnonempty relation.index)
    relEnv.lookup relation =
      (terminalRelation_proxy_arity payload state site arguments hnonempty
        relation) ▸ values proxy

private theorem relEnv_eq_of_lookup
    {rels : RelCtx} {left right : RelEnv D rels}
    (equal : ∀ {arity : Nat} (relation : RelVar rels arity),
      left.lookup relation = right.lookup relation) :
    left = right := by
  induction rels with
  | nil => cases left; cases right; rfl
  | cons head tail induction =>
      rcases left with ⟨leftHead, leftTail⟩
      rcases right with ⟨rightHead, rightTail⟩
      have headEq : leftHead = rightHead := by
        simpa [RelEnv.lookup] using
          equal (⟨0, rfl⟩ : RelVar (head :: tail) head)
      have tailEq : leftTail = rightTail := by
        apply induction
        intro arity relation
        simpa [RelEnv.lookup] using
          equal (⟨relation.index.succ, relation.hasArity⟩ :
            RelVar (head :: tail) arity)
      rw [headEq, tailEq]

/-- The indexed proxy family determines the complete terminal lexical
relation environment.  In particular, a relation witness cannot choose a
second interpretation for any terminal binder. -/
theorem terminalRelationsMatch_unique
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    {model : Lambda.LambdaModel}
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (left right : RelEnv model.Carrier
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels)
    (leftMatch : TerminalRelationsMatch payload state site arguments hnonempty
      values left)
    (rightMatch : TerminalRelationsMatch payload state site arguments hnonempty
      values right) :
    left = right := by
  apply relEnv_eq_of_lookup
  intro arity relation
  exact (leftMatch relation).trans (rightMatch relation).symm

private theorem relationLookup_cast_back
    {D : Type}
    {rels : RelCtx}
    {sourceArity targetArity : Nat}
    (arityEq : sourceArity = targetArity)
    (relation : RelVar rels targetArity)
    (relEnv : RelEnv D rels) :
    arityEq ▸ relEnv.lookup (arityEq.symm ▸ relation) =
      relEnv.lookup relation := by
  cases arityEq
  rfl

/-- The relation environment recovered from the actual output compiler leaf
matches the same proxy values seen through the coalesced host compiler leaf. -/
theorem terminalOutputRelations_match
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    {model : Lambda.LambdaModel}
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (outputRelEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
      let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun relation =>
        spliceInput.plugLayout.hostRelationRenaming host.intrinsicPath
          host.compilerLeaf outputWitness outputLeaf relation
      ProxyRelationsAt payload state host.compilerLeaf.binders
        (RelEnv.pullback hostRelations outputRelEnv) values) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let terminalRelations : RelationRenaming
        pattern.witness.toFocus.holeRels outputWitness.toFocus.holeRels :=
      fun relation =>
        spliceInput.plugLayout.hostRelationRenaming host.intrinsicPath
          host.compilerLeaf outputWitness outputLeaf
          (spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
            hnonempty relation)
    TerminalRelationsMatch payload state site arguments hnonempty values
      (RelEnv.pullback terminalRelations outputRelEnv) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf relation
  let terminalRelations : RelationRenaming pattern.witness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    hostRelations (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf hnonempty
      relation)
  intro arity relation
  let proxy : Fin payload.binderSpine.proxyCount := Classical.choose
    (layout.terminalBodyBinder_is_proxy pattern.witness pattern.leaf hnonempty
      relation.index)
  have arityEq := terminalRelation_proxy_arity payload state site arguments
    hnonempty relation
  let hostRelation := layout.coalescedTerminalRelationRenaming hadmissible
    host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf hnonempty
    relation
  let hostRelationAtProxy : RelVar host.intrinsicPath.toFocus.holeRels
      (payload.binderSpine.arity proxy) := arityEq.symm ▸ hostRelation
  have rawHostLookup := layout.coalescedTerminalRelationRenaming_lookup
    hadmissible host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
    hnonempty relation
  change host.compilerLeaf.binders (state.binderTargets proxy) =
    some ⟨arity, hostRelation⟩ at rawHostLookup
  have hostSigmaEq :
      (⟨payload.binderSpine.arity proxy, hostRelationAtProxy⟩ :
        Σ arity, RelVar host.intrinsicPath.toFocus.holeRels arity) =
      ⟨arity, hostRelation⟩ := by
    exact Sigma.ext arityEq (eqRec_heq arityEq.symm hostRelation)
  have hostLookup : host.compilerLeaf.binders (state.binderTargets proxy) =
      some ⟨payload.binderSpine.arity proxy, hostRelationAtProxy⟩ :=
    rawHostLookup.trans (congrArg some hostSigmaEq).symm
  have fixedValue := fixed proxy hostRelationAtProxy hostLookup
  have castFixed := congrArg (fun value => arityEq ▸ value) fixedValue
  have hostLookupCast : arityEq ▸
      (RelEnv.pullback hostRelations outputRelEnv).lookup hostRelationAtProxy =
      (RelEnv.pullback hostRelations outputRelEnv).lookup hostRelation := by
    simpa only [hostRelationAtProxy] using relationLookup_cast_back arityEq
      hostRelation (RelEnv.pullback hostRelations outputRelEnv)
  dsimp only at castFixed
  rw [hostLookupCast] at castFixed
  change (RelEnv.pullback terminalRelations outputRelEnv).lookup relation =
    arityEq ▸ values proxy
  rw [RelEnv.pullback_agrees terminalRelations outputRelEnv arity relation]
  change outputRelEnv.lookup (hostRelations hostRelation) =
    arityEq ▸ values proxy
  exact (RelEnv.pullback_agrees hostRelations outputRelEnv arity
    hostRelation).symm.trans castFixed

/-- The nonempty-spine comprehension witness determined by one fixed family of
certified host relation values. -/
noncomputable def terminalRelationOfValues
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    Relation model.Carrier payload.arity :=
  fun relationArguments =>
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases relationArguments (wireValue ∘ state.parameters) ∘
            Fin.cast payload.boundarySplit ∧
        ∃ relEnv : RelEnv model.Carrier pattern.witness.toFocus.holeRels,
          TerminalRelationsMatch payload state site arguments hnonempty values
              relEnv ∧
            denoteRegion model named
              (terminalInheritedEnvironment payload state site arguments
                hnonempty assignment)
              relEnv
              (ConcreteElaboration.finishRegion comprehension.val.diagram
                pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
                pattern.leaf.items)

/-- Every executor copy of one comprehension uses the same terminal relation.
The state, occurrence site, and ordered argument wires only select where that
relation is applied; its value depends solely on the transported parameter
values and the fixed family of enclosing proxy relations. -/
theorem terminalRelationOfValues_eq
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (left right : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (leftSite : Fin left.diagram.val.regionCount)
    (rightSite : Fin right.diagram.val.regionCount)
    (leftArguments : Fin payload.arity → Fin left.diagram.val.wireCount)
    (rightArguments : Fin payload.arity → Fin right.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (leftWire : Fin left.diagram.val.wireCount → model.Carrier)
    (rightWire : Fin right.diagram.val.wireCount → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameters : leftWire ∘ left.parameters =
      rightWire ∘ right.parameters) :
    terminalRelationOfValues payload left leftSite leftArguments hnonempty
        model named leftWire values =
      terminalRelationOfValues payload right rightSite rightArguments hnonempty
        model named rightWire values := by
  funext relationArguments
  apply propext
  simp only [terminalRelationOfValues]
  rw [parameters]
  rfl

/-- A denoting actual splice output establishes the target-indexed terminal
relation at the executor-recorded argument wires. -/
theorem terminalRelationOfValues_of_output
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (outputRelEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (denotes : denoteItemSeq model named env outputRelEnv outputLeaf.items)
    (fixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
      let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun relation =>
        spliceInput.plugLayout.hostRelationRenaming host.intrinsicPath
          host.compilerLeaf outputWitness outputLeaf relation
      ProxyRelationsAt payload state host.compilerLeaf.binders
        (RelEnv.pullback hostRelations outputRelEnv) values) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let context := outputLeaf.inheritedWires.extend
      (spliceInput.plugLayout.frameRegion site)
    let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput context
      outputLeaf.wiresExact env fallback
    let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
      fun wire => quotientValues (spliceInput.quotientWire wire)
    terminalRelationOfValues payload state site arguments hnonempty model named
      wireValue values (wireValue ∘ arguments) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let context := outputLeaf.inheritedWires.extend (layout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput context
    outputLeaf.wiresExact env fallback
  let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
    fun wire => quotientValues (spliceInput.quotientWire wire)
  let assignment := spliceInput.patternAttachmentAssignment.map quotientValues
  let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf relation
  let terminalRelations : RelationRenaming pattern.witness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    hostRelations (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf hnonempty
      relation)
  let terminalRelEnv := RelEnv.pullback terminalRelations outputRelEnv
  change ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
    assignment.args =
        Fin.addCases (wireValue ∘ arguments) (wireValue ∘ state.parameters) ∘
          Fin.cast payload.boundarySplit ∧
      ∃ relEnv : RelEnv model.Carrier pattern.witness.toFocus.holeRels,
        TerminalRelationsMatch payload state site arguments hnonempty values
            relEnv ∧
          denoteRegion model named
            (terminalInheritedEnvironment payload state site arguments hnonempty
              assignment)
            relEnv
            (ConcreteElaboration.finishRegion comprehension.val.diagram
              pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
              pattern.leaf.items)
  refine ⟨assignment, ?_, terminalRelEnv, ?_, ?_⟩
  · funext position
    let split : Fin (payload.arity + attachments.length) :=
      Fin.cast payload.boundarySplit position
    change quotientValues
        (spliceInput.quotientWire
          (Fin.addCases arguments state.parameters split)) =
      Fin.addCases
        (fun index => quotientValues
          (spliceInput.quotientWire (arguments index)))
        (fun index => quotientValues
          (spliceInput.quotientWire (state.parameters index))) split
    exact Fin.addCases
      (fun index => by simp only [Fin.addCases_left])
      (fun index => by simp only [Fin.addCases_right]) split
  · exact terminalOutputRelations_match payload state site arguments hnonempty
      hadmissible values outputWitness outputLeaf outputRelEnv fixed
  · have recovered := patternTerminalRegion_denotes_of_output spliceInput
      hadmissible host pattern.witness pattern.leaf outputWitness outputLeaf
      hnonempty model named env outputRelEnv fallback denotes
    simpa [terminalRelEnv, terminalRelations, terminalInheritedEnvironment,
      assignment, quotientValues, context, pattern, layout, Function.comp_def]
      using recovered

end InstantiationSemantic

end VisualProof.Rule
