import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The trace-stable terminal relation family specializes exactly to the
relation obtained from the current quantified bubble's certified proxy
binders.  This is the bridge between per-splice compiler extraction and the
single relation witness eventually chosen for the eliminated bubble. -/
theorem terminalRelationOfValues_iff_nonempty
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
    (targets : BinderTargetsAtBubble payload state)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val
      state.bubble hostWitness)
    (hostRelEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels)
    (relationArguments : Fin payload.arity → model.Carrier) :
    terminalRelationOfValues payload state site arguments hnonempty model named
        wireValue
        (proxyRelationsAtBubble payload state targets hostWitness hostLeaf
          hostRelEnv)
        relationArguments ↔
      terminalRelationOfNonempty payload state site arguments hnonempty targets
        model named wireValue hostWitness hostLeaf hostRelEnv
        relationArguments := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      hostWitness.toFocus.holeRels :=
    terminalRelationRenamingAtBubble payload state site arguments hnonempty
      targets hostWitness hostLeaf
  let values := proxyRelationsAtBubble payload state targets hostWitness
    hostLeaf hostRelEnv
  let pulled := RelEnv.pullback relationMap hostRelEnv
  unfold terminalRelationOfValues terminalRelationOfNonempty
  change
    (∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases relationArguments (wireValue ∘ state.parameters) ∘
            Fin.cast payload.boundarySplit ∧
        ∃ terminalRelEnv :
            RelEnv model.Carrier pattern.witness.toFocus.holeRels,
          TerminalRelationsMatch payload state site arguments hnonempty values
              terminalRelEnv ∧
            denoteRegion model named
              (terminalInheritedEnvironment payload state site arguments
                hnonempty assignment)
              terminalRelEnv
              (ConcreteElaboration.finishRegion comprehension.val.diagram
                pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
                pattern.leaf.items)) ↔
    ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases relationArguments (wireValue ∘ state.parameters) ∘
            Fin.cast payload.boundarySplit ∧
        denoteRegion model named
          (terminalInheritedEnvironment payload state site arguments hnonempty
            assignment)
          hostRelEnv
          ((ConcreteElaboration.finishRegion comprehension.val.diagram
            pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            pattern.leaf.items).renameRelations relationMap)
  constructor
  · rintro ⟨assignment, assignmentEq, terminalRelEnv, terminalMatch,
        terminalDenotes⟩
    refine ⟨assignment, assignmentEq, ?_⟩
    have agrees : RelEnv.Agrees relationMap terminalRelEnv hostRelEnv := by
      intro arity relation
      have matched := terminalMatch relation
      have pulledLookup := terminalRelationPullback_lookup payload state site
        arguments hnonempty targets hostWitness hostLeaf hostRelEnv relation
      have pullbackAgrees := RelEnv.pullback_agrees relationMap hostRelEnv arity
        relation
      exact matched.trans (pulledLookup.symm.trans pullbackAgrees)
    exact (denoteRegion_renameRelations model named relationMap terminalRelEnv
      hostRelEnv agrees
      (terminalInheritedEnvironment payload state site arguments hnonempty
        assignment)
      (ConcreteElaboration.finishRegion comprehension.val.diagram
        pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
        pattern.leaf.items)).mpr terminalDenotes
  · rintro ⟨assignment, assignmentEq, renamedDenotes⟩
    refine ⟨assignment, assignmentEq, pulled, ?_, ?_⟩
    · intro arity relation
      exact terminalRelationPullback_lookup payload state site arguments
        hnonempty targets hostWitness hostLeaf hostRelEnv relation
    · exact (denoteRegion_renameRelations model named relationMap pulled
        hostRelEnv (RelEnv.pullback_agrees relationMap hostRelEnv)
        (terminalInheritedEnvironment payload state site arguments hnonempty
          assignment)
        (ConcreteElaboration.finishRegion comprehension.val.diagram
          pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
          pattern.leaf.items)).mp renamedDenotes

end InstantiationSemantic

end VisualProof.Rule
