import VisualProof.Rule.Soundness.Comprehension.InstantiationAtomCompiler
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.CompilerSource

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The executor's retained binder targets, stated at the quantified bubble
where its relation witness is chosen. -/
structure BinderTargetsAtBubble
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
      payload.binderSpine.proxyCount) : Prop where
  target_shape : ∀ index, ∃ parent,
    state.diagram.val.regions (state.binderTargets index) =
      .bubble parent (payload.binderSpine.arity index)
  target_encloses : ∀ index,
    state.diagram.val.Encloses (state.binderTargets index) state.bubble

/-- A terminal compiler relation variable resolves to the relation owned by
its certified host binder target at the quantified bubble. -/
theorem terminalTargetRelation_exists
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
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val state.bubble
      hostWitness)
    {arity : Nat}
    (relation : RelVar
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels arity) :
    ∃ target : RelVar hostWitness.toFocus.holeRels arity,
      hostLeaf.binders
          (state.binderTargets (Classical.choose
            ((instantiateSpliceInput comprehension attachments binders payload
              state site arguments).plugLayout.terminalBodyBinder_is_proxy
                (Splice.Input.compiledSpliceTerminalView
                  (instantiateSpliceInput comprehension attachments binders
                    payload state site arguments) hnonempty).witness
                (Splice.Input.compiledSpliceTerminalView
                  (instantiateSpliceInput comprehension attachments binders
                    payload state site arguments) hnonempty).leaf
                hnonempty relation.index))) =
        some ⟨arity, target⟩ := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let proxy : Fin payload.binderSpine.proxyCount := Classical.choose
    (layout.terminalBodyBinder_is_proxy pattern.witness pattern.leaf hnonempty
      relation.index)
  have proxySpec :
      pattern.leaf.binderEnumeration.binder relation.index =
        payload.binderSpine.proxy proxy :=
    Classical.choose_spec
      (layout.terminalBodyBinder_is_proxy pattern.witness pattern.leaf hnonempty
        relation.index)
  obtain ⟨patternParent, patternBubble⟩ :=
    pattern.leaf.binderEnumeration.bubble relation.index
  rw [proxySpec] at patternBubble
  have patternBubble' : comprehension.val.diagram.regions
      (payload.binderSpine.proxy proxy) =
        .bubble patternParent
          (pattern.witness.toFocus.holeRels.get relation.index) := by
    simpa [spliceInput, instantiateSpliceInput] using patternBubble
  have proxyArity : payload.binderSpine.arity proxy = arity := by
    rw [payload.binderSpine.proxy_region] at patternBubble'
    have arityEq := (CRegion.bubble.inj patternBubble').2
    exact arityEq.trans relation.hasArity
  obtain ⟨targetParent, targetBubble⟩ := targets.target_shape proxy
  have targetBubble' : state.diagram.val.regions
      (state.binderTargets proxy) = .bubble targetParent arity := by
    simpa [proxyArity] using targetBubble
  exact hostLeaf.bindersCover (state.binderTargets proxy) targetParent arity
    targetBubble' (targets.target_encloses proxy)

/-- Capture-avoiding renaming of the canonical terminal compiler relation
context into the quantified bubble's current lexical relation context. -/
noncomputable def terminalRelationRenamingAtBubble
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
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val state.bubble
      hostWitness) :
    RelationRenaming
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels
      hostWitness.toFocus.holeRels :=
  fun relation => Classical.choose
    (terminalTargetRelation_exists payload state site arguments hnonempty
      targets hostWitness hostLeaf relation)

theorem terminalRelationRenamingAtBubble_lookup
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
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val state.bubble
      hostWitness)
    {arity : Nat}
    (relation : RelVar
      (Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels arity) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let proxy : Fin payload.binderSpine.proxyCount := Classical.choose
      (spliceInput.plugLayout.terminalBodyBinder_is_proxy pattern.witness
        pattern.leaf hnonempty relation.index)
    hostLeaf.binders (state.binderTargets proxy) =
      some ⟨arity,
        terminalRelationRenamingAtBubble payload state site arguments hnonempty
          targets hostWitness hostLeaf relation⟩ := by
  dsimp only
  exact Classical.choose_spec
    (terminalTargetRelation_exists payload state site arguments hnonempty
      targets hostWitness hostLeaf relation)

/-- The terminal body's inherited compiler environment is the open pattern's
distinct exposed-wire environment, preserving the boundary's alias quotient. -/
noncomputable def terminalInheritedEnvironment
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
    {D : Type}
    (assignment : BoundaryAssignment comprehension.elaborate D) :
    Fin (Splice.Input.compiledSpliceTerminalView
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments) hnonempty).leaf.inheritedWires.length → D :=
  fun index =>
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    assignment.classes (Splice.Input.PlugLayout.exposedWireIndex spliceInput
      (pattern.leaf.inheritedWires.get index)
      ((layout.terminalBody_inherited_mem_iff_exposed pattern.witness
        pattern.leaf hnonempty (pattern.leaf.inheritedWires.get index)).1
          (List.get_mem _ index)))

/-- The strongest sound nonzero-spine comprehension relation: its proxy
relations are the current certified host relations, while its ordered object
boundary is supplied by relation arguments followed by fixed parameters. -/
noncomputable def terminalRelationOfNonempty
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
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val state.bubble
      hostWitness)
    (relEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels) :
    Relation model.Carrier payload.arity :=
  fun relationArguments =>
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases relationArguments (wireValue ∘ state.parameters) ∘
            Fin.cast payload.boundarySplit ∧
        denoteRegion model named
          (terminalInheritedEnvironment payload state site arguments hnonempty
            assignment)
          relEnv
          ((ConcreteElaboration.finishRegion comprehension.val.diagram
              pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
              pattern.leaf.items).renameRelations
            (terminalRelationRenamingAtBubble payload state site arguments
              hnonempty targets hostWitness hostLeaf))

theorem terminalRelationOfNonempty_apply
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
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val state.bubble
      hostWitness)
    (relEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels)
    (relationArguments : Fin payload.arity → model.Carrier) :
    terminalRelationOfNonempty payload state site arguments hnonempty targets
        model named wireValue hostWitness hostLeaf relEnv relationArguments ↔
      ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
        assignment.args =
            Fin.addCases relationArguments (wireValue ∘ state.parameters) ∘
              Fin.cast payload.boundarySplit ∧
          denoteRegion model named
            (terminalInheritedEnvironment payload state site arguments
              hnonempty assignment)
            relEnv
            ((ConcreteElaboration.finishRegion comprehension.val.diagram
                (Splice.Input.compiledSpliceTerminalView
                  (instantiateSpliceInput comprehension attachments binders
                    payload state site arguments) hnonempty).leaf.inheritedWires
                payload.binderSpine.bodyContainer
                (Splice.Input.compiledSpliceTerminalView
                  (instantiateSpliceInput comprehension attachments binders
                    payload state site arguments) hnonempty).leaf.items)
              |>.renameRelations
                (terminalRelationRenamingAtBubble payload state site arguments
                  hnonempty targets hostWitness hostLeaf)) :=
  Iff.rfl

end InstantiationSemantic

end VisualProof.Rule
