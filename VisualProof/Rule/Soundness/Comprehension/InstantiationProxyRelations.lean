import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

private theorem relationLookup_cast
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

/-- Concrete binder targets carry a fixed target-indexed family of relation
values through any intrinsic lexical context in which they are visible. -/
def ProxyRelationsAt
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
    {model : Lambda.LambdaModel}
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) : Prop :=
  ∀ index relation,
    binderContext (state.binderTargets index) =
        some ⟨payload.binderSpine.arity index, relation⟩ →
      relEnv.lookup relation = values index

/-- Pushing a distinct child binder preserves every retained proxy value. -/
theorem ProxyRelationsAt.push_other
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
    {model : Lambda.LambdaModel}
    {rels : RelCtx}
    (binderContext : ConcreteElaboration.BinderContext state.diagram.val rels)
    (relEnv : RelEnv model.Carrier rels)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (fixed : ProxyRelationsAt payload state binderContext relEnv values)
    (child : Fin state.diagram.val.regionCount)
    (childArity : Nat)
    (childRelation : Relation model.Carrier childArity)
    (hne : ∀ index, state.binderTargets index ≠ child) :
    ProxyRelationsAt payload state (binderContext.push child childArity)
      (childRelation, relEnv) values := by
  intro index relation hlookup
  rw [ConcreteElaboration.BinderContext.push_other binderContext childArity
    (hne index)] at hlookup
  cases hold : binderContext (state.binderTargets index) with
  | none => simp [hold] at hlookup
  | some owned =>
      rcases owned with ⟨ownedArity, ownedRelation⟩
      simp only [hold, Option.map_some] at hlookup
      have ownedArityEq : ownedArity = payload.binderSpine.arity index := by
        exact congrArg Sigma.fst (Option.some.inj hlookup)
      subst ownedArity
      have relationEq : relation =
          ConcreteElaboration.BinderContext.liftVar childArity ownedRelation := by
        have hsigma := Option.some.inj hlookup
        cases hsigma
        rfl
      subst relation
      simpa [RelEnv.lookup,
        ConcreteElaboration.BinderContext.liftVar] using
          fixed index ownedRelation hold

/-- Every retained target has its certified arity in the quantified bubble's
compiler leaf. -/
theorem binderTargetRelation_exists
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
    (targets : BinderTargetsAtBubble payload state)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val
      state.bubble hostWitness)
    (index : Fin payload.binderSpine.proxyCount) :
    ∃ relation : RelVar hostWitness.toFocus.holeRels
        (payload.binderSpine.arity index),
      hostLeaf.binders (state.binderTargets index) =
        some ⟨payload.binderSpine.arity index, relation⟩ := by
  obtain ⟨parent, hshape⟩ := targets.target_shape index
  exact hostLeaf.bindersCover (state.binderTargets index) parent
    (payload.binderSpine.arity index) hshape (targets.target_encloses index)

/-- Canonical proxy values at the quantified bubble, indexed by the executor's
binder-spine positions rather than by context-dependent relation variables. -/
noncomputable def proxyRelationsAtBubble
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
    (targets : BinderTargetsAtBubble payload state)
    {model : Lambda.LambdaModel}
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val
      state.bubble hostWitness)
    (relEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels)
    (index : Fin payload.binderSpine.proxyCount) :
    Relation model.Carrier (payload.binderSpine.arity index) :=
  relEnv.lookup (Classical.choose
    (binderTargetRelation_exists payload state targets hostWitness hostLeaf
      index))

theorem proxyRelationsAtBubble_fixed
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
    (targets : BinderTargetsAtBubble payload state)
    {model : Lambda.LambdaModel}
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val
      state.bubble hostWitness)
    (relEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels) :
    ProxyRelationsAt payload state hostLeaf.binders relEnv
      (proxyRelationsAtBubble payload state targets hostWitness hostLeaf
        relEnv) := by
  intro index relation hlookup
  let chosen := Classical.choose
    (binderTargetRelation_exists payload state targets hostWitness hostLeaf
      index)
  have chosenLookup := Classical.choose_spec
    (binderTargetRelation_exists payload state targets hostWitness hostLeaf
      index)
  have hsigma := Option.some.inj (hlookup.symm.trans chosenLookup)
  have relationEq : relation = chosen := by
    cases hsigma
    rfl
  subst relation
  rfl

/-- Pulling the terminal compiler's relation environment back to its native
context reads exactly the target-indexed proxy values chosen at the bubble. -/
theorem terminalRelationPullback_lookup
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
    {model : Lambda.LambdaModel}
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf state.diagram.val
      state.bubble hostWitness)
    (relEnv : RelEnv model.Carrier hostWitness.toFocus.holeRels)
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
    (RelEnv.pullback
      (terminalRelationRenamingAtBubble payload state site arguments hnonempty
        targets hostWitness hostLeaf) relEnv).lookup relation =
      (terminalRelation_proxy_arity payload state site arguments hnonempty
        relation) ▸
        proxyRelationsAtBubble payload state targets hostWitness hostLeaf relEnv
          proxy := by
  dsimp only
  let proxy : Fin payload.binderSpine.proxyCount := Classical.choose
    ((instantiateSpliceInput comprehension attachments binders payload state
      site arguments).plugLayout.terminalBodyBinder_is_proxy
        (Splice.Input.compiledSpliceTerminalView
          (instantiateSpliceInput comprehension attachments binders payload
            state site arguments) hnonempty).witness
        (Splice.Input.compiledSpliceTerminalView
          (instantiateSpliceInput comprehension attachments binders payload
            state site arguments) hnonempty).leaf
        hnonempty relation.index)
  have arityEq := terminalRelation_proxy_arity payload state site arguments
    hnonempty relation
  rw [RelEnv.pullback_agrees
    (terminalRelationRenamingAtBubble payload state site arguments hnonempty
      targets hostWitness hostLeaf) relEnv arity relation]
  let target := terminalRelationRenamingAtBubble payload state site arguments
    hnonempty targets hostWitness hostLeaf relation
  let targetAtProxy : RelVar hostWitness.toFocus.holeRels
      (payload.binderSpine.arity proxy) := arityEq.symm ▸ target
  have rawTargetLookup :=
    terminalRelationRenamingAtBubble_lookup payload state site arguments
      hnonempty targets hostWitness hostLeaf relation
  change hostLeaf.binders (state.binderTargets proxy) =
    some ⟨arity, target⟩ at rawTargetLookup
  have targetSigmaEq :
      (⟨payload.binderSpine.arity proxy, targetAtProxy⟩ :
        Σ arity, RelVar hostWitness.toFocus.holeRels arity) =
      ⟨arity, target⟩ := by
    exact Sigma.ext arityEq (eqRec_heq arityEq.symm target)
  have targetLookup : hostLeaf.binders (state.binderTargets proxy) =
      some ⟨payload.binderSpine.arity proxy, targetAtProxy⟩ := by
    exact rawTargetLookup.trans (congrArg some targetSigmaEq).symm
  have fixed := proxyRelationsAtBubble_fixed payload state targets hostWitness
    hostLeaf relEnv proxy targetAtProxy targetLookup
  have castFixed := congrArg (fun value => arityEq ▸ value) fixed
  have lookupCast : arityEq ▸ relEnv.lookup targetAtProxy =
      relEnv.lookup target := by
    simpa only [targetAtProxy] using relationLookup_cast arityEq target relEnv
  dsimp only at castFixed
  rw [lookupCast] at castFixed
  simpa only [proxy, target] using castFixed

end InstantiationSemantic

end VisualProof.Rule
