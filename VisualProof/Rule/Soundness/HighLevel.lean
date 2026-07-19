import VisualProof.Rule.Soundness
import VisualProof.Rule.Comprehension.Semantics
import VisualProof.Diagram.Concrete.Elaboration.Simulation
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalAllowedRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

/-- Relate exposed classes when they contain the same ordered boundary
position.  The relation is intentionally many-to-many: unequal alias
partitions may relate several fine classes to one coarse class. -/
def orderedBoundaryRelation
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity) :
    Diagram.ConcreteElaboration.ContextIndexRelation
      source.externalClasses target.externalClasses where
  Rel sourceClass targetClass :=
    ∃ position : Fin sourceArity,
      source.boundary position = sourceClass ∧
        target.boundary (Fin.cast sameArity position) = targetClass

/-- Construct the coarse-or-fine target boundary assignment only after the
active source denotation has produced it through the local implication. -/
theorem proofDependentBoundaryWitness_forward
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (localLaw : denoteOpen model named source sourceArgs →
      denoteOpen model named target
        (sourceArgs ∘ Fin.cast sameArity.symm)) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .forward source target (orderedBoundaryRelation source target sameArity)
      model named sourceArgs (sourceArgs ∘ Fin.cast sameArity.symm) := by
  intro sourceAssignment sourceArgsEq sourceBody
  obtain ⟨targetAssignment, targetArgsEq, targetBody⟩ :=
    localLaw ⟨sourceAssignment, sourceArgsEq, sourceBody⟩
  refine ⟨targetAssignment, targetArgsEq, ?_⟩
  intro sourceClass targetClass related
  obtain ⟨position, rfl, rfl⟩ := related
  calc
    sourceAssignment.classes (source.boundary position) =
        sourceAssignment.args position := sourceAssignment.agrees position
    _ = sourceArgs position := congrFun sourceArgsEq position
    _ = (sourceArgs ∘ Fin.cast sameArity.symm)
        (Fin.cast sameArity position) := by
          congr 1
    _ = targetAssignment.args (Fin.cast sameArity position) :=
      (congrFun targetArgsEq (Fin.cast sameArity position)).symm
    _ = targetAssignment.classes
        (target.boundary (Fin.cast sameArity position)) :=
      (targetAssignment.agrees (Fin.cast sameArity position)).symm

/-- Backward simulation is the exact active-target dual: the source
assignment is chosen only after target denotation has justified it. -/
theorem proofDependentBoundaryWitness_backward
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (localLaw : denoteOpen model named target
        (sourceArgs ∘ Fin.cast sameArity.symm) →
      denoteOpen model named source sourceArgs) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .backward source target (orderedBoundaryRelation source target sameArity)
      model named sourceArgs (sourceArgs ∘ Fin.cast sameArity.symm) := by
  intro targetAssignment targetArgsEq targetBody
  obtain ⟨sourceAssignment, sourceArgsEq, sourceBody⟩ :=
    localLaw ⟨targetAssignment, targetArgsEq, targetBody⟩
  refine ⟨sourceAssignment, sourceArgsEq, ?_⟩
  intro sourceClass targetClass related
  obtain ⟨position, rfl, rfl⟩ := related
  calc
    sourceAssignment.classes (source.boundary position) =
        sourceAssignment.args position := sourceAssignment.agrees position
    _ = sourceArgs position := congrFun sourceArgsEq position
    _ = (sourceArgs ∘ Fin.cast sameArity.symm)
        (Fin.cast sameArity position) := by
          congr 1
    _ = targetAssignment.args (Fin.cast sameArity position) :=
      (congrFun targetArgsEq (Fin.cast sameArity position)).symm
    _ = targetAssignment.classes
        (target.boundary (Fin.cast sameArity position)) :=
      (targetAssignment.agrees (Fin.cast sameArity position)).symm

namespace StrictAliasPartitionExamples

/-- Two ordered boundary positions remain distinct structurally, while the
active body proves their semantic values equal. -/
def equalityFineBoundary : OpenDiagram [] 2 where
  externalClasses := 2
  boundary := id
  boundary_surjective := fun external => ⟨external, rfl⟩
  body := .mk 0 (.cons (.equation 1 (.port 0)) .nil)

/-- Active denotation, rather than an unconditional premise, supplies the
equality needed to inhabit the strictly coarser aliased boundary. -/
theorem equalityFineBoundary_entails_aliased
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    denoteOpen model named equalityFineBoundary args →
      denoteOpen model named aliasedBinaryBoundaryExample args := by
  rintro ⟨sourceAssignment, rfl, sourceLocal, sourceItems⟩
  have sourceEquality : sourceAssignment.args 0 =
      sourceAssignment.args 1 := by
    have itemEquality :
        sourceAssignment.classes (equalityFineBoundary.boundary 1) =
          sourceAssignment.classes (equalityFineBoundary.boundary 0) := by
      change sourceAssignment.classes (equalityFineBoundary.boundary 1) =
        sourceAssignment.classes (equalityFineBoundary.boundary 0)
      calc
        _ = model.eval (.port (0 : Fin 2)) sourceAssignment.classes := by
          simpa [equalityFineBoundary] using sourceItems.1
        _ = _ := by
          simpa [equalityFineBoundary] using
            model.eval_port (0 : Fin 2) sourceAssignment.classes
    exact (sourceAssignment.agrees 0).symm |>.trans
      (itemEquality.symm.trans (sourceAssignment.agrees 1))
  obtain ⟨targetAssignment, htargetArgs⟩ :=
    (boundaryAssignment_iff_aliasConsistent
      aliasedBinaryBoundaryExample sourceAssignment.args).2
        ((aliasedBinaryBoundaryExample_consistency_iff _).2 sourceEquality)
  exact ⟨targetAssignment, htargetArgs, Fin.elim0, True.intro⟩

example (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .forward
      equalityFineBoundary aliasedBinaryBoundaryExample
      (orderedBoundaryRelation equalityFineBoundary
        aliasedBinaryBoundaryExample rfl)
      model named args args := by
  exact proofDependentBoundaryWitness_forward equalityFineBoundary
    aliasedBinaryBoundaryExample rfl model named args
      (equalityFineBoundary_entails_aliased model named args)

example (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .backward
      aliasedBinaryBoundaryExample equalityFineBoundary
      (orderedBoundaryRelation aliasedBinaryBoundaryExample
        equalityFineBoundary rfl)
      model named args args := by
  exact proofDependentBoundaryWitness_backward aliasedBinaryBoundaryExample
    equalityFineBoundary rfl model named args
      (equalityFineBoundary_entails_aliased model named args)

end StrictAliasPartitionExamples

/-- The compiler-simulation direction induced by replay orientation. -/
def replaySimulationDirection : Orientation →
    Diagram.ConcreteElaboration.SimulationDirection
  | .forward => .forward
  | .backward => .backward

/-- The local compiler-simulation direction selected by the cited theorem
side.  Forward citations replace the registered left side by the right side;
reverse citations present the same implication with those local roles
exchanged. -/
def citationSimulationDirection : Direction →
    Diagram.ConcreteElaboration.SimulationDirection
  | .forward => .forward
  | .reverse => .backward

/-- Citation polarity is exactly the route admissibility required by the
paired splice compiler.  The proof uses the compiler's aligned coalesced-frame
and output traces, so the operational cut depth and the semantic cut depth have
one authority. -/
private theorem theoremCitationAllowed
    {input : Diagram.CheckedDiagram signature}
    {selection : Diagram.CheckedSelection input.val}
    {pattern : Diagram.CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Diagram.Decomposition signature input selection)
    (replacement : Diagram.CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity)
    {sourceResult : Diagram.CheckedDiagram signature}
    (sourceSplice : Diagram.Splice.Input.spliceChecked signature
      (occurrence.reassemblyInput decomposition) = .ok sourceResult)
    (sourceBoundary : List
      (Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((occurrence.reassemblyInput decomposition).frame.val.wires wire).scope =
        (occurrence.reassemblyInput decomposition).frame.val.root)
    (orientation : Orientation) (direction : Direction)
    (polarity : citationPolarity orientation direction
      (concreteCutDepth input.val selection.val.anchor)) :
    (occurrence.reassemblyTwoInputPresentation decomposition replacement
      sameArity locality).Allowed
        (citationSimulationDirection direction)
        (replaySimulationDirection orientation)
        (occurrence.reassemblyInput decomposition).plugLayout.plugRaw.root := by
  let sourceInput := occurrence.reassemblyInput decomposition
  let layout := sourceInput.plugLayout
  let hadmissible :=
    (Diagram.Splice.Input.spliceChecked_sound sourceSplice).2.1
  let outputView :=
    Diagram.Splice.Input.compiledSpliceOutputOpenView sourceInput layout
      hadmissible sourceBoundary sourceRoot
  have houtputDepth :
      outputView.focus.context.cutDepth =
        concreteCutDepth input.val selection.val.anchor := by
    by_cases hsite : sourceInput.site = sourceInput.frame.val.root
    · have hplugSite :
          layout.frameRegion sourceInput.site = layout.plugRaw.root := by
        simp [layout, Diagram.Splice.Input.PlugLayout.plugRaw, hsite]
      have houtputZero : outputView.focus.context.cutDepth = 0 := by
        rw [← openSiteView_concreteCutDepth_eq outputView, hplugSite]
        exact concreteCutDepth_root_eq_zero
          ⟨layout.plugRaw,
            layout.plugRaw_wellFormed signature sourceInput hadmissible⟩
      have hhostZero :
          concreteCutDepth input.val selection.val.anchor = 0 := by
        rw [← Diagram.Splice.Decomposition.originalSite_concreteCutDepth_eq
          decomposition]
        change concreteCutDepth sourceInput.frame.val sourceInput.site = 0
        rw [hsite]
        exact concreteCutDepth_root_eq_zero sourceInput.frame
      exact houtputZero.trans hhostZero.symm
    · let sourceView :=
        Diagram.Splice.Input.compiledSpliceCoalescedOpenView sourceInput
          hadmissible sourceBoundary sourceRoot
      let alignment := layout.compiledNestedFrameContextIso sourceInput
        hadmissible sourceBoundary sourceRoot hsite
      have hsourceDepth :
          concreteCutDepth sourceInput.frame.val sourceInput.site =
            sourceView.focus.context.cutDepth := by
        calc
          concreteCutDepth sourceInput.frame.val sourceInput.site =
              concreteCutDepth sourceInput.coalesceFrameRaw sourceInput.site :=
            (concreteCutDepth_coalesceFrameRaw sourceInput
              sourceInput.site).symm
          _ = sourceView.focus.context.cutDepth :=
            openSiteView_concreteCutDepth_eq sourceView
      have halignedDepth :
          sourceView.focus.context.cutDepth =
            outputView.focus.context.cutDepth := by
        exact alignment.contexts.cutDepth_eq.trans
          (DiagramContext.cutDepth_castRels alignment.holeRelsEq.symm
            outputView.focus.context)
      have horiginal :=
        Diagram.Splice.Decomposition.originalSite_concreteCutDepth_eq
          decomposition
      change concreteCutDepth sourceInput.frame.val sourceInput.site =
        concreteCutDepth input.val selection.val.anchor at horiginal
      exact halignedDepth.symm.trans (hsourceDepth.symm.trans horiginal)
  intro path depth route routeDepth
  have pathEq : path = outputView.path :=
    Diagram.Splice.Input.RegionRoute.path_unique
      (layout.plugRaw_wellFormed signature sourceInput hadmissible)
      route outputView.route
  subst path
  have routeEq : route = outputView.route := Subsingleton.elim _ _
  subst route
  have depthEq : depth = outputView.focus.context.cutDepth :=
    regionRoute_cutDepth_unique routeDepth outputView.cutDepth
  subst depth
  rw [houtputDepth]
  cases orientation <;> cases direction <;>
    simpa [citationPolarity, citationSimulationDirection,
      replaySimulationDirection] using polarity

/-- The registered forward side of a theorem payload inherits exactly the
schema implication.  Equality of checked open diagrams is recovered from the
serialized value equalities, so no second theorem-validity authority is
introduced. -/
theorem theoremPayload_forward_local
    (schema : TheoremSchema signature)
    (payload : TheoremPayload input selection hostArgs)
    (registered : theoremSidesMatch schema .forward payload)
    (named : NamedEnv Lambda.Individual signature)
    (valid : schema.Valid named)
    (args : Fin payload.source.val.boundary.length → Lambda.Individual) :
    payload.source.denote Lambda.canonicalModel named args →
      payload.target.denote Lambda.canonicalModel named
        (args ∘ Fin.cast payload.sameBoundaryArity.symm) := by
  rcases payload with ⟨source, target, payloadArity, occurrence⟩
  rcases schema with ⟨left, right, schemaArity⟩
  change source.val = left.val ∧ target.val = right.val at registered
  have hleft : left = source := Subtype.ext registered.1.symm
  have hright : right = target := Subtype.ext registered.2.symm
  subst left
  subst right
  simpa using valid args

/-- A registered reverse citation consumes the same schema implication in the
opposite local presentation: its target is the valid left side and its source
is the entailed right side.  Context polarity later supplies the operational
direction. -/
theorem theoremPayload_backward_local
    (schema : TheoremSchema signature)
    (payload : TheoremPayload input selection hostArgs)
    (registered : theoremSidesMatch schema .reverse payload)
    (named : NamedEnv Lambda.Individual signature)
    (valid : schema.Valid named)
    (args : Fin payload.target.val.boundary.length → Lambda.Individual) :
    payload.target.denote Lambda.canonicalModel named args →
      payload.source.denote Lambda.canonicalModel named
        (args ∘ Fin.cast payload.sameBoundaryArity) := by
  rcases payload with ⟨source, target, payloadArity, occurrence⟩
  rcases schema with ⟨left, right, schemaArity⟩
  change source.val = right.val ∧ target.val = left.val at registered
  have hleft : left = target := Subtype.ext registered.2.symm
  have hright : right = source := Subtype.ext registered.1.symm
  subst left
  subst right
  simpa using valid args

/-- A single local implication has exactly the four contextual directions
accepted by theorem citation.  The executable direction chooses which side is
present before replacement; replay orientation chooses which whole-diagram
implication must be proved.  `citationPolarity` is precisely the condition
that makes those choices agree with cut contravariance. -/
theorem contextualizeCitation
    (orientation : Orientation) (direction : Direction)
    (context : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (left right : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (polarity : citationPolarity orientation direction context.cutDepth)
    (localLaw : ∀ holeRelEnv patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) left →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) right) :
    let before := match direction with
      | .forward => context.fill
          (Region.spliceAt hostLocal hostItems left wireMap relationMap)
      | .reverse => context.fill
          (Region.spliceAt hostLocal hostItems right wireMap relationMap)
    let after := match direction with
      | .forward => context.fill
          (Region.spliceAt hostLocal hostItems right wireMap relationMap)
      | .reverse => context.fill
          (Region.spliceAt hostLocal hostItems left wireMap relationMap)
    DirectedImplication orientation
      (denoteRegion model named env rels before)
      (denoteRegion model named env rels after) := by
  cases orientation <;> cases direction <;>
    simp only [citationPolarity, DirectedImplication] at polarity ⊢
  · exact context.fill_spliceAt_mono_even model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_odd model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_odd model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_even model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw

/-- A local equivalence induces an equivalence between the paired canonical
splice compiler sources. Cut parity selects which local implication proves
each whole-root direction. -/
private theorem equivalentPinnedReplacement_compiled
    (context : ProofContext signature)
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (pattern : Diagram.CheckedOpenDiagram signature)
    (hostArgs : List (Fin input.val.wireCount))
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Diagram.Decomposition signature input selection)
    (replacement : Diagram.CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity)
    {sourceResult targetResult : Diagram.CheckedDiagram signature}
    (sourceSplice : Diagram.Splice.Input.spliceChecked signature
      (occurrence.reassemblyInput decomposition) = .ok sourceResult)
    (targetSplice : Diagram.Splice.Input.spliceChecked signature
      (occurrence.replacementInput decomposition replacement sameArity) =
        .ok targetResult)
    (frameBoundary : List
      (Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount))
    (frameRoot : ∀ wire, wire ∈ frameBoundary →
      ((occurrence.reassemblyInput decomposition).frame.val.wires wire).scope =
        (occurrence.reassemblyInput decomposition).frame.val.root)
    (localForward : ∀ sourceArgs,
      (occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) sourceArgs →
        replacement.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceArgs ∘ Fin.cast
            (occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq.symm))
    (localBackward : ∀ targetArgs,
      replacement.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) targetArgs →
        (occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetArgs ∘ Fin.cast
            (occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq))
    (proofArgs : Fin frameBoundary.length → Lambda.Individual) :
    denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (Diagram.Splice.Input.compiledSpliceSourceOpen
          (occurrence.reassemblyInput decomposition) sourceSplice
          frameBoundary frameRoot)
        (proofArgs ∘ Fin.cast (by
          simp [Diagram.Splice.Input.compiledSpliceSourceOpen,
            Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
            Diagram.Splice.Input.PlugLayout.coalescedOpenRoot])) ↔
      denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (Diagram.Splice.Input.compiledSpliceSourceOpen
          (occurrence.replacementInput decomposition replacement sameArity)
          targetSplice
          ((occurrence.reassemblyTwoInputPresentation decomposition
            replacement sameArity locality).targetBoundary frameBoundary)
          ((occurrence.reassemblyTwoInputPresentation decomposition
            replacement sameArity locality).targetBoundary_root
              frameBoundary frameRoot))
        (proofArgs ∘ Fin.cast (by
          simp [Diagram.Splice.Input.compiledSpliceSourceOpen,
            Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
            Diagram.Splice.Input.PlugLayout.coalescedOpenRoot,
            Diagram.Splice.Input.TwoInputPresentation.targetBoundary])) := by
  let presentation :=
    occurrence.reassemblyTwoInputPresentation decomposition replacement
      sameArity locality
  have hmod :
      concreteCutDepth input.val selection.val.anchor % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  by_cases heven :
      concreteCutDepth input.val selection.val.anchor % 2 = 0
  · have forwardAllowed :
        presentation.Allowed .forward .forward
          (occurrence.reassemblyInput decomposition).plugLayout.plugRaw.root := by
      dsimp only [presentation]
      exact theoremCitationAllowed occurrence decomposition replacement sameArity
        locality sourceSplice frameBoundary frameRoot .forward .forward
        (by simpa [citationPolarity] using heven)
    have backwardAllowed :
        presentation.Allowed .backward .backward
          (occurrence.reassemblyInput decomposition).plugLayout.plugRaw.root := by
      dsimp only [presentation]
      exact theoremCitationAllowed occurrence decomposition replacement sameArity
        locality sourceSplice frameBoundary frameRoot .backward .reverse
        (by simpa [citationPolarity] using heven)
    constructor
    · exact presentation.compiledSpliceSourceOpen_entails sourceSplice
        targetSplice frameBoundary frameRoot rfl rfl .forward .forward
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) localForward
        forwardAllowed proofArgs
    · exact presentation.compiledSpliceSourceOpen_entails sourceSplice
        targetSplice frameBoundary frameRoot rfl rfl .backward .backward
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) localBackward
        backwardAllowed proofArgs
  · have hodd :
        concreteCutDepth input.val selection.val.anchor % 2 = 1 := by
      omega
    have forwardAllowed :
        presentation.Allowed .backward .forward
          (occurrence.reassemblyInput decomposition).plugLayout.plugRaw.root := by
      dsimp only [presentation]
      exact theoremCitationAllowed occurrence decomposition replacement sameArity
        locality sourceSplice frameBoundary frameRoot .forward .reverse
        (by simpa [citationPolarity] using hodd)
    have backwardAllowed :
        presentation.Allowed .forward .backward
          (occurrence.reassemblyInput decomposition).plugLayout.plugRaw.root := by
      dsimp only [presentation]
      exact theoremCitationAllowed occurrence decomposition replacement sameArity
        locality sourceSplice frameBoundary frameRoot .backward .forward
        (by simpa [citationPolarity] using hodd)
    constructor
    · exact presentation.compiledSpliceSourceOpen_entails sourceSplice
        targetSplice frameBoundary frameRoot rfl rfl .backward .forward
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) localBackward
        forwardAllowed proofArgs
    · exact presentation.compiledSpliceSourceOpen_entails sourceSplice
        targetSplice frameBoundary frameRoot rfl rfl .forward .backward
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) localForward
        backwardAllowed proofArgs

/-- Normalize a canonical pinned replacement to a boundary-parametric receipt
once the paired splice compilers have supplied the required whole-root
entailment.  This theorem owns remove/splice boundary factorization, literal
source reassembly, result-boundary normalization, and every dependent arity
cast; individual rule families supply only their local semantic transport. -/
private theorem pinnedReplacementReceipt_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (pattern : Diagram.CheckedOpenDiagram signature)
    (hostArgs : List (Fin input.val.wireCount))
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Diagram.Decomposition signature input selection)
    (replacement : Diagram.CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity)
    (step : Step context input)
    (receipt : StepReceipt input)
    (targetResult : Diagram.CheckedDiagram signature)
    (targetSplice : Diagram.Splice.Input.spliceChecked signature
      (occurrence.replacementInput decomposition replacement sameArity) =
        .ok targetResult)
    (realizes : receipt.Realizes
      (occurrence.replacementInput decomposition replacement
        sameArity).plugLayout.plugRaw
      ((removeWireProvenance input selection
          decomposition.frameDomains).compose
        (spliceFrameWireProvenance
          (occurrence.replacementInput decomposition replacement sameArity)))
      ((removeWireInterfaceTransport input selection
          decomposition.frameDomains).compose
        (spliceFrameInterfaceTransport
          (occurrence.replacementInput decomposition replacement sameArity))))
    (pairedEntails :
      ∀ {sourceResult : Diagram.CheckedDiagram signature}
        (sourceSplice : Diagram.Splice.Input.spliceChecked signature
          (occurrence.reassemblyInput decomposition) = .ok sourceResult)
        (frameBoundary : List
          (Fin (occurrence.reassemblyInput decomposition).frame.val.wireCount))
        (frameRoot : ∀ wire, wire ∈ frameBoundary →
          ((occurrence.reassemblyInput decomposition).frame.val.wires
            wire).scope =
              (occurrence.reassemblyInput decomposition).frame.val.root)
        (proofArgs : Fin frameBoundary.length → Lambda.Individual),
        DirectedEntailment step.tag orientation
          (denoteOpen Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (Diagram.Splice.Input.compiledSpliceSourceOpen
              (occurrence.reassemblyInput decomposition) sourceSplice
              frameBoundary frameRoot)
            (proofArgs ∘ Fin.cast (by
              simp [Diagram.Splice.Input.compiledSpliceSourceOpen,
                Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
                Diagram.Splice.Input.PlugLayout.coalescedOpenRoot])))
          (denoteOpen Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            (Diagram.Splice.Input.compiledSpliceSourceOpen
              (occurrence.replacementInput decomposition replacement sameArity)
              targetSplice
              ((occurrence.reassemblyTwoInputPresentation decomposition
                replacement sameArity locality).targetBoundary frameBoundary)
              ((occurrence.reassemblyTwoInputPresentation decomposition
                replacement sameArity locality).targetBoundary_root
                  frameBoundary frameRoot))
            (proofArgs ∘ Fin.cast (by
              simp [Diagram.Splice.Input.compiledSpliceSourceOpen,
                Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
                Diagram.Splice.Input.PlugLayout.coalescedOpenRoot,
                Diagram.Splice.Input.TwoInputPresentation.targetBoundary])))) :
    SuccessfulReceiptSound context orientation input step receipt := by
  let sourceInput := occurrence.reassemblyInput decomposition
  let targetInput :=
    occurrence.replacementInput decomposition replacement sameArity
  obtain ⟨sourceResult, sourceSplice⟩ :=
    occurrence.replacement_complete decomposition
      (occurrence.reassemblyPattern decomposition)
      (occurrence.reassemblyPattern_boundary_length decomposition).symm
  have sourceSplice' :
      Diagram.Splice.Input.spliceChecked signature sourceInput =
        .ok sourceResult := by
    simpa [sourceInput, PinnedOccurrence.reassemblyInput] using sourceSplice
  let presentation :=
    occurrence.reassemblyTwoInputPresentation decomposition replacement
      sameArity locality
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun _ sourceRoot mapped htransport =>
      ⟨realizes.rawResultOpen mapped,
        realizes.rawResultOpen_wellFormed sourceRoot htransport⟩)
    (operationalIso := fun _ _ _ _ => Diagram.OpenConcreteIso.refl _)
  intro boundary sourceRoot mapped htransport _valid proofArgs
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      ((removeWireInterfaceTransport input selection
          decomposition.frameDomains).compose
        (spliceFrameInterfaceTransport targetInput)).transportBoundary
          boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  obtain ⟨frameBoundary, hremove, htargetBoundary⟩ :=
    (InterfaceTransport.transportBoundary_compose_iff
      (removeWireInterfaceTransport input selection
        decomposition.frameDomains)
      (spliceFrameInterfaceTransport targetInput) boundary rawMapped).1
      hexpected
  have frameRoot : ∀ wire, wire ∈ frameBoundary →
      (sourceInput.frame.val.wires wire).scope =
        sourceInput.frame.val.root := by
    exact (removeWireInterfaceTransport input selection
      decomposition.frameDomains).transportBoundary_root_scoped sourceRoot
        hremove
  let pairedArgs : Fin frameBoundary.length → Lambda.Individual :=
    proofArgs ∘ Fin.cast
      ((removeWireInterfaceTransport input selection
        decomposition.frameDomains).transportBoundary_length hremove)
  have paired :
      DirectedEntailment step.tag orientation
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen sourceInput
            sourceSplice' frameBoundary frameRoot)
          (pairedArgs ∘ Fin.cast (by
            change (frameBoundary.map sourceInput.quotientWire).length =
              frameBoundary.length
            exact List.length_map (as := frameBoundary)
              sourceInput.quotientWire)))
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen targetInput
            targetSplice (presentation.targetBoundary frameBoundary)
            (presentation.targetBoundary_root frameBoundary frameRoot))
          (pairedArgs ∘ Fin.cast (by
            change
              ((presentation.targetBoundary frameBoundary).map
                targetInput.quotientWire).length = frameBoundary.length
            rw [List.length_map]
            exact presentation.targetBoundary_length frameBoundary))) := by
    simpa [sourceInput, targetInput, presentation] using
      pairedEntails sourceSplice' frameBoundary frameRoot pairedArgs
  let sourceAdmissible :=
    (Diagram.Splice.Input.spliceChecked_sound sourceSplice').2.1
  let targetAdmissible :=
    (Diagram.Splice.Input.spliceChecked_sound targetSplice).2.1
  let sourceOutput :=
    Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot sourceInput
      sourceInput.plugLayout sourceAdmissible frameBoundary frameRoot
  let targetFrameBoundary := presentation.targetBoundary frameBoundary
  have targetFrameRoot :
      ∀ wire, wire ∈ targetFrameBoundary →
        (targetInput.frame.val.wires wire).scope =
          targetInput.frame.val.root :=
    presentation.targetBoundary_root frameBoundary frameRoot
  let targetOutput :=
    Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot targetInput
      targetInput.plugLayout targetAdmissible targetFrameBoundary
      targetFrameRoot
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins :
      frameBoundary.map decomposition.frameDomains.wires.origin = boundary := by
    simpa [sourceInput] using
      removeWireInterfaceTransport_boundary_origins input selection
        decomposition.frameDomains boundary frameBoundary hremove
  let sourceHostIso : Diagram.OpenConcreteIso sourceOutput.val
      source.asCheckedOpen.val := {
    diagram := occurrence.reassemblyHostIso decomposition
    boundary := by
      change
        (frameBoundary.map fun wire =>
          sourceInput.plugLayout.frameWire
            (sourceInput.quotientWire wire)).map
              (occurrence.reassemblyHostIso decomposition).wires =
          boundary
      calc
        List.map (occurrence.reassemblyHostIso decomposition).wires
            (List.map
              (fun wire => sourceInput.plugLayout.frameWire
                (sourceInput.quotientWire wire)) frameBoundary) =
            List.map
              ((occurrence.reassemblyHostIso decomposition).wires ∘
                fun wire => sourceInput.plugLayout.frameWire
                  (sourceInput.quotientWire wire)) frameBoundary :=
          List.map_map
        _ = frameBoundary.map decomposition.frameDomains.wires.origin := by
          apply List.map_congr_left
          intro wire _
          simp [sourceInput,
            occurrence.reassemblyHostIso_frameWire_quotientWire
              decomposition wire]
        _ = boundary := horigins
  }
  have hrawBoundary :
      rawMapped =
        targetFrameBoundary.map fun wire =>
          targetInput.plugLayout.frameWire
            (targetInput.quotientWire wire) := by
    have hcanonical :=
      spliceFrameInterfaceTransport_boundary_eq targetInput frameBoundary
        rawMapped htargetBoundary
    simpa [targetFrameBoundary, presentation, targetInput, sourceInput,
      Diagram.Splice.Input.TwoInputPresentation.targetBoundary] using hcanonical
  let targetRawIso : Diagram.OpenConcreteIso targetOutput.val
      (realizes.rawResultOpen mapped) := {
    diagram := Diagram.ConcreteIso.refl targetInput.plugLayout.plugRaw
    boundary := by
      change
        (targetFrameBoundary.map fun wire =>
          targetInput.plugLayout.frameWire
            (targetInput.quotientWire wire)).map
              (Diagram.ConcreteIso.refl
                targetInput.plugLayout.plugRaw).wires =
          rawMapped
      simpa [Diagram.ConcreteIso.refl, Diagram.FiniteEquiv.refl] using
        hrawBoundary.symm
  }
  let sourceCompilerArgs : Fin
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot sourceInput
        sourceAdmissible frameBoundary frameRoot).val.boundary.length →
        Lambda.Individual :=
    pairedArgs ∘ Fin.cast (by
      change (frameBoundary.map sourceInput.quotientWire).length =
        frameBoundary.length
      exact List.length_map (as := frameBoundary) sourceInput.quotientWire)
  let targetCompilerArgs : Fin
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot targetInput
        targetAdmissible targetFrameBoundary targetFrameRoot).val.boundary.length →
        Lambda.Individual :=
    pairedArgs ∘ Fin.cast (by
      change (targetFrameBoundary.map targetInput.quotientWire).length =
        frameBoundary.length
      rw [List.length_map]
      exact presentation.targetBoundary_length frameBoundary)
  let sourceArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot sourceInput
        sourceAdmissible frameBoundary frameRoot).val.boundary.length =
      sourceOutput.val.boundary.length := by
    change (frameBoundary.map sourceInput.quotientWire).length =
      (frameBoundary.map fun wire =>
        sourceInput.plugLayout.frameWire
          (sourceInput.quotientWire wire)).length
    simp
  let targetArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot targetInput
        targetAdmissible targetFrameBoundary targetFrameRoot).val.boundary.length =
      targetOutput.val.boundary.length := by
    change (targetFrameBoundary.map targetInput.quotientWire).length =
      (targetFrameBoundary.map fun wire =>
        targetInput.plugLayout.frameWire
          (targetInput.quotientWire wire)).length
    simp
  have sourceCompilerOutput :=
    Diagram.Splice.Input.spliceChecked_open_denotation_iff sourceInput
      sourceSplice' frameBoundary frameRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) sourceCompilerArgs
  have targetCompilerOutput :=
    Diagram.Splice.Input.spliceChecked_open_denotation_iff targetInput
      targetSplice targetFrameBoundary targetFrameRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) targetCompilerArgs
  have sourceOutputHost := sourceHostIso.denote_iff sourceOutput.property
    source.asCheckedOpen.property Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions)
    (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm)
  have targetOutputRaw := targetRawIso.denote_iff targetOutput.property
    (realizes.rawResultOpen_wellFormed sourceRoot htransport)
    Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions)
    (targetCompilerArgs ∘ Fin.cast targetArityEq.symm)
  have paired' :
      DirectedEntailment step.tag orientation
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen sourceInput
            sourceSplice' frameBoundary frameRoot) sourceCompilerArgs)
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen targetInput
            targetSplice targetFrameBoundary targetFrameRoot)
          targetCompilerArgs) := by
    simpa [sourceCompilerArgs, targetCompilerArgs, sourceInput, targetInput,
      targetFrameBoundary] using paired
  have sourceCompilerOutput' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen sourceInput
            sourceSplice' frameBoundary frameRoot) sourceCompilerArgs ↔
        sourceOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) := by
    simpa [sourceOutput, sourceArityEq, CheckedOpenDiagram.denote,
      denoteOpen_castArity] using sourceCompilerOutput
  have targetCompilerOutput' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen targetInput
            targetSplice targetFrameBoundary targetFrameRoot)
          targetCompilerArgs ↔
        targetOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetCompilerArgs ∘ Fin.cast targetArityEq.symm) := by
    simpa [targetOutput, targetArityEq, CheckedOpenDiagram.denote,
      denoteOpen_castArity] using targetCompilerOutput
  have sourceArgsEq :
      ((sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) ∘
          Fin.cast sourceHostIso.boundary_length_eq.symm) =
        proofArgs := by
    funext position
    apply congrArg proofArgs
    apply Fin.ext
    rfl
  have sourceOutputHost' :
      sourceOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) ↔
        source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) proofArgs := by
    simpa [CheckedOpenDiagram.denote, OpenProofState.denote, sourceArgsEq]
      using sourceOutputHost
  let operationalArgs :=
    proofArgs ∘ Fin.cast
      ((Diagram.OpenConcreteIso.refl
          (realizes.rawResultOpen mapped)).boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport)))
  have targetArgsEq :
      ((targetCompilerArgs ∘ Fin.cast targetArityEq.symm) ∘
          Fin.cast targetRawIso.boundary_length_eq.symm) =
        operationalArgs := by
    funext position
    apply congrArg proofArgs
    apply Fin.ext
    rfl
  have targetOutputRaw' :
      targetOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetCompilerArgs ∘ Fin.cast targetArityEq.symm) ↔
        denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          ((realizes.rawResultOpen mapped).elaborate
            (realizes.rawResultOpen_wellFormed sourceRoot htransport))
          operationalArgs := by
    simpa [CheckedOpenDiagram.denote, targetArgsEq] using targetOutputRaw
  have sourceCompilerHost :=
    sourceCompilerOutput'.trans sourceOutputHost'
  have targetCompilerRaw :=
    targetCompilerOutput'.trans targetOutputRaw'
  dsimp only
  unfold DirectedEntailment at paired' ⊢
  cases hmode : step.tag.semanticMode with
  | directed =>
      simp only [hmode] at paired' ⊢
      cases orientation with
      | forward =>
          intro sourceDenotes
          exact targetCompilerRaw.mp
            (paired' (sourceCompilerHost.mpr sourceDenotes))
      | backward =>
          intro targetDenotes
          exact sourceCompilerHost.mp
            (paired' (targetCompilerRaw.mpr targetDenotes))
  | equivalent =>
      simp only [hmode] at paired' ⊢
      exact sourceCompilerHost.symm.trans (paired'.trans targetCompilerRaw)

/-- Every successful comprehension-instantiation receipt is sound. -/
theorem applyComprehensionInstantiate_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (bubble : Fin input.val.regionCount)
    (comprehension : Diagram.CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (receipt : StepReceipt input)
    (happly : applyComprehensionInstantiate orientation input bubble
      comprehension attachments binders payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.comprehensionInstantiate bubble comprehension attachments binders
        payload) receipt := by
  obtain ⟨polarity, materialization, hmaterialization, copied, hcopy,
      raw, hraw, checked, hcheck, receiptEq, realizes⟩ :=
    applyComprehensionInstantiate_realizes happly
  let operational := materialization.result
  let operationalPayload := materializedInstantiationPayload payload
    materialization
  let initial := initialInstantiationState operationalPayload
  let copyTrace := instantiateCopiesSuccessTrace operational attachments binders
    operationalPayload initial.pendingAtoms.length initial copied hcopy
  let elimTrace := vacuousElimTrace hraw
  have finalWellFormed :
      (dropInstantiationAtomsRaw copied).WellFormed signature :=
    InstantiationDrop.raw_wellFormed copied
  have rawWellFormed : raw.WellFormed signature := by
    exact realizes.result_eq ▸ receipt.result.property
  have sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature := by
    exact Eq.mp (congrArg (fun diagram => diagram.WellFormed signature)
      elimTrace.promotion.raw_eq_diagram) rawWellFormed
  have boundaryNodup : operational.val.boundary.Nodup :=
    materialization.boundary_nodup
  let expectedInterface :=
    (copied.interface.compose
      (InterfaceTransport.byWireCount copied.diagram.val
        (dropInstantiationAtomsRaw copied) rfl)).compose
      (vacuousElimInterfaceTransport hraw)
  let operationalOpen := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (_mapped : List (Fin receipt.result.val.wireCount))
      (_htransport : receipt.interface.transportBoundary boundary =
        some _mapped) =>
    (⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundaryNodup boundary sourceRoot⟩ :
      CheckedOpenDiagram signature)
  let operationalIso := fun
      (boundary : List (Fin input.val.wireCount))
      (sourceRoot : ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root)
      (mapped : List (Fin receipt.result.val.wireCount))
      (htransport : receipt.interface.transportBoundary boundary =
        some mapped) => by
    let rawBoundary := boundary.map fun wire =>
      Fin.cast (vacuousElimRaw?_wireCount hraw).symm
        (copyTrace.wireMap wire)
    let rawOpen : OpenConcreteDiagram := {
      diagram := raw
      boundary := rawBoundary
    }
    let toRaw : OpenConcreteIso
        (copyTrace.finalSourceOpen elimTrace boundary) rawOpen := {
      diagram := VacuousElimTrace.concreteIsoOfEq
        elimTrace.promotion.raw_eq_diagram.symm
      boundary := by
        simp only [InstantiationTrace.finalSourceOpen,
          InstantiationTrace.finalWireMap, rawOpen, rawBoundary, List.map_map]
        apply List.map_congr_left
        intro wire member
        apply Fin.ext
        calc
          ((VacuousElimTrace.concreteIsoOfEq
              elimTrace.promotion.raw_eq_diagram.symm).wires
                (copyTrace.finalWireMap elimTrace wire)).val =
              (copyTrace.finalWireMap elimTrace wire).val :=
            VacuousElimTrace.concreteIsoOfEq_wires_val
              elimTrace.promotion.raw_eq_diagram.symm _
          _ = (Fin.cast (vacuousElimRaw?_wireCount hraw).symm
                (copyTrace.wireMap wire)).val := rfl
    }
    have expectedBoundary :
        expectedInterface.transportBoundary boundary = some rawBoundary := by
      exact copyTrace.finalInterface_transportBoundary_eq_map hraw
        finalWellFormed boundary sourceRoot boundaryNodup
    exact toRaw.trans
      (realizes.operationalIso_to_rawResultOpen htransport rawBoundary
        expectedBoundary)
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := operationalOpen) (operationalIso := operationalIso)
  intro boundary sourceRoot mapped htransport valid args
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let direction : ConcreteElaboration.SimulationDirection :=
    match orientation with
    | .forward => .backward
    | .backward => .forward
  have allowedDepth : InstantiationTrace.FinalDepthAllowed direction
      (concreteCutDepth input.val bubble) := by
    cases orientation <;>
      simpa [direction, InstantiationTrace.FinalDepthAllowed, spawnPolarity]
        using polarity
  have allowed : InstantiationTrace.FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      elimTrace.sourceDiagram.root := by
    intro path depth route routeDepth
    exact copyTrace.finalAllowed_root elimTrace sourceWellFormed
      finalWellFormed direction allowedDepth route routeDepth
  have semantic := copyTrace.finalOpen_denote elimTrace sourceWellFormed
    finalWellFormed boundaryNodup boundary sourceRoot direction allowed
    Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  let iso := operationalIso boundary sourceRoot mapped htransport
  have operationalArgsEq :
      args ∘ Fin.cast (iso.boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport))) =
        args ∘ Fin.cast
          (copyTrace.finalBoundaryLengthEq elimTrace boundary) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  cases orientation with
  | forward =>
      simpa [DirectedEntailment, DirectedImplication, source,
        OpenProofState.denote, operationalOpen, direction, operationalArgsEq]
        using semantic
  | backward =>
      simpa [DirectedEntailment, DirectedImplication, source,
        OpenProofState.denote, operationalOpen, direction, operationalArgsEq]
        using semantic

/-- Every successful comprehension-abstraction receipt is sound. -/
theorem applyComprehensionAbstract_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (wrap : Diagram.CheckedSelection input.val)
    (comprehension : Diagram.CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input))
    (payload : ComprehensionAbstractPayload input wrap comprehension
      occurrences)
    (receipt : StepReceipt input)
    (happly : applyComprehensionAbstract orientation input wrap comprehension
      occurrences payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.comprehensionAbstract wrap comprehension occurrences payload)
      receipt := by
  sorry

/-- Every successful registered-theorem replacement receipt is sound. -/
theorem applyTheorem_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (theoremIndex : Fin context.theorems.length)
    (selection : Diagram.CheckedSelection input.val)
    (args : List (Fin input.val.wireCount)) (direction : Direction)
    (payload : TheoremPayload input selection args)
    (registered : theoremSidesMatch (context.theorems.get theoremIndex)
      direction payload)
    (receipt : StepReceipt input)
    (happly : applyTheorem orientation input theoremIndex.val selection args
      direction payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.theorem theoremIndex selection args direction payload registered)
      receipt := by
  obtain ⟨polarity, decomposition, hdecomposition, locality, targetResult,
      targetSplice, realizes⟩ := applyTheorem_realizes happly
  let sourceInput := payload.occurrence.reassemblyInput decomposition
  let targetInput := payload.occurrence.replacementInput decomposition
    payload.target payload.sameBoundaryArity
  obtain ⟨sourceResult, sourceSplice⟩ :=
    payload.occurrence.replacement_complete decomposition
      (payload.occurrence.reassemblyPattern decomposition)
      (payload.occurrence.reassemblyPattern_boundary_length decomposition).symm
  have sourceSplice' :
      Diagram.Splice.Input.spliceChecked signature sourceInput =
        .ok sourceResult := by
    simpa [sourceInput, PinnedOccurrence.reassemblyInput] using sourceSplice
  let presentation :=
    payload.occurrence.reassemblyTwoInputPresentation decomposition
      payload.target payload.sameBoundaryArity locality
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun _ sourceRoot mapped htransport =>
      ⟨realizes.rawResultOpen mapped,
        realizes.rawResultOpen_wellFormed sourceRoot htransport⟩)
    (operationalIso := fun _ _ _ _ => Diagram.OpenConcreteIso.refl _)
  intro boundary sourceRoot mapped htransport valid proofArgs
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      ((removeWireInterfaceTransport input selection
          decomposition.frameDomains).compose
        (spliceFrameInterfaceTransport targetInput)).transportBoundary
          boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  obtain ⟨frameBoundary, hremove, htargetBoundary⟩ :=
    (InterfaceTransport.transportBoundary_compose_iff
      (removeWireInterfaceTransport input selection
        decomposition.frameDomains)
      (spliceFrameInterfaceTransport targetInput) boundary rawMapped).1
      hexpected
  have frameRoot : ∀ wire, wire ∈ frameBoundary →
      (sourceInput.frame.val.wires wire).scope =
        sourceInput.frame.val.root := by
    exact (removeWireInterfaceTransport input selection
      decomposition.frameDomains).transportBoundary_root_scoped sourceRoot
        hremove
  have allowed :
      presentation.Allowed
        (citationSimulationDirection direction)
        (replaySimulationDirection orientation)
        sourceInput.plugLayout.plugRaw.root := by
    dsimp only [presentation, sourceInput]
    exact theoremCitationAllowed payload.occurrence decomposition
      payload.target payload.sameBoundaryArity locality sourceSplice'
      frameBoundary frameRoot orientation direction polarity
  let pairedArgs : Fin frameBoundary.length → Lambda.Individual :=
    proofArgs ∘ Fin.cast
      ((removeWireInterfaceTransport input selection
        decomposition.frameDomains).transportBoundary_length hremove)
  have paired :=
    presentation.compiledSpliceSourceOpen_entails sourceSplice' targetSplice
      frameBoundary frameRoot rfl rfl
      (citationSimulationDirection direction)
      (replaySimulationDirection orientation)
      Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions)
      (by
        cases direction with
        | forward =>
            intro sourceArgs sourceDenotes
            let sourceIso :=
              payload.occurrence.reassemblyPatternIso decomposition
            have patternDenotes :=
              (sourceIso.denote_iff
                (payload.occurrence.reassemblyPattern decomposition).property
                payload.source.property Lambda.canonicalModel
                (Theory.interpretDefinitions context.definitions)
                sourceArgs).mp sourceDenotes
            have targetDenotes :=
              theoremPayload_forward_local
                (context.theorems.get theoremIndex) payload registered
                (Theory.interpretDefinitions context.definitions)
                (valid.theorems theoremIndex) _ patternDenotes
            simpa [presentation, sourceInput, targetInput,
              PinnedOccurrence.reassemblyInput,
              PinnedOccurrence.replacementInput] using targetDenotes
        | reverse =>
            intro targetArgs targetDenotes
            let sourceIso :=
              payload.occurrence.reassemblyPatternIso decomposition
            have patternDenotes :=
              theoremPayload_backward_local
                (context.theorems.get theoremIndex) payload registered
                (Theory.interpretDefinitions context.definitions)
                (valid.theorems theoremIndex) targetArgs targetDenotes
            apply (sourceIso.denote_iff
              (payload.occurrence.reassemblyPattern decomposition).property
              payload.source.property Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions) _).mpr
            simpa [presentation, sourceInput, targetInput,
              PinnedOccurrence.reassemblyInput,
              PinnedOccurrence.replacementInput] using patternDenotes)
      allowed pairedArgs
  let sourceAdmissible :=
    (Diagram.Splice.Input.spliceChecked_sound sourceSplice').2.1
  let targetAdmissible :=
    (Diagram.Splice.Input.spliceChecked_sound targetSplice).2.1
  let sourceOutput :=
    Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot sourceInput
      sourceInput.plugLayout sourceAdmissible frameBoundary frameRoot
  let targetFrameBoundary := presentation.targetBoundary frameBoundary
  have targetFrameRoot :
      ∀ wire, wire ∈ targetFrameBoundary →
        (targetInput.frame.val.wires wire).scope =
          targetInput.frame.val.root :=
    presentation.targetBoundary_root frameBoundary frameRoot
  let targetOutput :=
    Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot targetInput
      targetInput.plugLayout targetAdmissible targetFrameBoundary
      targetFrameRoot
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins :
      frameBoundary.map decomposition.frameDomains.wires.origin = boundary := by
    simpa [sourceInput] using
      removeWireInterfaceTransport_boundary_origins input selection
        decomposition.frameDomains boundary frameBoundary hremove
  let sourceHostIso : Diagram.OpenConcreteIso sourceOutput.val
      source.asCheckedOpen.val := {
    diagram := payload.occurrence.reassemblyHostIso decomposition
    boundary := by
      change
        (frameBoundary.map fun wire =>
          sourceInput.plugLayout.frameWire
            (sourceInput.quotientWire wire)).map
              (payload.occurrence.reassemblyHostIso decomposition).wires =
          boundary
      calc
        List.map (payload.occurrence.reassemblyHostIso decomposition).wires
            (List.map
              (fun wire => sourceInput.plugLayout.frameWire
                (sourceInput.quotientWire wire)) frameBoundary) =
            List.map
              ((payload.occurrence.reassemblyHostIso decomposition).wires ∘
                fun wire => sourceInput.plugLayout.frameWire
                  (sourceInput.quotientWire wire)) frameBoundary :=
          List.map_map
        _ = frameBoundary.map decomposition.frameDomains.wires.origin := by
          apply List.map_congr_left
          intro wire _
          simp [sourceInput,
            payload.occurrence.reassemblyHostIso_frameWire_quotientWire
              decomposition wire]
        _ = boundary := horigins
  }
  have hrawBoundary :
      rawMapped =
        targetFrameBoundary.map fun wire =>
          targetInput.plugLayout.frameWire
            (targetInput.quotientWire wire) := by
    have hcanonical :=
      spliceFrameInterfaceTransport_boundary_eq targetInput frameBoundary
        rawMapped htargetBoundary
    simpa [targetFrameBoundary, presentation, targetInput, sourceInput,
      Diagram.Splice.Input.TwoInputPresentation.targetBoundary] using hcanonical
  let targetRawIso : Diagram.OpenConcreteIso targetOutput.val
      (realizes.rawResultOpen mapped) := {
    diagram := Diagram.ConcreteIso.refl targetInput.plugLayout.plugRaw
    boundary := by
      change
        (targetFrameBoundary.map fun wire =>
          targetInput.plugLayout.frameWire
            (targetInput.quotientWire wire)).map
              (Diagram.ConcreteIso.refl
                targetInput.plugLayout.plugRaw).wires =
          rawMapped
      simpa [Diagram.ConcreteIso.refl, Diagram.FiniteEquiv.refl] using
        hrawBoundary.symm
  }
  let sourceCompilerArgs : Fin
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot sourceInput
        sourceAdmissible frameBoundary frameRoot).val.boundary.length →
        Lambda.Individual :=
    pairedArgs ∘ Fin.cast (by
      change (frameBoundary.map sourceInput.quotientWire).length =
        frameBoundary.length
      exact List.length_map (as := frameBoundary) sourceInput.quotientWire)
  let targetCompilerArgs : Fin
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot targetInput
        targetAdmissible targetFrameBoundary targetFrameRoot).val.boundary.length →
        Lambda.Individual :=
    pairedArgs ∘ Fin.cast (by
      change (targetFrameBoundary.map targetInput.quotientWire).length =
        frameBoundary.length
      rw [List.length_map]
      exact presentation.targetBoundary_length frameBoundary)
  let sourceArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot sourceInput
        sourceAdmissible frameBoundary frameRoot).val.boundary.length =
      sourceOutput.val.boundary.length := by
    change (frameBoundary.map sourceInput.quotientWire).length =
      (frameBoundary.map fun wire =>
        sourceInput.plugLayout.frameWire
          (sourceInput.quotientWire wire)).length
    simp
  let targetArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot targetInput
        targetAdmissible targetFrameBoundary targetFrameRoot).val.boundary.length =
      targetOutput.val.boundary.length := by
    change (targetFrameBoundary.map targetInput.quotientWire).length =
      (targetFrameBoundary.map fun wire =>
        targetInput.plugLayout.frameWire
          (targetInput.quotientWire wire)).length
    simp
  have sourceCompilerOutput :=
    Diagram.Splice.Input.spliceChecked_open_denotation_iff sourceInput
      sourceSplice' frameBoundary frameRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) sourceCompilerArgs
  have targetCompilerOutput :=
    Diagram.Splice.Input.spliceChecked_open_denotation_iff targetInput
      targetSplice targetFrameBoundary targetFrameRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) targetCompilerArgs
  have sourceOutputHost := sourceHostIso.denote_iff sourceOutput.property
    source.asCheckedOpen.property Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions)
    (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm)
  have targetOutputRaw := targetRawIso.denote_iff targetOutput.property
    (realizes.rawResultOpen_wellFormed sourceRoot htransport)
    Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions)
    (targetCompilerArgs ∘ Fin.cast targetArityEq.symm)
  have paired' :
      (replaySimulationDirection orientation).Entails
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen sourceInput
            sourceSplice' frameBoundary frameRoot) sourceCompilerArgs)
        (denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen targetInput
            targetSplice targetFrameBoundary targetFrameRoot)
          targetCompilerArgs) := by
    simpa [sourceCompilerArgs, targetCompilerArgs, sourceInput, targetInput,
      targetFrameBoundary] using paired
  have sourceCompilerOutput' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen sourceInput
            sourceSplice' frameBoundary frameRoot) sourceCompilerArgs ↔
        sourceOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) := by
    simpa [sourceOutput, sourceArityEq, CheckedOpenDiagram.denote,
      denoteOpen_castArity] using sourceCompilerOutput
  have targetCompilerOutput' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen targetInput
            targetSplice targetFrameBoundary targetFrameRoot)
          targetCompilerArgs ↔
        targetOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetCompilerArgs ∘ Fin.cast targetArityEq.symm) := by
    simpa [targetOutput, targetArityEq, CheckedOpenDiagram.denote,
      denoteOpen_castArity] using targetCompilerOutput
  have sourceArgsEq :
      ((sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) ∘
          Fin.cast sourceHostIso.boundary_length_eq.symm) =
        proofArgs := by
    funext position
    apply congrArg proofArgs
    apply Fin.ext
    rfl
  have sourceOutputHost' :
      sourceOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceCompilerArgs ∘ Fin.cast sourceArityEq.symm) ↔
        source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) proofArgs := by
    simpa [CheckedOpenDiagram.denote, OpenProofState.denote, sourceArgsEq]
      using sourceOutputHost
  let operationalArgs :=
    proofArgs ∘ Fin.cast
      ((Diagram.OpenConcreteIso.refl
          (realizes.rawResultOpen mapped)).boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport)))
  have targetArgsEq :
      ((targetCompilerArgs ∘ Fin.cast targetArityEq.symm) ∘
          Fin.cast targetRawIso.boundary_length_eq.symm) =
        operationalArgs := by
    funext position
    apply congrArg proofArgs
    apply Fin.ext
    rfl
  have targetOutputRaw' :
      targetOutput.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetCompilerArgs ∘ Fin.cast targetArityEq.symm) ↔
        denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          ((realizes.rawResultOpen mapped).elaborate
            (realizes.rawResultOpen_wellFormed sourceRoot htransport))
          operationalArgs := by
    simpa [CheckedOpenDiagram.denote, targetArgsEq] using targetOutputRaw
  have sourceCompilerHost :=
    sourceCompilerOutput'.trans sourceOutputHost'
  have targetCompilerRaw :=
    targetCompilerOutput'.trans targetOutputRaw'
  dsimp only
  unfold DirectedEntailment
  simp only [Step.tag, StepTag.semanticMode]
  cases orientation with
  | forward =>
      intro sourceDenotes
      exact targetCompilerRaw.mp
        (paired' (sourceCompilerHost.mpr sourceDenotes))
  | backward =>
      intro targetDenotes
      exact sourceCompilerHost.mp
        (paired' (targetCompilerRaw.mpr targetDenotes))

/-- Every successful relation-unfolding receipt is sound. -/
theorem applyRelUnfold_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (definition : Fin signature.length)
    (payload : RelUnfoldPayload input node definition)
    (body_eq :
      payload.body.val = (context.definitionEntry definition).body.val)
    (receipt : StepReceipt input)
    (happly : applyRelUnfold input node definition payload
      (relUnfold_body_arity context definition payload body_eq) =
        .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.relUnfold node definition payload body_eq)
      receipt := by
  let sameArity :=
    relUnfold_body_arity context definition payload body_eq
  have happly' :
      applyRelUnfold input node definition payload sameArity =
        .ok receipt := by
    simpa [sameArity] using happly
  obtain ⟨decomposition, hdecomposition, locality, targetResult,
      targetSplice, realizes⟩ := applyRelUnfold_realizes happly'
  let source := namedReferencePattern signature definition
  apply pinnedReplacementReceipt_sound context orientation input
    payload.selection source payload.args payload.occurrence decomposition
    payload.body sameArity locality
    (.relUnfold node definition payload body_eq) receipt targetResult
    targetSplice realizes
  intro sourceResult sourceSplice frameBoundary frameRoot proofArgs
  have localForward : ∀ sourceArgs,
      (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) sourceArgs →
        payload.body.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              payload.body sameArity locality).boundary_arity_eq.symm) := by
    intro sourceArgs sourceDenotes
    let sourceIso :=
      payload.occurrence.reassemblyPatternIso decomposition
    let namedArgs :=
      sourceArgs ∘ Fin.cast sourceIso.boundary_length_eq.symm
    have sourcePatternDenotes :
        source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) namedArgs :=
      (sourceIso.denote_iff
        (payload.occurrence.reassemblyPattern decomposition).property
        source.property Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) sourceArgs).mp
        sourceDenotes
    let entryNamedEq :
        (context.definitionEntry definition).body.val.boundary.length =
          source.val.boundary.length :=
      (context.definitionEntry definition).body_arity.trans
        (namedReferencePattern_boundary_length signature definition).symm
    let entryArgs :=
      namedArgs ∘ Fin.cast entryNamedEq
    have sourceArgsEq :
        ((entryArgs ∘
            Fin.cast
              (context.definitionEntry definition).body_arity.symm) ∘
          Fin.cast
            (namedReferencePattern_boundary_length signature definition)) =
          namedArgs := by
      funext position
      apply congrArg namedArgs
      apply Fin.ext
      rfl
    have namedDenotes :=
      (namedReferencePattern_denote_entry
        (context.definitionEntry definition) Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) entryArgs).mp (by
          simpa [source, sourceArgsEq] using sourcePatternDenotes)
    have entryDenotes :=
      (relUnfold_equiv context.definitions definition entryArgs).mp
        namedDenotes
    let bodyIso : Diagram.OpenConcreteIso payload.body.val
        (context.definitionEntry definition).body.val :=
      Diagram.OpenConcreteIso.ofEq body_eq
    let bodyArgs :=
      entryArgs ∘ Fin.cast bodyIso.boundary_length_eq
    have entryArgsEq :
        bodyArgs ∘ Fin.cast bodyIso.boundary_length_eq.symm =
          entryArgs := by
      funext position
      apply congrArg entryArgs
      apply Fin.ext
      rfl
    have bodyDenotes :
        payload.body.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) bodyArgs :=
      (bodyIso.denote_iff payload.body.property
        (context.definitionEntry definition).body.property
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) bodyArgs).mpr (by
          simpa [entryArgsEq] using entryDenotes)
    have bodyArgsEq :
        bodyArgs =
          sourceArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              payload.body sameArity locality).boundary_arity_eq.symm := by
      funext position
      apply congrArg sourceArgs
      apply Fin.ext
      rfl
    simpa [bodyArgsEq] using bodyDenotes
  have localBackward : ∀ targetArgs,
      payload.body.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) targetArgs →
        (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              payload.body sameArity locality).boundary_arity_eq) := by
    intro targetArgs targetDenotes
    let bodyIso : Diagram.OpenConcreteIso payload.body.val
        (context.definitionEntry definition).body.val :=
      Diagram.OpenConcreteIso.ofEq body_eq
    let entryArgs :=
      targetArgs ∘ Fin.cast bodyIso.boundary_length_eq.symm
    have entryDenotes :
        (context.definitionEntry definition).body.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) entryArgs :=
      (bodyIso.denote_iff payload.body.property
        (context.definitionEntry definition).body.property
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) targetArgs).mp
        targetDenotes
    have namedDenotes :=
      (relUnfold_equiv context.definitions definition entryArgs).mpr
        entryDenotes
    have sourcePatternDenotes :=
      (namedReferencePattern_denote_entry
        (context.definitionEntry definition) Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) entryArgs).mpr
        namedDenotes
    let sourceIso :=
      payload.occurrence.reassemblyPatternIso decomposition
    let sourceArgs :=
      (((entryArgs ∘
          Fin.cast
            (context.definitionEntry definition).body_arity.symm) ∘
        Fin.cast
          (namedReferencePattern_boundary_length signature definition)) ∘
        Fin.cast sourceIso.boundary_length_eq)
    have sourceTargetArgsEq :
        sourceArgs ∘ Fin.cast sourceIso.boundary_length_eq.symm =
          ((entryArgs ∘
              Fin.cast
                (context.definitionEntry definition).body_arity.symm) ∘
            Fin.cast
              (namedReferencePattern_boundary_length signature definition)) := by
      funext position
      apply congrArg
        ((entryArgs ∘
            Fin.cast
              (context.definitionEntry definition).body_arity.symm) ∘
          Fin.cast
            (namedReferencePattern_boundary_length signature definition))
      apply Fin.ext
      rfl
    have sourceDenotes :
        (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) sourceArgs :=
      (sourceIso.denote_iff
        (payload.occurrence.reassemblyPattern decomposition).property
        (namedReferencePattern signature definition).property
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) sourceArgs).mpr (by
          simpa [sourceTargetArgsEq] using sourcePatternDenotes)
    have sourceArgsEq :
        sourceArgs =
          targetArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              payload.body sameArity locality).boundary_arity_eq := by
      funext position
      apply congrArg targetArgs
      apply Fin.ext
      rfl
    simpa [sourceArgsEq] using sourceDenotes
  have equivalence :=
    equivalentPinnedReplacement_compiled context input payload.selection
      source payload.args payload.occurrence decomposition payload.body
      sameArity locality sourceSplice targetSplice frameBoundary frameRoot
      localForward localBackward proofArgs
  simpa [DirectedEntailment, Step.tag, StepTag.semanticMode] using equivalence

/-- Every successful relation-folding receipt is sound. -/
theorem applyRelFold_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (definition : Fin signature.length)
    (args : List (Fin input.val.wireCount))
    (payload : RelFoldPayload input selection definition.val args)
    (body_eq :
      payload.body.val = (context.definitionEntry definition).body.val)
    (receipt : StepReceipt input)
    (happly : applyRelFold input selection definition args payload
      (relFold_namedReference_arity context definition payload body_eq) =
        .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.relFold selection definition args payload body_eq) receipt := by
  let sameArity :=
    relFold_namedReference_arity context definition payload body_eq
  have happly' :
      applyRelFold input selection definition args payload sameArity =
        .ok receipt := by
    simpa [sameArity] using happly
  obtain ⟨decomposition, hdecomposition, targetResult, targetSplice,
      realizes⟩ := applyRelFold_realizes happly'
  let replacement := namedReferencePattern signature definition
  have locality :
      payload.occurrence.ReplacementQuotientsLocal decomposition replacement
        sameArity :=
    payload.occurrence.namedReferenceReplacement_local decomposition
      definition sameArity
  apply pinnedReplacementReceipt_sound context orientation input selection
    payload.body args payload.occurrence decomposition replacement sameArity
    locality (.relFold selection definition args payload body_eq) receipt
    targetResult targetSplice realizes
  intro sourceResult sourceSplice frameBoundary frameRoot proofArgs
  have localForward : ∀ sourceArgs,
      (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) sourceArgs →
        replacement.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (sourceArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq.symm) := by
    intro sourceArgs sourceDenotes
    let sourceIso :=
      payload.occurrence.reassemblyPatternIso decomposition
    let bodyArgs :=
      sourceArgs ∘ Fin.cast sourceIso.boundary_length_eq.symm
    have bodyDenotes :
        payload.body.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) bodyArgs :=
      (sourceIso.denote_iff
        (payload.occurrence.reassemblyPattern decomposition).property
        payload.body.property Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) sourceArgs).mp
        sourceDenotes
    let bodyIso : Diagram.OpenConcreteIso payload.body.val
        (context.definitionEntry definition).body.val :=
      Diagram.OpenConcreteIso.ofEq body_eq
    let entryArgs :=
      bodyArgs ∘ Fin.cast bodyIso.boundary_length_eq.symm
    have entryDenotes :
        (context.definitionEntry definition).body.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) entryArgs :=
      (bodyIso.denote_iff payload.body.property
        (context.definitionEntry definition).body.property
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) bodyArgs).mp
        bodyDenotes
    have namedDenotes :=
      (relFold_equiv context.definitions definition entryArgs).mp
        entryDenotes
    have replacementDenotes :=
      (namedReferencePattern_denote_entry
        (context.definitionEntry definition) Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) entryArgs).mpr
        namedDenotes
    have argsEq :
        ((entryArgs ∘
            Fin.cast
              (context.definitionEntry definition).body_arity.symm) ∘
          Fin.cast
            (namedReferencePattern_boundary_length signature definition)) =
          sourceArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq.symm := by
      funext position
      apply congrArg sourceArgs
      apply Fin.ext
      rfl
    simpa [replacement, argsEq] using replacementDenotes
  have localBackward : ∀ targetArgs,
      replacement.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) targetArgs →
        (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (targetArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq) := by
    intro targetArgs targetDenotes
    let entryReplacementEq :
        (context.definitionEntry definition).body.val.boundary.length =
          replacement.val.boundary.length :=
      (context.definitionEntry definition).body_arity.trans
        (namedReferencePattern_boundary_length signature definition).symm
    let entryArgs :=
      targetArgs ∘ Fin.cast entryReplacementEq
    have targetArgsEq :
        ((entryArgs ∘
            Fin.cast
              (context.definitionEntry definition).body_arity.symm) ∘
          Fin.cast
            (namedReferencePattern_boundary_length signature definition)) =
          targetArgs := by
      funext position
      apply congrArg targetArgs
      apply Fin.ext
      rfl
    have replacementDenotes :
        (namedReferencePattern signature definition).denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          ((entryArgs ∘
              Fin.cast
                (context.definitionEntry definition).body_arity.symm) ∘
            Fin.cast
              (namedReferencePattern_boundary_length signature definition)) := by
      simpa [replacement, targetArgsEq] using targetDenotes
    have namedDenotes :=
      (namedReferencePattern_denote_entry
        (context.definitionEntry definition) Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) entryArgs).mp
        replacementDenotes
    have entryDenotes :=
      (relFold_equiv context.definitions definition entryArgs).mpr
        namedDenotes
    let bodyIso : Diagram.OpenConcreteIso payload.body.val
        (context.definitionEntry definition).body.val :=
      Diagram.OpenConcreteIso.ofEq body_eq
    let bodyArgs :=
      entryArgs ∘ Fin.cast bodyIso.boundary_length_eq
    have entryArgsEq :
        bodyArgs ∘ Fin.cast bodyIso.boundary_length_eq.symm =
          entryArgs := by
      funext position
      apply congrArg entryArgs
      apply Fin.ext
      rfl
    have bodyDenotes :
        payload.body.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) bodyArgs :=
      (bodyIso.denote_iff payload.body.property
        (context.definitionEntry definition).body.property
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) bodyArgs).mpr (by
          simpa [entryArgsEq] using entryDenotes)
    let sourceIso :=
      payload.occurrence.reassemblyPatternIso decomposition
    let sourceArgs :=
      bodyArgs ∘ Fin.cast sourceIso.boundary_length_eq
    have bodyArgsEq :
        sourceArgs ∘ Fin.cast sourceIso.boundary_length_eq.symm =
          bodyArgs := by
      funext position
      apply congrArg bodyArgs
      apply Fin.ext
      rfl
    have sourceDenotes :
        (payload.occurrence.reassemblyInput decomposition).pattern.denote
          Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) sourceArgs :=
      (sourceIso.denote_iff
        (payload.occurrence.reassemblyPattern decomposition).property
        payload.body.property Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions) sourceArgs).mpr (by
          simpa [bodyArgsEq] using bodyDenotes)
    have sourceArgsEq :
        sourceArgs =
          targetArgs ∘ Fin.cast
            (payload.occurrence.reassemblyTwoInputPresentation decomposition
              replacement sameArity locality).boundary_arity_eq := by
      funext position
      apply congrArg targetArgs
      apply Fin.ext
      rfl
    simpa [sourceArgsEq] using sourceDenotes
  have equivalence :=
    equivalentPinnedReplacement_compiled context input selection payload.body
      args payload.occurrence decomposition replacement sameArity locality
      sourceSplice targetSplice frameBoundary frameRoot localForward
      localBackward proofArgs
  simpa [DirectedEntailment, Step.tag, StepTag.semanticMode] using equivalence

end VisualProof.Rule
