import VisualProof.Rule.Named

namespace VisualProof.Rule

open VisualProof
open Diagram
open Theory

theorem OpenProofState.closed_denote_iff
    (input : CheckedDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin 0 → model.Carrier) :
    (OpenProofState.closed input).denote model named args ↔
      input.denote model named := by
  change denoteOpen model named input.asOpen.elaborate args ↔
    denoteRegion (relCtx := []) model named Fin.elim0 PUnit.unit input.elaborate
  unfold denoteOpen
  constructor
  · rintro ⟨assignment, _, hbody⟩
    have hclasses : assignment.classes = Fin.elim0 := by
      funext index
      exact Fin.elim0 index
    rw [hclasses] at hbody
    simpa using hbody
  · intro hbody
    let assignment : BoundaryAssignment input.asOpen.elaborate model.Carrier := {
      args := args
      classes := Fin.elim0
      agrees := fun index => Fin.elim0 index
    }
    exact ⟨assignment, rfl, by simpa using hbody⟩

/-- The sole checked dispatcher for the complete twenty-five-form calculus. -/
def applyStep (context : ProofContext signature) (orientation : Orientation)
    (input : CheckedDiagram signature) (step : Step context input) :
    Except StepError (StepReceipt input) :=
  match step with
  | .openTermSpawn region freePorts term =>
      applyOpenTermSpawn orientation input region freePorts term
  | .relationSpawn region definition arity =>
      applyRelationSpawn orientation input region definition arity
  | .boundRelationSpawn region binder arity =>
      applyBoundRelationSpawn orientation input region binder arity
  | .wireJoin first second =>
      applyWireJoin orientation input first second
  | .erasure selection =>
      applyErasure orientation input selection
  | .wireSever wire keep =>
      applyWireSever orientation input wire keep
  | .iteration selection target =>
      applyIteration input selection target
  | .deiteration selection witness =>
      applyDeiteration input selection witness
  | .doubleCutIntro selection =>
      applyDoubleCutIntro input selection
  | .doubleCutElim region =>
      applyDoubleCutElim input region
  | .conversion node payload =>
      applyConversion input node payload
  | .congruenceJoin first second payload =>
      applyCongruenceJoin input payload
  | .anchoredWireSplit wire witness endpoints target =>
      applyAnchoredWireSplit input wire witness endpoints target
  | .anchoredWireContract redundant survivor certificate =>
      applyAnchoredWireContract input redundant survivor certificate
  | .headStrip first second payload =>
      applyHeadStrip input payload
  | .closedTermIntro region term =>
      applyClosedTermIntro input region term
  | .fusion wire =>
      applyFusion input wire
  | .fission node path =>
      applyFission input node path
  | .comprehensionInstantiate bubble comprehension attachments binders payload =>
      applyComprehensionInstantiate orientation input bubble comprehension
        attachments binders payload
  | .comprehensionAbstract wrap comprehension occurrences payload =>
      applyComprehensionAbstract orientation input wrap comprehension
        occurrences payload
  | .theorem theoremIndex selection args direction payload _ =>
      applyTheorem orientation input theoremIndex.val selection args direction payload
  | .vacuousIntro selection arity =>
      applyVacuousIntro input selection arity
  | .vacuousElim region =>
      applyVacuousElim input region
  | .relUnfold node definition payload body_eq =>
      applyRelUnfold input node definition payload
        (relUnfold_body_arity context definition payload body_eq)
  | .relFold selection definition args payload body_eq =>
      applyRelFold input selection definition args payload
        (relFold_namedReference_arity context definition payload body_eq)

def TheoremSchema.Valid (schema : TheoremSchema signature)
    (named : NamedEnv Lambda.Individual signature) : Prop :=
  ∀ args : Fin schema.left.val.boundary.length → Lambda.Individual,
    schema.left.denote Lambda.canonicalModel named args →
      schema.right.denote Lambda.canonicalModel named
        (args ∘ Fin.cast schema.sameBoundaryArity.symm)

structure ProofContext.Valid (context : ProofContext signature) : Prop where
  theorems : ∀ index : Fin context.theorems.length,
    (context.theorems.get index).Valid
      (Theory.interpretDefinitions context.definitions)

def SuccessfulStepSound (context : ProofContext signature)
    (orientation : Orientation) (input result : CheckedDiagram signature)
    (step : Step context input) : Prop :=
  context.Valid →
    DirectedEntailment step.tag orientation
      (input.denote Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions))
      (result.denote Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions))

/-- Boundary-parametric soundness of an interface-bearing successful result.
This is the theorem strength required by replay and theorem registration;
closed soundness is its empty-boundary specialization. -/
def SuccessfulReceiptSound (context : ProofContext signature)
    (orientation : Orientation) (input : CheckedDiagram signature)
    (step : Step context input) (receipt : StepReceipt input) : Prop :=
  ∀ (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped),
    context.Valid → ∀ args : Fin boundary.length → Lambda.Individual,
      let source : OpenProofState signature := {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      }
      let target : OpenProofState signature := {
        diagram := receipt.result
        boundary := mapped
        boundary_root_scoped :=
          receipt.interface.transportBoundary_root_scoped sourceRoot htransport
      }
      DirectedEntailment step.tag orientation
        (source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) args)
        (target.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (args ∘ Fin.cast
            (receipt.interface.transportBoundary_length htransport)))

namespace SuccessfulReceiptSound

/-- A boundary-parametric semantic equivalence discharges every equivalence
rule, independently of replay orientation.  This is the common final step for
the concrete equivalence appliers; it does not add a second soundness
authority. -/
theorem of_equivalence
    (mode : step.tag.semanticMode = .equivalent)
    (equivalent :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        context.Valid → ∀ args : Fin boundary.length → Lambda.Individual,
          let source : OpenProofState signature := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OpenProofState signature := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          source.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions) args ↔
            target.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport))) :
    SuccessfulReceiptSound context orientation input step receipt := by
  intro boundary sourceRoot mapped htransport valid args
  have hequivalent := equivalent boundary sourceRoot mapped htransport
    valid args
  unfold DirectedEntailment
  rw [mode]
  exact hequivalent

/-- A forward boundary-parametric implication discharges a directed rule in
forward replay. -/
theorem of_forward
    (mode : step.tag.semanticMode = .directed)
    (entails :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        context.Valid → ∀ args : Fin boundary.length → Lambda.Individual,
          let source : OpenProofState signature := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OpenProofState signature := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          source.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions) args →
            target.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport))) :
    SuccessfulReceiptSound context .forward input step receipt := by
  intro boundary sourceRoot mapped htransport valid args
  have hentails := entails boundary sourceRoot mapped htransport valid args
  unfold DirectedEntailment DirectedImplication
  rw [mode]
  exact hentails

/-- A reverse boundary-parametric implication discharges a directed rule in
backward replay. -/
theorem of_backward
    (mode : step.tag.semanticMode = .directed)
    (entails :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        context.Valid → ∀ args : Fin boundary.length → Lambda.Individual,
          let source : OpenProofState signature := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OpenProofState signature := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          target.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport)) →
            source.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions) args) :
    SuccessfulReceiptSound context .backward input step receipt := by
  intro boundary sourceRoot mapped htransport valid args
  have hentails := entails boundary sourceRoot mapped htransport valid args
  unfold DirectedEntailment DirectedImplication
  rw [mode]
  exact hentails

/-- Close a successful receipt from semantics proved on the exact operational
open result.  The realized receipt supplies the sole normalization from that
ordered operational boundary to the checked target boundary. -/
theorem of_realized_operational
    {signature : List Nat} {context : ProofContext signature}
    {orientation : Orientation} {input : Diagram.CheckedDiagram signature}
    {step : Step context input} {receipt : StepReceipt input}
    {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (operational :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        Diagram.CheckedOpenDiagram signature)
    (operationalIso :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        Diagram.OpenConcreteIso
          (operational boundary sourceRoot mapped htransport).val
          (realizes.rawResultOpen mapped))
    (sound :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        context.Valid → ∀ args : Fin boundary.length → Lambda.Individual,
          let source : OpenProofState signature := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let iso := operationalIso boundary sourceRoot mapped htransport
          DirectedEntailment step.tag orientation
            (source.denote Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions) args)
            ((operational boundary sourceRoot mapped htransport).denote
              Lambda.canonicalModel
              (Theory.interpretDefinitions context.definitions)
              (args ∘ Fin.cast (iso.boundary_length_eq.trans
                ((realizes.rawResultOpen_boundary_length mapped).trans
                  (receipt.interface.transportBoundary_length htransport)))))) :
    SuccessfulReceiptSound context orientation input step receipt := by
  intro boundary sourceRoot mapped htransport valid args
  let op := operational boundary sourceRoot mapped htransport
  let iso := operationalIso boundary sourceRoot mapped htransport
  have hsound := sound boundary sourceRoot mapped htransport valid args
  have hnormalize := realizes.operationalOpen_denote_iff_result sourceRoot
    htransport op iso Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  unfold DirectedEntailment at hsound ⊢
  cases hmode : step.tag.semanticMode with
  | directed =>
      simp only [hmode] at hsound ⊢
      cases orientation with
      | forward => exact fun hsource => hnormalize.mp (hsound hsource)
      | backward => exact fun htarget => hsound (hnormalize.mpr htarget)
  | equivalent =>
      simp only [hmode] at hsound ⊢
      exact hsound.trans hnormalize

end SuccessfulReceiptSound

private def spawnOperationalOpen
    (source : OpenProofState signature)
    (node : Diagram.CNode source.diagram.val.regionCount)
    (scope : Fin source.diagram.val.regionCount) (portCount : Nat)
    (port : Fin portCount → Diagram.CPort)
    (htarget : (spawnNodeRaw source.diagram.val node scope portCount port).WellFormed
      signature) : Diagram.CheckedOpenDiagram signature :=
  ⟨spawnNodeRawOpen source.asCheckedOpen.val node scope portCount port,
    spawnNodeRawOpen_wellFormed source.asCheckedOpen node scope portCount port
      htarget⟩

private def spawnOperationalIso
    {input : Diagram.CheckedDiagram signature} {receipt : StepReceipt input}
    {node : Diagram.CNode input.val.regionCount}
    {scope : Fin input.val.regionCount} {portCount : Nat}
    {port : Fin portCount → Diagram.CPort}
    (realizes : receipt.Realizes
      (spawnNodeRaw input.val node scope portCount port)
      (spawnNodeWireProvenance input.val node scope portCount port)
      (spawnNodeInterfaceTransport input.val node scope portCount port))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Diagram.OpenConcreteIso
      (spawnNodeRawOpen
        (OpenProofState.asCheckedOpen {
          diagram := input
          boundary := boundary
          boundary_root_scoped := sourceRoot
        }).val node scope portCount port)
      (realizes.rawResultOpen mapped) := by
  apply realizes.operationalIso_to_rawResultOpen htransport
    (boundary.map (Fin.castAdd portCount))
  simpa using spawnNodeInterfaceTransport_transportBoundary
    (input := input.val) (node := node) (scope := scope)
    (portCount := portCount) (port := port) boundary sourceRoot

/-- Common receipt theorem for the three append-only spawn forms.  The
operation-specific public theorems only supply their node and success facts. -/
private theorem spawnReceipt_sound
    {signature : List Nat} {context : ProofContext signature}
    (orientation : Orientation) (input : Diagram.CheckedDiagram signature)
    (step : Step context input) (receipt : StepReceipt input)
    (node : Diagram.CNode input.val.regionCount)
    (scope : Fin input.val.regionCount) (portCount : Nat)
    (port : Fin portCount → Diagram.CPort)
    (hnode : node.region = scope)
    (realizes : receipt.Realizes
      (spawnNodeRaw input.val node scope portCount port)
      (spawnNodeWireProvenance input.val node scope portCount port)
      (spawnNodeInterfaceTransport input.val node scope portCount port))
    (polarity : spawnPolarity orientation
      (concreteCutDepth input.val scope))
    (mode : step.tag.semanticMode = .directed) :
    SuccessfulReceiptSound context orientation input step receipt := by
  have htarget : (spawnNodeRaw input.val node scope portCount port).WellFormed
      signature := realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _ _ =>
      spawnOperationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } node scope portCount port htarget)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      spawnOperationalIso realizes boundary sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let view := Classical.choice
    (Diagram.Splice.openSiteView_complete source.asCheckedOpen scope)
  have hdepth : concreteCutDepth input.val scope =
      view.focus.context.cutDepth := by
    simpa [source] using openSiteView_concreteCutDepth_eq view
  have projects := spawnNodeRawOpen_projects source.asCheckedOpen node scope
    portCount port hnode htarget view.route view.cutDepth Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  dsimp only
  unfold DirectedEntailment
  rw [mode]
  cases orientation with
  | forward =>
      simp only [DirectedImplication]
      have hodd : view.focus.context.cutDepth % 2 = 1 := by
        simpa [spawnPolarity, hdepth] using polarity
      intro hsource
      have hoperational := projects.2 hodd hsource
      simpa [source, spawnOperationalOpen] using hoperational
  | backward =>
      simp only [DirectedImplication]
      have heven : view.focus.context.cutDepth % 2 = 0 := by
        simpa [spawnPolarity, hdepth] using polarity
      intro hoperational
      apply projects.1 heven
      simpa [source, spawnOperationalOpen] using hoperational

/-- Every successful closed-term introduction receipt preserves ordered-open
semantics in both directions. -/
theorem applyClosedTermIntro_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (region : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (receipt : StepReceipt input)
    (happly : applyClosedTermIntro input region term = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.closedTermIntro region term) receipt := by
  have realizes := applyClosedTermIntro_realizes happly
  have htargetClosed : (closedTermIntroRaw input.val region term).WellFormed
      signature := realizes.result_eq ▸ receipt.result.property
  have htarget : (spawnNodeRaw input.val (.term region 0 term) region 1
      (fun _ => .output)).WellFormed signature :=
    by simpa only [closedTermIntroRaw] using htargetClosed
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _ _ =>
      spawnOperationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } (.term region 0 term) region 1 (fun _ => .output) htarget)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      spawnOperationalIso realizes boundary sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let view := Classical.choice
    (Diagram.Splice.openSiteView_complete source.asCheckedOpen region)
  have hequivalent := closedTermIntroOpen_equiv source.asCheckedOpen region term
    htarget view.route view.cutDepth Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  dsimp only
  unfold DirectedEntailment
  change source.denote Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) args ↔ _
  simpa [source, spawnOperationalOpen] using hequivalent

/-- Every successful open-term spawn receipt has the directed semantics
selected by its checked orientation and site polarity. -/
theorem applyOpenTermSpawn_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (region : Fin input.val.regionCount) (freePorts : Nat)
    (term : Lambda.Term 0 (Fin freePorts)) (receipt : StepReceipt input)
    (happly : applyOpenTermSpawn orientation input region freePorts term =
      .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.openTermSpawn region freePorts term) receipt := by
  have realizes := applyOpenTermSpawn_realizes happly
  have success := applyOpenTermSpawn_success orientation input region freePorts
    term receipt happly
  exact spawnReceipt_sound orientation input
    (.openTermSpawn region freePorts term) receipt
    (.term region freePorts term) region (freePorts + 1)
    (Fin.cases .output fun index => .free index) rfl realizes success.1 rfl

/-- Every successful named-relation spawn receipt has the directed semantics
selected by its checked orientation and site polarity. -/
theorem applyRelationSpawn_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (region : Fin input.val.regionCount) (definition arity : Nat)
    (receipt : StepReceipt input)
    (happly : applyRelationSpawn orientation input region definition arity =
      .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.relationSpawn region definition arity) receipt := by
  have realizes := applyRelationSpawn_realizes happly
  have success := applyRelationSpawn_success orientation input region definition
    arity receipt happly
  exact spawnReceipt_sound orientation input
    (.relationSpawn region definition arity) receipt
    (.named region definition arity) region arity (fun index => .arg index)
    rfl realizes success.1 rfl

/-- Every successful bound-relation spawn receipt has the directed semantics
selected by its checked orientation and site polarity. -/
theorem applyBoundRelationSpawn_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (region binder : Fin input.val.regionCount) (arity : Nat)
    (receipt : StepReceipt input)
    (happly : applyBoundRelationSpawn orientation input region binder arity =
      .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.boundRelationSpawn region binder arity) receipt := by
  have realizes := applyBoundRelationSpawn_realizes happly
  have success := applyBoundRelationSpawn_success orientation input region binder
    arity receipt happly
  exact spawnReceipt_sound orientation input
    (.boundRelationSpawn region binder arity) receipt
    (.atom region binder) region arity (fun index => .arg index)
    rfl realizes success.1 rfl

/-- The canonical splice source of a decomposition projects to its retained
frame with exactly the variance selected by the original anchor polarity. -/
private theorem canonicalErasureProjection
    (orientation : Orientation)
    (decomposition : Diagram.Decomposition signature host selection)
    {result : Diagram.CheckedDiagram signature}
    (hsplice : Diagram.Splice.Input.spliceChecked signature
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok result)
    (sourceBoundary : List (Fin
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Diagram.Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (polarity : erasurePolarity orientation
      (concreteCutDepth host.val selection.val.anchor))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    DirectedImplication orientation
      (denoteOpen model named
        (Diagram.Splice.Input.compiledSpliceSourceOpen
          (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
          hsplice sourceBoundary sourceRoot) args)
      (denoteOpen model named
        (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
          (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1
          sourceBoundary sourceRoot).elaborate args) := by
  let spliceInput :=
    Diagram.Splice.Decomposition.originalFragmentInput decomposition
  let hadmissible :=
    (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1
  let layout := spliceInput.plugLayout
  by_cases hsite : spliceInput.site = spliceInput.frame.val.root
  · cases orientation with
    | forward =>
        simp only [DirectedImplication]
        by_cases hzero : spliceInput.binderSpine.proxyCount = 0
        · simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_true, spliceInput, layout, hadmissible] using
            Diagram.Splice.Input.compiledSpliceRootSourceOfEmpty_projects_coalesced
              spliceInput layout hadmissible sourceBoundary sourceRoot hsite
              hzero model named args
        · simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_true, dite_false, spliceInput, layout,
            hadmissible] using
            Diagram.Splice.Input.compiledSpliceRootSourceOfNonempty_projects_coalesced
              spliceInput layout hadmissible sourceBoundary sourceRoot hsite
              hzero model named args
    | backward =>
        have hzeroDepth : concreteCutDepth host.val selection.val.anchor = 0 := by
          rw [← Diagram.Splice.Decomposition.originalSite_concreteCutDepth_eq
            decomposition]
          change concreteCutDepth spliceInput.frame.val spliceInput.site = 0
          rw [hsite]
          exact concreteCutDepth_root_eq_zero spliceInput.frame
        simp [erasurePolarity, hzeroDepth] at polarity
  · let sourceView :=
      Diagram.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
        hadmissible sourceBoundary sourceRoot
    let outputView :=
      Diagram.Splice.Input.compiledSpliceOutputOpenView spliceInput layout
        hadmissible sourceBoundary sourceRoot
    let alignment := layout.compiledNestedFrameContextIso spliceInput
      hadmissible sourceBoundary sourceRoot hsite
    have hsourceDepth : concreteCutDepth spliceInput.frame.val spliceInput.site =
        sourceView.focus.context.cutDepth := by
      calc
        concreteCutDepth spliceInput.frame.val spliceInput.site =
            concreteCutDepth spliceInput.coalesceFrameRaw spliceInput.site :=
          (concreteCutDepth_coalesceFrameRaw spliceInput spliceInput.site).symm
        _ = sourceView.focus.context.cutDepth :=
          openSiteView_concreteCutDepth_eq sourceView
    have halignedDepth : sourceView.focus.context.cutDepth =
        outputView.focus.context.cutDepth := by
      exact alignment.contexts.cutDepth_eq.trans
        (DiagramContext.cutDepth_castRels alignment.holeRelsEq.symm
          outputView.focus.context)
    have houtputDepth : outputView.focus.context.cutDepth =
        concreteCutDepth host.val selection.val.anchor := by
      have horiginal :=
        Diagram.Splice.Decomposition.originalSite_concreteCutDepth_eq
          decomposition
      change concreteCutDepth spliceInput.frame.val spliceInput.site =
        concreteCutDepth host.val selection.val.anchor at horiginal
      exact halignedDepth.symm.trans (hsourceDepth.symm.trans horiginal)
    by_cases hzero : spliceInput.binderSpine.proxyCount = 0
    · have projects :=
        Diagram.Splice.Input.compiledSpliceNestedSourceOfEmpty_projects_coalesced
          spliceInput layout hadmissible sourceBoundary sourceRoot hsite hzero
          model named args
      cases orientation with
      | forward =>
          simp only [DirectedImplication]
          have heven : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, dite_true, spliceInput, layout,
            hadmissible, outputView] using projects.1 heven
      | backward =>
          simp only [DirectedImplication]
          have hodd : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, dite_true, spliceInput, layout,
            hadmissible, outputView] using projects.2 hodd
    · have projects :=
        Diagram.Splice.Input.compiledSpliceNestedSourceOfNonempty_projects_coalesced
          spliceInput layout hadmissible sourceBoundary sourceRoot hsite hzero
          model named args
      cases orientation with
      | forward =>
          simp only [DirectedImplication]
          have heven : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, spliceInput, layout, hadmissible,
            outputView] using projects.1 heven
      | backward =>
          simp only [DirectedImplication]
          have hodd : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Diagram.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, spliceInput, layout, hadmissible,
            outputView] using projects.2 hodd

private def erasureOperationalOpen
    {input : Diagram.CheckedDiagram signature}
    {selection : Diagram.CheckedSelection input.val}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Diagram.CheckedOpenDiagram signature :=
  ⟨realizes.rawResultOpen mapped,
    realizes.rawResultOpen_wellFormed sourceRoot htransport⟩

private def erasureOperationalIso
    {input : Diagram.CheckedDiagram signature}
    {selection : Diagram.CheckedSelection input.val}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireInterfaceTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Diagram.OpenConcreteIso
      (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).val
      (realizes.rawResultOpen mapped) :=
  Diagram.OpenConcreteIso.refl _

/-- Every successful erasure receipt is sound at every ordered open boundary.
Forward erasure uses even polarity; backward replay uses odd polarity and is
therefore insertion under an odd number of cuts. -/
theorem applyErasure_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (receipt : StepReceipt input)
    (happly : applyErasure orientation input selection = .ok receipt) :
    SuccessfulReceiptSound context orientation input (.erasure selection)
      receipt := by
  have realizes := applyErasure_realizes orientation input selection receipt
    happly
  have success := applyErasure_success orientation input selection receipt
    happly
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      erasureOperationalOpen realizes boundary sourceRoot mapped htransport)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      erasureOperationalIso realizes boundary sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      (removeWireInterfaceTransport input selection).transportBoundary
        boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  have rawRoot : ∀ wire, wire ∈ rawMapped →
      ((input.val.removeRaw selection {}).wires wire).scope =
        (input.val.removeRaw selection {}).root :=
    (removeWireInterfaceTransport input selection)
      |>.transportBoundary_root_scoped sourceRoot hexpected
  let extraction := Classical.choose
    (Diagram.extractChecked_complete signature input selection)
  let decomposition : Diagram.Decomposition signature input selection := {
    frameDomains := {}
    frame := ⟨input.val.removeRaw selection {},
      Diagram.ConcreteDiagram.removeRaw_wellFormed input selection {}⟩
    frame_eq := rfl
    extraction := extraction
  }
  let spliceResult := Classical.choose
    (Diagram.Splice.Decomposition.reassemble_original_checked_complete
      decomposition)
  have hsplice : Diagram.Splice.Input.spliceChecked signature
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok spliceResult :=
    Classical.choose_spec
      (Diagram.Splice.Decomposition.reassemble_original_checked_complete
        decomposition)
  have hcoalescedArity :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length = boundary.length := by
    change (rawMapped.map
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition).quotientWire).length =
        boundary.length
    simpa using
      (removeWireInterfaceTransport input selection)
        |>.transportBoundary_length hexpected
  let commonArgs := args ∘ Fin.cast hcoalescedArity
  have projection := canonicalErasureProjection orientation decomposition
    hsplice rawMapped rawRoot success.1 Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) commonArgs
  have hdirect :=
    Diagram.Splice.Decomposition.reassemble_original_source_open_denotation_iff_direct
      decomposition hsplice rawMapped rawRoot Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) commonArgs
  dsimp only at hdirect
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins : rawMapped.map decomposition.frameDomains.wires.origin =
      boundary := by
    simpa [decomposition, rawMapped] using
      removeWireInterfaceTransport_boundary_origins input selection {}
        boundary rawMapped hexpected
  let sourceHostIso : Diagram.OpenConcreteIso source.asCheckedOpen.val
      (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
        rawMapped rawRoot).val := {
    diagram := Diagram.ConcreteIso.refl input.val
    boundary := by
      change boundary.map (Diagram.ConcreteIso.refl input.val).wires =
        rawMapped.map decomposition.frameDomains.wires.origin
      simpa [Diagram.ConcreteIso.refl, Diagram.FiniteEquiv.refl] using
        horigins.symm
  }
  have hsourceHost := sourceHostIso.denote_iff source.asCheckedOpen.property
    (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
      rawMapped rawRoot).property Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  let outputArityEq :
      (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length =
      (Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length := by
    simp [Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Diagram.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Diagram.Splice.Input.PlugLayout.coalescedOpenRoot,
      Diagram.Splice.Input.PlugLayout.outputOpenRoot]
  let directArgs :=
    (commonArgs ∘ Fin.cast outputArityEq.symm) ∘ Fin.cast
      (Diagram.Splice.Decomposition.reassemble_original_output_open_iso
        decomposition rawMapped).boundary_length_eq.symm
  have hdirect' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
            rawMapped rawRoot).elaborate directArgs := by
    simpa only [directArgs, outputArityEq] using hdirect
  have hdirectArgs : directArgs =
      (args ∘ Fin.cast sourceHostIso.boundary_length_eq.symm) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hcompilerSource :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.compiledSpliceSourceOpen
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        source.denote Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions) args := by
    rw [hdirect', hdirectArgs]
    exact hsourceHost.symm
  have hframeRawEq :
      Diagram.Splice.Decomposition.originalFrameOpenRaw decomposition
          rawMapped = realizes.rawResultOpen mapped := by
    rfl
  let frameIso : Diagram.OpenConcreteIso
      (Diagram.Splice.Input.PlugLayout.coalescedOpenRoot
        (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
        rawMapped)
      (realizes.rawResultOpen mapped) := by
    rw [← hframeRawEq]
    exact Diagram.Splice.Decomposition.originalCoalescedFrameOpenIso
      decomposition rawMapped
  have hframe := frameIso.denote_iff
    (Diagram.Splice.Input.PlugLayout.coalescedOpenRoot_wellFormed
      (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
      (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped rawRoot)
    (realizes.rawResultOpen_wellFormed sourceRoot htransport)
    Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) commonArgs
  let operationalIso := erasureOperationalIso realizes boundary sourceRoot
    mapped htransport
  let frameArgs := commonArgs ∘ Fin.cast frameIso.boundary_length_eq.symm
  let operationalArgs :=
    args ∘ Fin.cast (operationalIso.boundary_length_eq.trans
        ((realizes.rawResultOpen_boundary_length mapped).trans
          (receipt.interface.transportBoundary_length htransport)))
  have hopenArgs : frameArgs = operationalArgs := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hframe' :
      denoteOpen Lambda.canonicalModel
          (Theory.interpretDefinitions context.definitions)
          (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
            (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
            (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
            rawRoot).elaborate commonArgs ↔
        (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).denote
            Lambda.canonicalModel
            (Theory.interpretDefinitions context.definitions)
            operationalArgs := by
    rw [← hopenArgs]
    change denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (Diagram.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Diagram.Splice.Decomposition.originalFragmentInput decomposition)
          (Diagram.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
          rawRoot).elaborate commonArgs ↔
      denoteOpen Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).elaborate
        frameArgs
    exact hframe
  change DirectedEntailment .erasure orientation
    (source.denote Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) args)
    ((erasureOperationalOpen realizes boundary sourceRoot mapped htransport).denote
        Lambda.canonicalModel
        (Theory.interpretDefinitions context.definitions)
        operationalArgs)
  unfold DirectedEntailment
  simp only [StepTag.semanticMode]
  cases orientation with
  | forward =>
      intro hsource
      exact hframe'.mp (projection (hcompilerSource.mpr hsource))
  | backward =>
      intro hopen
      exact hcompilerSource.mp (projection (hframe'.mpr hopen))

theorem SuccessfulReceiptSound.closed
    (receipt : StepReceipt input)
    (sound : SuccessfulReceiptSound context orientation input step receipt) :
    SuccessfulStepSound context orientation input receipt.result step := by
  intro valid
  have hopen := sound [] (by simp) [] rfl valid Fin.elim0
  change DirectedEntailment step.tag orientation
    ((OpenProofState.closed input).denote Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) Fin.elim0)
    ((OpenProofState.closed receipt.result).denote Lambda.canonicalModel
      (Theory.interpretDefinitions context.definitions) Fin.elim0) at hopen
  unfold DirectedEntailment at hopen ⊢
  cases hmode : step.tag.semanticMode <;> simp only [hmode] at hopen ⊢
  · cases orientation <;>
      simpa only [OpenProofState.closed_denote_iff] using hopen
  · simpa only [OpenProofState.closed_denote_iff] using hopen

end VisualProof.Rule
