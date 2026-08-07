import VisualProof.Concrete.Operation.Comprehension

namespace VisualProof.Refinement.Implementation

open VisualProof.Concrete

open VisualProof
open Diagram
open Theory

theorem OperationState.closed_denote_iff
    (input : Concrete.Checked )
    (model : Model)
    (args : Fin 0 → model.Carrier) :
    (OperationState.closed input).denote model  args ↔
      input.denote model  := by
  change denoteOpen model  input.asOpen.elaborate args ↔
    denoteRegion (relCtx := []) model  Fin.elim0 PUnit.unit input.elaborate
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

def SuccessfulOperationSound (orientation : Orientation)
    (input result : Concrete.Checked ) : Prop :=
  ∀ model,
    match orientation with
    | .forward => input.denote model → result.denote model
    | .backward => result.denote model → input.denote model

/-- Boundary-parametric semantic implication for an operation-specific raw
receipt. Closed soundness is its empty-boundary specialization. -/
def SuccessfulReceiptSound (orientation : Orientation)
    (input : Concrete.Checked )
    (receipt : OperationReceipt input) : Prop :=
  ∀ (model : Model) (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped),
    ∀ args : Fin boundary.length → model.Carrier,
      let source : OperationState  := {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      }
      let target : OperationState  := {
        diagram := receipt.result
        boundary := mapped
        boundary_root_scoped :=
          receipt.interface.transportBoundary_root_scoped sourceRoot htransport
      }
      match orientation with
      | .forward => source.denote model args →
          target.denote model
            (args ∘ Fin.cast
              (receipt.interface.transportBoundary_length htransport))
      | .backward => target.denote model
            (args ∘ Fin.cast
              (receipt.interface.transportBoundary_length htransport)) →
          source.denote model args

namespace SuccessfulReceiptSound

/-- Project a boundary-parametric semantic equivalence in either requested
orientation. -/
theorem of_equivalence
    (equivalent :
      ∀ (model : Model) (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        ∀ args : Fin boundary.length → model.Carrier,
          let source : OperationState  := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OperationState  := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          source.denote model args ↔
            target.denote model
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport))) :
    SuccessfulReceiptSound orientation input receipt := by
  intro model boundary sourceRoot mapped htransport args
  have hequivalent := equivalent model boundary sourceRoot mapped htransport args
  cases orientation with
  | forward => exact hequivalent.mp
  | backward => exact hequivalent.mpr

/-- Package a forward boundary-parametric implication. -/
theorem of_forward
    (entails :
      ∀ (model : Model) (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        ∀ args : Fin boundary.length → model.Carrier,
          let source : OperationState  := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OperationState  := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          source.denote model args →
            target.denote model
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport))) :
    SuccessfulReceiptSound .forward input receipt := by
  intro model boundary sourceRoot mapped htransport args
  have hentails := entails model boundary sourceRoot mapped htransport args
  exact hentails

/-- Package a reverse boundary-parametric implication. -/
theorem of_backward
    (entails :
      ∀ (model : Model) (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        ∀ args : Fin boundary.length → model.Carrier,
          let source : OperationState  := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let target : OperationState  := {
            diagram := receipt.result
            boundary := mapped
            boundary_root_scoped :=
              receipt.interface.transportBoundary_root_scoped sourceRoot htransport
          }
          target.denote model
              (args ∘ Fin.cast
                (receipt.interface.transportBoundary_length htransport)) →
            source.denote model args) :
    SuccessfulReceiptSound .backward input receipt := by
  intro model boundary sourceRoot mapped htransport args
  have hentails := entails model boundary sourceRoot mapped htransport args
  exact hentails

/-- Close a successful receipt from semantics proved on the exact operational
open result. The realized receipt supplies the normalization from that
ordered operational boundary to the checked target boundary. -/
theorem of_realized_operational
    {orientation : Orientation} {input : Concrete.Checked }
    {receipt : OperationReceipt input}
    {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (operational :
      ∀ (boundary : List (Fin input.val.wireCount))
        (_sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (_htransport : receipt.interface.transportBoundary boundary = some mapped),
        Concrete.CheckedOpen )
    (operationalIso :
      ∀ (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        Concrete.OpenIso
          (operational boundary sourceRoot mapped htransport).val
          (realizes.rawResultOpen mapped))
    (sound :
      ∀ (model : Model) (boundary : List (Fin input.val.wireCount))
        (sourceRoot : ∀ wire, wire ∈ boundary →
          (input.val.wires wire).scope = input.val.root)
        (mapped : List (Fin receipt.result.val.wireCount))
        (htransport : receipt.interface.transportBoundary boundary = some mapped),
        ∀ args : Fin boundary.length → model.Carrier,
          let source : OperationState  := {
            diagram := input
            boundary := boundary
            boundary_root_scoped := sourceRoot
          }
          let iso := operationalIso boundary sourceRoot mapped htransport
          match orientation with
          | .forward => source.denote model args →
              (operational boundary sourceRoot mapped htransport).denote model
                (args ∘ Fin.cast (iso.boundary_length_eq.trans
                  ((realizes.rawResultOpen_boundary_length mapped).trans
                    (receipt.interface.transportBoundary_length htransport))))
          | .backward =>
              (operational boundary sourceRoot mapped htransport).denote model
                  (args ∘ Fin.cast (iso.boundary_length_eq.trans
                    ((realizes.rawResultOpen_boundary_length mapped).trans
                      (receipt.interface.transportBoundary_length htransport)))) →
                source.denote model args) :
    SuccessfulReceiptSound orientation input receipt := by
  intro model boundary sourceRoot mapped htransport args
  let op := operational boundary sourceRoot mapped htransport
  let iso := operationalIso boundary sourceRoot mapped htransport
  have hsound := sound model boundary sourceRoot mapped htransport args
  have hnormalize := realizes.operationalOpen_denote_iff_result sourceRoot
    htransport op iso model args
  cases orientation with
  | forward => exact fun hsource => hnormalize.mp (hsound hsource)
  | backward => exact fun htarget => hsound (hnormalize.mpr htarget)

end SuccessfulReceiptSound

private def spawnOperationalOpen
    (source : OperationState )
    (node : Concrete.CNode source.diagram.val.regionCount)
    (scope : Fin source.diagram.val.regionCount) (portCount : Nat)
    (port : Fin portCount → Concrete.CPort)
    (htarget : (spawnNodeRaw source.diagram.val node scope portCount port).WellFormed
      ) : Concrete.CheckedOpen  :=
  ⟨spawnNodeRawOpen source.asCheckedOpen.val node scope portCount port,
    spawnNodeRawOpen_wellFormed source.asCheckedOpen node scope portCount port
      htarget⟩

private def spawnOperationalIso
    {input : Concrete.Checked } {receipt : OperationReceipt input}
    {node : Concrete.CNode input.val.regionCount}
    {scope : Fin input.val.regionCount} {portCount : Nat}
    {port : Fin portCount → Concrete.CPort}
    (realizes : receipt.Realizes
      (spawnNodeRaw input.val node scope portCount port)
      (spawnNodeWireProvenance input.val node scope portCount port)
      (spawnNodeWireTransport input.val node scope portCount port))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.OpenIso
      (spawnNodeRawOpen
        (OperationState.asCheckedOpen {
          diagram := input
          boundary := boundary
          boundary_root_scoped := sourceRoot
        }).val node scope portCount port)
      (realizes.rawResultOpen mapped) := by
  apply realizes.operationalIso_to_rawResultOpen htransport
    (boundary.map (Fin.castAdd portCount))
  simpa using spawnNodeWireTransport_transportBoundary
    (input := input.val) (node := node) (scope := scope)
    (portCount := portCount) (port := port) boundary sourceRoot

/-- Common receipt theorem for the three append-only spawn forms.  The
operation-specific public theorems only supply their node and success facts. -/
private theorem spawnReceipt_sound
    (orientation : Orientation) (input : Concrete.Checked )
    (receipt : OperationReceipt input)
    (node : Concrete.CNode input.val.regionCount)
    (scope : Fin input.val.regionCount) (portCount : Nat)
    (port : Fin portCount → Concrete.CPort)
    (hnode : node.region = scope)
    (realizes : receipt.Realizes
      (spawnNodeRaw input.val node scope portCount port)
      (spawnNodeWireProvenance input.val node scope portCount port)
      (spawnNodeWireTransport input.val node scope portCount port))
    (polarity : spawnPolarity orientation
      (concreteCutDepth input.val scope)) :
    SuccessfulReceiptSound orientation input receipt := by
  have htarget : (spawnNodeRaw input.val node scope portCount port).WellFormed
       := realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot _ _ =>
      spawnOperationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } node scope portCount port htarget)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      spawnOperationalIso realizes boundary sourceRoot mapped htransport)
  intro model boundary sourceRoot mapped htransport args
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let view := Classical.choice
    (Concrete.Splice.openSiteView_complete source.asCheckedOpen scope)
  have hdepth : concreteCutDepth input.val scope =
      view.focus.context.cutDepth := by
    simpa [source] using openSiteView_concreteCutDepth_eq view
  have projects := spawnNodeRawOpen_projects source.asCheckedOpen node scope
    portCount port hnode htarget view.route view.cutDepth model args
  dsimp only
  cases orientation with
  | forward =>
      have hodd : view.focus.context.cutDepth % 2 = 1 := by
        simpa [spawnPolarity, hdepth] using polarity
      intro hsource
      have hoperational := projects.2 hodd hsource
      simpa [source, spawnOperationalOpen] using hoperational
  | backward =>
      have heven : view.focus.context.cutDepth % 2 = 0 := by
        simpa [spawnPolarity, hdepth] using polarity
      intro hoperational
      apply projects.1 heven
      simpa [source, spawnOperationalOpen] using hoperational

/-- Every successful bound-relation spawn receipt has the directed semantics
selected by its checked orientation and site polarity. -/
theorem applyBoundRelationSpawn_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (region binder : Fin input.val.regionCount) (arity : Nat)
    (receipt : OperationReceipt input)
    (happly : applyBoundRelationSpawn orientation input region binder arity =
      .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyBoundRelationSpawn_realizes happly
  have success := applyBoundRelationSpawn_success orientation input region binder
    arity receipt happly
  exact spawnReceipt_sound orientation input receipt
    (.atom region binder) region arity (fun index => .arg index)
    rfl realizes success.1

/-- The canonical splice source of a decomposition projects to its retained
frame with exactly the variance selected by the original anchor polarity. -/
private theorem canonicalErasureProjection
    (orientation : Orientation)
    (decomposition : Concrete.Decomposition  host selection)
    {result : Concrete.Checked }
    (hsplice : Concrete.Splice.Input.spliceChecked
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok result)
    (sourceBoundary : List (Fin
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition).frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      ((Concrete.Splice.Decomposition.originalFragmentInput decomposition).frame.val.wires
        wire).scope =
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition).frame.val.root)
    (polarity : erasurePolarity orientation
      (concreteCutDepth host.val selection.val.anchor))
    (model : Model)
    (args : Fin
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
        (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    (match orientation with
    | .forward => denoteOpen model
          (Concrete.Splice.Input.compiledSpliceSourceOpen
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice sourceBoundary sourceRoot) args →
        denoteOpen model
          (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
            sourceBoundary sourceRoot).elaborate args
    | .backward => denoteOpen model
          (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
            sourceBoundary sourceRoot).elaborate args →
        denoteOpen model
          (Concrete.Splice.Input.compiledSpliceSourceOpen
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice sourceBoundary sourceRoot) args) := by
  let spliceInput :=
    Concrete.Splice.Decomposition.originalFragmentInput decomposition
  let hadmissible :=
    (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1
  let layout := spliceInput.plugLayout
  by_cases hsite : spliceInput.site = spliceInput.frame.val.root
  · cases orientation with
    | forward =>
        by_cases hzero : spliceInput.binderSpine.proxyCount = 0
        · simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_true, spliceInput, layout, hadmissible] using
            Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty_projects_coalesced
              spliceInput layout hadmissible sourceBoundary sourceRoot hsite
              hzero model  args
        · simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_true, dite_false, spliceInput, layout,
            hadmissible] using
            Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty_projects_coalesced
              spliceInput layout hadmissible sourceBoundary sourceRoot hsite
              hzero model  args
    | backward =>
        have hzeroDepth : concreteCutDepth host.val selection.val.anchor = 0 := by
          rw [← Concrete.Splice.Decomposition.originalSite_concreteCutDepth_eq
            decomposition]
          change concreteCutDepth spliceInput.frame.val spliceInput.site = 0
          rw [hsite]
          exact concreteCutDepth_root_eq_zero spliceInput.frame
        simp [erasurePolarity, hzeroDepth] at polarity
  · let sourceView :=
      Concrete.Splice.Input.compiledSpliceCoalescedOpenView spliceInput
        hadmissible sourceBoundary sourceRoot
    let outputView :=
      Concrete.Splice.Input.compiledSpliceOutputOpenView spliceInput layout
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
        Concrete.Splice.Decomposition.originalSite_concreteCutDepth_eq
          decomposition
      change concreteCutDepth spliceInput.frame.val spliceInput.site =
        concreteCutDepth host.val selection.val.anchor at horiginal
      exact halignedDepth.symm.trans (hsourceDepth.symm.trans horiginal)
    by_cases hzero : spliceInput.binderSpine.proxyCount = 0
    · have projects :=
        Concrete.Splice.Input.compiledSpliceNestedSourceOfEmpty_projects_coalesced
          spliceInput layout hadmissible sourceBoundary sourceRoot hsite hzero
          model  args
      cases orientation with
      | forward =>
          have heven : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, dite_true, spliceInput, layout,
            hadmissible, outputView] using projects.1 heven
      | backward =>
          have hodd : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, dite_true, spliceInput, layout,
            hadmissible, outputView] using projects.2 hodd
    · have projects :=
        Concrete.Splice.Input.compiledSpliceNestedSourceOfNonempty_projects_coalesced
          spliceInput layout hadmissible sourceBoundary sourceRoot hsite hzero
          model  args
      cases orientation with
      | forward =>
          have heven : outputView.focus.context.cutDepth % 2 = 0 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, spliceInput, layout, hadmissible,
            outputView] using projects.1 heven
      | backward =>
          have hodd : outputView.focus.context.cutDepth % 2 = 1 := by
            rw [houtputDepth]
            exact polarity
          simpa only [Concrete.Splice.Input.compiledSpliceSourceOpen,
            hsite, hzero, dite_false, spliceInput, layout, hadmissible,
            outputView] using projects.2 hodd

private def erasureOperationalOpen
    {input : Concrete.Checked }
    {selection : Concrete.CheckedSelection input.val}
    {receipt : OperationReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireWireTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.CheckedOpen  :=
  ⟨realizes.rawResultOpen mapped,
    realizes.rawResultOpen_wellFormed sourceRoot htransport⟩

private def erasureOperationalIso
    {input : Concrete.Checked }
    {selection : Concrete.CheckedSelection input.val}
    {receipt : OperationReceipt input}
    (realizes : receipt.Realizes (input.val.removeRaw selection {})
      (removeWireProvenance input selection)
      (removeWireWireTransport input selection))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    Concrete.OpenIso
      (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).val
      (realizes.rawResultOpen mapped) :=
  Concrete.OpenIso.refl _

/-- Every successful erasure receipt is sound at every ordered open boundary.
Forward erasure uses even polarity; backward erasure uses odd polarity and is
therefore insertion under an odd number of cuts. -/
theorem applyErasure_sound
    (orientation : Orientation)
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (receipt : OperationReceipt input)
    (happly : applyErasure orientation input selection = .ok receipt) :
    SuccessfulReceiptSound orientation input receipt := by
  have realizes := applyErasure_realizes orientation input selection receipt
    happly
  have success := applyErasure_success orientation input selection receipt
    happly
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      erasureOperationalOpen realizes boundary sourceRoot mapped htransport)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      erasureOperationalIso realizes boundary sourceRoot mapped htransport)
  intro model boundary sourceRoot mapped htransport args
  let rawMapped := realizes.targetBoundary mapped
  have hexpected :
      (removeWireWireTransport input selection).transportBoundary
        boundary = some rawMapped :=
    realizes.transportBoundary_expected htransport
  have rawRoot : ∀ wire, wire ∈ rawMapped →
      ((input.val.removeRaw selection {}).wires wire).scope =
        (input.val.removeRaw selection {}).root :=
    (removeWireWireTransport input selection)
      |>.transportBoundary_root_scoped sourceRoot hexpected
  let extraction := Classical.choose
    (Concrete.extractChecked_complete input selection)
  let decomposition : Concrete.Decomposition  input selection := {
    frameDomains := {}
    frame := ⟨input.val.removeRaw selection {},
      Concrete.Diagram.removeRaw_wellFormed input selection {}⟩
    frame_eq := rfl
    extraction := extraction
  }
  let spliceResult := Classical.choose
    (Concrete.Splice.Decomposition.reassemble_original_checked_complete
      decomposition)
  have hsplice : Concrete.Splice.Input.spliceChecked
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition) =
        .ok spliceResult :=
    Classical.choose_spec
      (Concrete.Splice.Decomposition.reassemble_original_checked_complete
        decomposition)
  have hcoalescedArity :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
        (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length = boundary.length := by
    change (rawMapped.map
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition).quotientWire).length =
        boundary.length
    simpa using
      (removeWireWireTransport input selection)
        |>.transportBoundary_length hexpected
  let commonArgs := args ∘ Fin.cast hcoalescedArity
  have projection := canonicalErasureProjection orientation decomposition
    hsplice rawMapped rawRoot success.1 model commonArgs
  have hdirect :=
    Concrete.Splice.Decomposition.reassemble_original_source_open_denotation_iff_direct
      decomposition hsplice rawMapped rawRoot model commonArgs
  dsimp only at hdirect
  let source : OperationState  := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  have horigins : rawMapped.map decomposition.frameDomains.wires.origin =
      boundary := by
    simpa [decomposition, rawMapped] using
      removeWireWireTransport_boundary_origins input selection {}
        boundary rawMapped hexpected
  let sourceHostIso : Concrete.OpenIso source.asCheckedOpen.val
      (Concrete.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
        rawMapped rawRoot).val := {
    diagram := Concrete.Iso.refl input.val
    boundary := by
      change boundary.map (Concrete.Iso.refl input.val).wires =
        rawMapped.map decomposition.frameDomains.wires.origin
      simpa [Concrete.Iso.refl, FiniteEquiv.refl] using
        horigins.symm
  }
  have hsourceHost := sourceHostIso.denote_iff source.asCheckedOpen.property
    (Concrete.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
      rawMapped rawRoot).property model args
  let outputArityEq :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
        (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length =
      (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition).plugLayout
        (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
        rawRoot).val.boundary.length := by
    simp [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let directArgs :=
    (commonArgs ∘ Fin.cast outputArityEq.symm) ∘ Fin.cast
      (Concrete.Splice.Decomposition.reassemble_original_output_open_iso
        decomposition rawMapped).boundary_length_eq.symm
  have hdirect' :
      denoteOpen model
          (Concrete.Splice.Input.compiledSpliceSourceOpen
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        denoteOpen model
          (Concrete.Splice.Decomposition.reassembleCanonicalHostOpen decomposition
            rawMapped rawRoot).elaborate directArgs := by
    simpa only [directArgs, outputArityEq] using hdirect
  have hdirectArgs : directArgs =
      (args ∘ Fin.cast sourceHostIso.boundary_length_eq.symm) := by
    funext position
    apply congrArg args
    apply Fin.ext
    rfl
  have hcompilerSource :
      denoteOpen model
          (Concrete.Splice.Input.compiledSpliceSourceOpen
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            hsplice rawMapped rawRoot) commonArgs ↔
        source.denote model args := by
    rw [hdirect', hdirectArgs]
    exact hsourceHost.symm
  have hframeRawEq :
      Concrete.Splice.Decomposition.originalFrameOpenRaw decomposition
          rawMapped = realizes.rawResultOpen mapped := by
    rfl
  let frameIso : Concrete.OpenIso
      (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
        (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
        rawMapped)
      (realizes.rawResultOpen mapped) := by
    rw [← hframeRawEq]
    exact Concrete.Splice.Decomposition.originalCoalescedFrameOpenIso
      decomposition rawMapped
  have hframe := frameIso.denote_iff
    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot_wellFormed
      (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
      (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped rawRoot)
    (realizes.rawResultOpen_wellFormed sourceRoot htransport)
    model commonArgs
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
      denoteOpen model
          (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
            (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
            (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
            rawRoot).elaborate commonArgs ↔
        (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).denote
            model
            operationalArgs := by
    rw [← hopenArgs]
    change denoteOpen model
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
          (Concrete.Splice.Decomposition.originalFragmentInput decomposition)
          (Concrete.Splice.Input.spliceChecked_sound hsplice).2.1 rawMapped
          rawRoot).elaborate commonArgs ↔
      denoteOpen model
        (erasureOperationalOpen realizes boundary sourceRoot mapped htransport).elaborate
        frameArgs
    exact hframe
  dsimp only
  cases orientation with
  | forward =>
      intro hsource
      exact hframe'.mp (projection (hcompilerSource.mpr hsource))
  | backward =>
      intro hopen
      exact hcompilerSource.mp (projection (hframe'.mpr hopen))

theorem SuccessfulReceiptSound.closed
    (receipt : OperationReceipt input)
    (sound : SuccessfulReceiptSound orientation input receipt) :
    SuccessfulOperationSound orientation input receipt.result := by
  intro model
  cases orientation with
  | forward =>
      have hopen := sound model [] (by simp) [] rfl Fin.elim0
      change (OperationState.closed input).denote model Fin.elim0 →
        (OperationState.closed receipt.result).denote model Fin.elim0 at hopen
      simpa only [OperationState.closed_denote_iff] using hopen
  | backward =>
      have hopen := sound model [] (by simp) [] rfl Fin.elim0
      change (OperationState.closed receipt.result).denote model Fin.elim0 →
        (OperationState.closed input).denote model Fin.elim0 at hopen
      simpa only [OperationState.closed_denote_iff] using hopen

end VisualProof.Refinement.Implementation
