import VisualProof.Concrete.Elaboration.SpliceGenerated
import VisualProof.Concrete.Elaboration.SpliceRouteRegion
import VisualProof.Concrete.Elaboration.Generated

/-! Canonical source and receipt endpoints for generic splice elaboration. -/

open VisualProof
open VisualProof.Diagram

namespace VisualProof.Diagram.ContextReplacement

/-- Package an exact source-derived one-hole context and a generated target
identification as a neutral replacement witness. -/
noncomputable def ofSourceContext
    {holeWires : Nat} {holeRels : Theory.RelCtx}
    (source target : OpenDiagram arity)
    (context : DiagramContext source.externalClasses holeWires [] holeRels)
    (before after : Region holeWires holeRels)
    (sourceRebuild : context.fill before = source.body)
    (targetIso : OpenDiagramIso target
      (source.withBody (context.fill after))) :
    ContextReplacement source target where
  holeWires := holeWires
  holeRels := holeRels
  interface := source
  context := context
  before := before
  after := after
  source_iso := {
    external := FiniteEquiv.refl (Fin source.externalClasses)
    boundary := fun _ => rfl
    body := by
      rw [sourceRebuild]
      exact RegionIso.refl source.body
  }
  target_iso := targetIso

end VisualProof.Diagram.ContextReplacement

namespace VisualProof.Concrete

namespace CompiledSite

/-- The intrinsic abstract replacement body determined entirely by the two
source compiler derivations and the checked splice input. -/
noncomputable def spliceBody
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer) :
    Region host.siteContext.length host.siteRels :=
  Region.spliceAt host.siteLocals.length
    (host.siteBody.itemsCast host.siteBody_localCount)
    material.siteBody
    (Fin.cast List.length_append ∘
      material.spliceWireMap normalized.toInput layout admissible
        (host.siteContext ++ host.siteLocals) host.completeContext_exact)
    (fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation)

end CompiledSite

namespace Splice.Input.PlugLayout

/-- Package the exact source-computed open splice target at the execution
state's boundary arity. -/
def outputState (layout : PlugLayout input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (wellFormed : (layout.outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed) : State arity where
  checked := ⟨layout.outputOpenRoot input
    (input.sourceBoundary source frameEq), wellFormed⟩
  boundary_length := by
    change ((input.sourceBoundary source frameEq).map
      (layout.frameWire ∘ input.quotientWire)).length = arity
    simpa only [List.length_map, Splice.Input.sourceBoundary,
      List.length_map] using source.boundary_length

@[simp] theorem outputState_checked_val
    (layout : PlugLayout input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (wellFormed : (layout.outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed) :
    (layout.outputState source frameEq wellFormed).checked.val =
      layout.outputOpenRoot input (input.sourceBoundary source frameEq) := rfl

end Splice.Input.PlugLayout

private def mappedOutputState
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed) : State arity where
  checked := ⟨layout.outputOpenRoot normalized.toInput
    source.checked.val.boundary, targetWellFormed⟩
  boundary_length := by
    simpa only [Splice.Input.PlugLayout.outputOpenRoot, List.length_map] using
      source.boundary_length

private theorem mappedOutputBoundaryLength
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput) :
    (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).boundary.length =
        source.checked.val.boundary.length := by
  simp only [Splice.Input.PlugLayout.outputOpenRoot, List.length_map]
  rfl

private noncomputable def normalizeCastIso
    (diagram : VisualProof.Diagram.OpenDiagram sourceArity)
    (first : sourceArity = middleArity)
    (second : middleArity = targetArity)
    (direct : sourceArity = targetArity) :
    OpenDiagramIso
      ((diagram.castArity first).castArity second)
      (diagram.castArity direct) := by
  subst middleArity
  subst targetArity
  exact OpenDiagramIso.refl _

namespace Splice.Input.PlugLayout.SpliceMappedOpenRouteResult

/-- Identify the generated open root with the exact source compiler context
filled by the intrinsic splice body, before execution-arity transport. -/
private noncomputable def naturalIso
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed)
    (result : SpliceMappedOpenRouteResult normalized layout consistent
      admissible host material) :
    OpenDiagramIso
      (mappedOutputState normalized layout targetWellFormed).checked.elaborate
      ((source.checked.elaborate.withBody
        (host.siteOccurrence.context.fill
          (host.spliceBody normalized layout admissible material))).castArity
            (mappedOutputBoundaryLength normalized layout).symm) := by
  apply OpenDiagramIso.ofArityEq
    (mappedOutputBoundaryLength normalized layout)
    (layout.outputExternalEquiv consistent
      source.checked.val.boundary).symm
  · intro position
    let sourcePosition : Fin source.checked.val.boundary.length :=
      Fin.cast (mappedOutputBoundaryLength normalized layout) position
    change (layout.outputExternalEquiv consistent
      source.checked.val.boundary).symm
        ((layout.outputOpenRoot normalized.toInput
          source.checked.val.boundary).boundaryClass position) =
      source.checked.val.boundaryClass sourcePosition
    have mapped := layout.outputExternalEquiv_boundaryClass consistent
      source.checked.val.boundary sourcePosition
    have mappedPositionEq : Fin.cast (by
          simp [Splice.Input.PlugLayout.outputOpenRoot]
          rfl) sourcePosition =
        position := by
      apply Fin.ext
      rfl
    have mapped' : (layout.outputExternalEquiv consistent
          source.checked.val.boundary)
          (source.checked.val.boundaryClass sourcePosition) =
        (layout.outputOpenRoot normalized.toInput
          source.checked.val.boundary).boundaryClass position := by
      exact mapped.trans (congrArg
        (layout.outputOpenRoot normalized.toInput
          source.checked.val.boundary).boundaryClass mappedPositionEq)
    rw [← mapped']
    exact (layout.outputExternalEquiv consistent
      source.checked.val.boundary).left_inv _
  · have targetBodyEq :
        (mappedOutputState normalized layout
          targetWellFormed).checked.elaborate.body = result.targetBody :=
      CheckedOpen.elaborate_body_eq_of_computation
        (mappedOutputState normalized layout targetWellFormed).checked
        result.target_compiled
    have filled := result.alignment.fill
      (layout.spliceCompilerSiteBodyIso normalized consistent admissible host
        host.kernel host.kernel.blocks material material.kernel
        material.kernel.blocks)
    rw [result.source_context_eq] at filled
    exact targetBodyEq.symm ▸ filled.symm

/-- Put the generated root at the raw source boundary arity and identify it
with the source compiler context filled by the intrinsic splice body. -/
private noncomputable def sourceContextIso
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed)
    (result : SpliceMappedOpenRouteResult normalized layout consistent
      admissible host material) :
    OpenDiagramIso
      (((mappedOutputState normalized layout targetWellFormed).checked.elaborate
        ).castArity
          (mappedOutputBoundaryLength normalized layout))
      (source.checked.elaborate.withBody
        (host.siteOccurrence.context.fill
          (host.spliceBody normalized layout admissible material))) :=
  (result.naturalIso normalized layout consistent admissible host material
    targetWellFormed).castArity
      (mappedOutputBoundaryLength normalized layout)
    |>.trans
      (normalizeCastIso (source.checked.elaborate.withBody
        (host.siteOccurrence.context.fill
          (host.spliceBody normalized layout admissible material)))
        (mappedOutputBoundaryLength normalized layout).symm
        (mappedOutputBoundaryLength normalized layout) rfl)

end Splice.Input.PlugLayout.SpliceMappedOpenRouteResult

namespace State

/-- Exact equality of checked open inputs identifies their canonical
elaborations, including the proof-only casts to the shared state arity. -/
noncomputable def elaborationIsoOfCheckedValEq
    (left right : State arity)
    (checkedEq : left.checked.val = right.checked.val) :
    OpenDiagramIso
      (left.checked.elaborate.castArity left.boundary_length)
      (right.checked.elaborate.castArity right.boundary_length) := by
  have checkedSubtypeEq : left.checked = right.checked :=
    Subtype.ext checkedEq
  rcases left with ⟨leftChecked, leftBoundary⟩
  rcases right with ⟨rightChecked, rightBoundary⟩
  dsimp only at checkedSubtypeEq ⊢
  subst rightChecked
  have boundaryEq : leftBoundary = rightBoundary := Subsingleton.elim _ _
  subst rightBoundary
  exact OpenDiagramIso.refl _

end State

/-- Successful primitive execution already contains the complete checked
splice-input contract. -/
theorem spliceRaw_admissible
    (input : Splice.Input) (operation : OperationReceipt input.frame)
    (success : spliceRaw input = .ok operation) : input.Admissible := by
  unfold spliceRaw at success
  split at success <;> try contradiction
  rename_i checked checkedInput
  exact (Splice.Input.checkInput_sound checkedInput).2

/-- A successful raw splice produces a well-formed instance of its exact
source-computed open target. -/
theorem spliceRaw_receipt_output_wellFormed
    (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (operation : OperationReceipt input.frame) (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt) :
    (({} : Splice.Input.PlugLayout input).outputOpenRoot input
      (input.sourceBoundary source frameEq)).WellFormed := by
  rw [← spliceRaw_receipt_open_result input source frameEq operation receipt
    success packed]
  exact receipt.target.checked.property

/-- Receipt packing changes no generated target: it only supplies the shared
execution arity and proof fields around the exact open result of `spliceRaw`. -/
noncomputable def spliceRaw_receipt_outputStateIso
    (input : Splice.Input) (source : State arity)
    (frameEq : input.frame = source.diagram)
    (operation : OperationReceipt input.frame) (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt) :
    OpenDiagramIso
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length)
      ((({} : Splice.Input.PlugLayout input).outputState source frameEq
        (spliceRaw_receipt_output_wellFormed input source frameEq operation
          receipt success packed)).checked.elaborate.castArity
            (({} : Splice.Input.PlugLayout input).outputState source frameEq
              (spliceRaw_receipt_output_wellFormed input source frameEq
                operation receipt success packed)).boundary_length) := by
  apply State.elaborationIsoOfCheckedValEq
  exact spliceRaw_receipt_open_result input source frameEq operation receipt
    success packed

namespace CompiledSite

/-- Exact proof-side result retained before the execution-arity cast.  Its
single target identification is enough to package the canonical compiler
context without exposing any generated route or compiler witness. -/
structure SpliceResult
    {source : State arity} (normalized : Splice.Input.SourceNormalized source)
    (layout : Splice.Input.PlugLayout normalized.toInput)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer)
    (receipt : Receipt source) where
  target_iso : OpenDiagramIso
    (receipt.target.checked.elaborate.castArity
      (receipt.target.boundary_length.trans source.boundary_length.symm))
    (source.checked.elaborate.withBody
      (host.siteOccurrence.context.fill
        (host.spliceBody normalized layout admissible material)))

/-- The neutral contextual replacement before the state-arity cast.  Its
local fields reduce exactly to the canonical compiled host and splice body. -/
noncomputable def SpliceResult.rawReplacement
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    Diagram.ContextReplacement source.checked.elaborate
      (receipt.target.checked.elaborate.castArity
        (receipt.target.boundary_length.trans source.boundary_length.symm)) :=
  Diagram.ContextReplacement.ofSourceContext source.checked.elaborate _
    host.siteOccurrence.context host.siteBody
    (host.spliceBody normalized layout admissible material)
    host.siteOccurrence_rebuild result.target_iso

@[simp] theorem SpliceResult.rawReplacement_context
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    result.rawReplacement.context = host.siteOccurrence.context := rfl

@[simp] theorem SpliceResult.rawReplacement_before
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    result.rawReplacement.before = host.siteBody := rfl

@[simp] theorem SpliceResult.rawReplacement_after
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    result.rawReplacement.after =
      host.spliceBody normalized layout admissible material := rfl

@[simp] theorem SpliceResult.rawReplacement_targetIso
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    result.rawReplacement.target_iso = result.target_iso := rfl

/-- Cast an exact splice result to the shared execution-state arity without
changing its local context or either local body. -/
noncomputable def SpliceResult.replacement
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    Diagram.ContextReplacement
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) := by
  let casted := result.rawReplacement.castArity source.boundary_length
  let targetNormalization : OpenDiagramIso
      ((receipt.target.checked.elaborate.castArity
        (receipt.target.boundary_length.trans source.boundary_length.symm)
          ).castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) :=
    normalizeCastIso receipt.target.checked.elaborate
      (receipt.target.boundary_length.trans source.boundary_length.symm)
      source.boundary_length receipt.target.boundary_length
  exact casted.iso (OpenDiagramIso.refl _) targetNormalization

@[simp] theorem SpliceResult.replacement_context
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    HEq result.replacement.context host.siteOccurrence.context := by
  change HEq
    (result.rawReplacement.castArity source.boundary_length).context
    host.siteOccurrence.context
  exact (Diagram.ContextReplacement.castArity_context_heq
    result.rawReplacement source.boundary_length).trans HEq.rfl

@[simp] theorem SpliceResult.replacement_before
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    HEq result.replacement.before host.siteBody := by
  change HEq
    (result.rawReplacement.castArity source.boundary_length).before
    host.siteBody
  exact (Diagram.ContextReplacement.castArity_before_heq
    result.rawReplacement source.boundary_length).trans HEq.rfl

@[simp] theorem SpliceResult.replacement_after
    {source : State arity} {normalized : Splice.Input.SourceNormalized source}
    {layout : Splice.Input.PlugLayout normalized.toInput}
    {admissible : normalized.toInput.Admissible}
    {host : CompiledSite source normalized.site}
    {material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer}
    {receipt : Receipt source}
    (result : SpliceResult normalized layout admissible host material receipt) :
    HEq result.replacement.after
      (host.spliceBody normalized layout admissible material) := by
  change HEq
    (result.rawReplacement.castArity source.boundary_length).after
    (host.spliceBody normalized layout admissible material)
  exact (Diagram.ContextReplacement.castArity_after_heq
    result.rawReplacement source.boundary_length).trans HEq.rfl

/-- Construct the exact canonical splice replacement result from the one
source compiler route and the primitive's exact packed receipt. -/
noncomputable def spliceResult
    (source : State arity)
    (normalized : Splice.Input.SourceNormalized source)
    (consistent : normalized.toInput.AttachmentConsistent)
    (operation : OperationReceipt normalized.toInput.frame)
    (receipt : Receipt source)
    (success : spliceRaw normalized.toInput = .ok operation)
    (packed : operation.toReceipt source = some receipt)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer) :
    SpliceResult normalized ({} : Splice.Input.PlugLayout normalized.toInput)
      (spliceRaw_admissible normalized.toInput operation success)
      host material receipt := by
  let layout : Splice.Input.PlugLayout normalized.toInput := {}
  let admissible : normalized.toInput.Admissible :=
    spliceRaw_admissible normalized.toInput operation success
  have packedCast :
      (operation.castInput rfl).toReceipt source = some receipt := by
    simpa using packed
  have generatedWellFormed := spliceRaw_receipt_output_wellFormed
    normalized.toInput source rfl operation receipt success packedCast
  have normalizedBoundary :
      normalized.toInput.sourceBoundary source rfl =
        source.checked.val.boundary := by
    simp [Splice.Input.sourceBoundary, Splice.Input.SourceNormalized.toInput]
  have targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed := by
    rw [← normalizedBoundary]
    exact generatedWellFormed
  let routeResult := layout.compileSpliceMappedOpenRoute normalized consistent
    admissible host material targetWellFormed
  let generated := mappedOutputState normalized layout targetWellFormed
  let boundaryEq := mappedOutputBoundaryLength normalized layout
  let generatedSourceIso : OpenDiagramIso
      (generated.checked.elaborate.castArity boundaryEq)
      (source.checked.elaborate.withBody
        (host.siteOccurrence.context.fill
          (host.spliceBody normalized layout admissible material))) :=
    routeResult.sourceContextIso normalized layout consistent admissible host
      material targetWellFormed
  let receiptIso := spliceRaw_receipt_outputStateIso normalized.toInput source
    rfl operation receipt success packedCast
  have generatedCheckedEq :
      (({} : Splice.Input.PlugLayout normalized.toInput).outputState source rfl
        generatedWellFormed).checked.val = generated.checked.val := by
    change ({} : Splice.Input.PlugLayout normalized.toInput).outputOpenRoot
        normalized.toInput
          (normalized.toInput.sourceBoundary source rfl) =
      layout.outputOpenRoot normalized.toInput source.checked.val.boundary
    rw [normalizedBoundary]
  let outputIso := State.elaborationIsoOfCheckedValEq
    (({} : Splice.Input.PlugLayout normalized.toInput).outputState source rfl
      generatedWellFormed) generated generatedCheckedEq
  let receiptToGenerated := receiptIso.trans outputIso
  let receiptToGeneratedAtSource :=
    receiptToGenerated.castArity source.boundary_length.symm
  let receiptNormalization : OpenDiagramIso
      (((receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length).castArity
          source.boundary_length.symm))
      (receipt.target.checked.elaborate.castArity
        (receipt.target.boundary_length.trans source.boundary_length.symm)) :=
    normalizeCastIso receipt.target.checked.elaborate
      receipt.target.boundary_length source.boundary_length.symm
      (receipt.target.boundary_length.trans source.boundary_length.symm)
  let generatedNormalization : OpenDiagramIso
      ((generated.checked.elaborate.castArity generated.boundary_length
        ).castArity source.boundary_length.symm)
      (generated.checked.elaborate.castArity boundaryEq) :=
    normalizeCastIso generated.checked.elaborate generated.boundary_length
      source.boundary_length.symm boundaryEq
  exact {
    target_iso := receiptNormalization.symm
      |>.trans receiptToGeneratedAtSource
      |>.trans generatedNormalization
      |>.trans generatedSourceIso
  }

/-- Generic splice elaboration is the neutral replacement of the retained
source compiler site by the material compiler body, at the exact primitive
receipt target. -/
noncomputable def splice
    (source : State arity) (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    (consistent : input.AttachmentConsistent)
    (operation : OperationReceipt input.frame)
    (receipt : Receipt source)
    (success : spliceRaw input = .ok operation)
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (host : CompiledSite source
      (Splice.Input.sourceNormalized source input frameEq).site)
    (material : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    Diagram.ContextReplacement
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  let normalized : Splice.Input.SourceNormalized source := {
    pattern := pattern
    site := site
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  have packed' : operation.toReceipt source = some receipt := by
    simpa using packed
  exact (CompiledSite.spliceResult source normalized consistent operation
    receipt success packed' host material).replacement

end CompiledSite

end VisualProof.Concrete
