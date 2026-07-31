import VisualProof.Diagram.Concrete.WirePrimitive.Content
import VisualProof.Diagram.Concrete.WirePrimitive.UniformSiteFactorization

namespace VisualProof

namespace ConcreteWirePrimitive

open WirePrimitive
open WirePrimitive.ConcreteFactorization

namespace ContentAlignment

theorem retainedWire_of_ne
    (base : CheckedDiagram definitions)
    (removed candidate : base.val.WireId)
    (different : candidate ≠ removed) :
    candidate ∈
      ConcreteWireQuantifier.Internal.retainedWires base [removed] := by
  unfold ConcreteWireQuantifier.Internal.retainedWires
    ConcreteDiagram.wiresList
  apply List.mem_filter.mpr
  exact ⟨Data.Finite.mem_allFin candidate, by simp [different]⟩

theorem retainedWire_of_ne_pair
    (base : CheckedDiagram definitions)
    (first second candidate : base.val.WireId)
    (differentFirst : candidate ≠ first)
    (differentSecond : candidate ≠ second) :
    candidate ∈
      ConcreteWireQuantifier.Internal.retainedWires base
        [first, second] := by
  unfold ConcreteWireQuantifier.Internal.retainedWires
    ConcreteDiagram.wiresList
  apply List.mem_filter.mpr
  exact
    ⟨Data.Finite.mem_allFin candidate,
      by simp [differentFirst, differentSecond]⟩

theorem not_mem_removed_of_retained
    (base : CheckedDiagram definitions)
    (removed : List base.val.WireId)
    (candidate : base.val.WireId)
    (retained :
      candidate ∈
        ConcreteWireQuantifier.Internal.retainedWires base removed) :
    candidate ∉ removed := by
  exact of_decide_eq_true (List.mem_filter.mp retained).2

def cutForwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire]) :
    source.val.WireId → result.checked.val.WireId :=
  fun candidate =>
    if same : candidate = wire then
      result.targetWire
    else
      core.forwardRetainedWire candidate (by
        rw [sourceExact]
        exact retainedWire_of_ne source wire candidate same)

theorem cutForwardWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (candidate : source.val.WireId) :
    (result.checked.val.wires
        (cutForwardWire result core sourceExact candidate)).sig =
      (source.val.wires candidate).sig := by
  unfold cutForwardWire
  split
  · rename_i same
    subst candidate
    exact result.targetWire_signature
  · exact core.forwardRetainedWire_signature _ _

def cutBackwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (targetExact : core.targetRemovedWires = [result.targetWire]) :
    result.checked.val.WireId → source.val.WireId :=
  fun candidate =>
    if same : candidate = result.targetWire then
      wire
    else
      core.backwardRetainedWire candidate (by
        rw [targetExact]
        exact
          retainedWire_of_ne result.checked result.targetWire candidate same)

theorem cutBackwardWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (targetExact : core.targetRemovedWires = [result.targetWire])
    (candidate : result.checked.val.WireId) :
    (source.val.wires
        (cutBackwardWire result core targetExact candidate)).sig =
      (result.checked.val.wires candidate).sig := by
  unfold cutBackwardWire
  split
  · rename_i same
    subst candidate
    exact result.targetWire_signature.symm
  · exact core.backwardRetainedWire_signature _ _

theorem cutBackward_forwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (targetExact : core.targetRemovedWires = [result.targetWire])
    (candidate : source.val.WireId) :
    cutBackwardWire result core targetExact
        (cutForwardWire result core sourceExact candidate) =
      candidate := by
  unfold cutForwardWire
  split
  · rename_i same
    subst candidate
    simp [cutBackwardWire]
  · rename_i different
    let retained :=
      retainedWire_of_ne source wire candidate different
    let targetRetained :=
      core.targetErasure.originalWire_mem_retained
        (core.coreIso.wires
          (core.sourceErasure.retainedWire candidate (by
            simpa [sourceExact] using retained)))
    unfold cutBackwardWire
    split
    · rename_i generated
      have notRemoved :=
        not_mem_removed_of_retained result.checked
          core.targetRemovedWires _ targetRetained
      have generatedExact :
          core.targetErasure.originalWire
              (core.coreIso.wires
                (core.sourceErasure.retainedWire candidate (by
                  simpa [sourceExact] using retained))) =
            result.targetWire := by
        simpa only [CommonCoreReceipt.forwardRetainedWire] using generated
      rw [generatedExact] at notRemoved
      exact (notRemoved (by rw [targetExact]; simp)).elim
    · exact
        core.backward_forwardRetainedWire candidate (by
          simpa [sourceExact] using retained)

theorem cutForward_backwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (targetExact : core.targetRemovedWires = [result.targetWire])
    (candidate : result.checked.val.WireId) :
    cutForwardWire result core sourceExact
        (cutBackwardWire result core targetExact candidate) =
      candidate := by
  unfold cutBackwardWire
  split
  · rename_i same
    subst candidate
    simp [cutForwardWire]
  · rename_i different
    let retained :=
      retainedWire_of_ne result.checked result.targetWire candidate
        different
    let sourceRetained :=
      core.sourceErasure.originalWire_mem_retained
        (core.coreIso.wires.symm
          (core.targetErasure.retainedWire candidate (by
            simpa [targetExact] using retained)))
    unfold cutForwardWire
    split
    · rename_i generated
      have notRemoved :=
        not_mem_removed_of_retained source core.sourceRemovedWires _
          sourceRetained
      have generatedExact :
          core.sourceErasure.originalWire
              (core.coreIso.wires.symm
                (core.targetErasure.retainedWire candidate (by
                  simpa [targetExact] using retained))) =
            wire := by
        simpa only [CommonCoreReceipt.backwardRetainedWire] using generated
      rw [generatedExact] at notRemoved
      exact (notRemoved (by rw [sourceExact]; simp)).elim
    · exact
        core.forward_backwardRetainedWire candidate (by
          simpa [targetExact] using retained)

def splitForwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire]) :
    source.val.WireId → result.checked.val.WireId :=
  fun candidate =>
    if same : candidate = wire then
      result.firstWire
    else
      core.forwardRetainedWire candidate (by
        rw [sourceExact]
        exact retainedWire_of_ne source wire candidate same)

theorem splitForwardWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (candidate : source.val.WireId) :
    (result.checked.val.wires
        (splitForwardWire result core sourceExact candidate)).sig =
      (source.val.wires candidate).sig := by
  unfold splitForwardWire
  split
  · rename_i same
    subst candidate
    exact result.firstWire_signature
  · exact core.forwardRetainedWire_signature _ _

def splitBackwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (targetExact :
      core.targetRemovedWires = [result.firstWire, result.secondWire]) :
    result.checked.val.WireId → source.val.WireId :=
  fun candidate =>
    if first : candidate = result.firstWire then
      wire
    else if second : candidate = result.secondWire then
      wire
    else
      core.backwardRetainedWire candidate (by
        rw [targetExact]
        exact
          retainedWire_of_ne_pair result.checked result.firstWire
            result.secondWire candidate first second)

theorem splitBackwardWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (targetExact :
      core.targetRemovedWires = [result.firstWire, result.secondWire])
    (candidate : result.checked.val.WireId) :
    (source.val.wires
        (splitBackwardWire result core targetExact candidate)).sig =
      (result.checked.val.wires candidate).sig := by
  unfold splitBackwardWire
  split
  · rename_i first
    subst candidate
    exact result.firstWire_signature.symm
  · split
    · rename_i second
      subst candidate
      exact result.secondWire_signature.symm
    · exact core.backwardRetainedWire_signature _ _

theorem splitBackward_forwardWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (targetExact :
      core.targetRemovedWires = [result.firstWire, result.secondWire])
    (candidate : source.val.WireId) :
    splitBackwardWire result core targetExact
        (splitForwardWire result core sourceExact candidate) =
      candidate := by
  unfold splitForwardWire
  split
  · rename_i same
    subst candidate
    simp [splitBackwardWire]
  · rename_i different
    let retained :=
      retainedWire_of_ne source wire candidate different
    let targetRetained :=
      core.targetErasure.originalWire_mem_retained
        (core.coreIso.wires
          (core.sourceErasure.retainedWire candidate (by
            simpa [sourceExact] using retained)))
    unfold splitBackwardWire
    split
    · rename_i generated
      have notRemoved :=
        not_mem_removed_of_retained result.checked
          core.targetRemovedWires _ targetRetained
      have generatedExact :
          core.targetErasure.originalWire
              (core.coreIso.wires
                (core.sourceErasure.retainedWire candidate (by
                  simpa [sourceExact] using retained))) =
            result.firstWire := by
        simpa only [CommonCoreReceipt.forwardRetainedWire] using generated
      rw [generatedExact] at notRemoved
      exact (notRemoved (by rw [targetExact]; simp)).elim
    · split
      · rename_i generated
        have notRemoved :=
          not_mem_removed_of_retained result.checked
            core.targetRemovedWires _ targetRetained
        have generatedExact :
            core.targetErasure.originalWire
                (core.coreIso.wires
                  (core.sourceErasure.retainedWire candidate (by
                    simpa [sourceExact] using retained))) =
              result.secondWire := by
          simpa only [CommonCoreReceipt.forwardRetainedWire] using generated
        rw [generatedExact] at notRemoved
        exact (notRemoved (by rw [targetExact]; simp)).elim
      · exact
          core.backward_forwardRetainedWire candidate (by
            simpa [sourceExact] using retained)

theorem splitForward_backwardWire_of_ne_second
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (core : CommonCoreReceipt source result.checked)
    (sourceExact : core.sourceRemovedWires = [wire])
    (targetExact :
      core.targetRemovedWires = [result.firstWire, result.secondWire])
    (candidate : result.checked.val.WireId)
    (notSecond : candidate ≠ result.secondWire) :
    splitForwardWire result core sourceExact
        (splitBackwardWire result core targetExact candidate) =
      candidate := by
  unfold splitBackwardWire
  split
  · rename_i first
    subst candidate
    simp [splitForwardWire]
  · rename_i notFirst
    let retained :=
      retainedWire_of_ne_pair result.checked result.firstWire
        result.secondWire candidate notFirst notSecond
    let sourceRetained :=
      core.sourceErasure.originalWire_mem_retained
        (core.coreIso.wires.symm
          (core.targetErasure.retainedWire candidate (by
            simpa [targetExact] using retained)))
    unfold splitForwardWire
    split
    · rename_i generated
      have notRemoved :=
        not_mem_removed_of_retained source core.sourceRemovedWires _
          sourceRetained
      have generatedExact :
          core.sourceErasure.originalWire
              (core.coreIso.wires.symm
                (core.targetErasure.retainedWire candidate (by
                  simpa [targetExact] using retained))) =
            wire := by
        simpa only [CommonCoreReceipt.backwardRetainedWire] using generated
      rw [generatedExact] at notRemoved
      exact (notRemoved (by rw [sourceExact]; simp)).elim
    · exact
        core.forward_backwardRetainedWire candidate (by
          simpa [targetExact] using retained)

/--
Checker-owned bidirectional alignment of two visible concrete wire contexts.
The typed renamings are derived from concrete wire maps whose visibility is
verified exhaustively; no caller supplies a variable-level correspondence.
-/
structure VisibleWireAlignment
    (source target : CheckedDiagram definitions)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val) where
  forwardWire : source.val.WireId → target.val.WireId
  backwardWire : target.val.WireId → source.val.WireId
  forwardSignature :
    ∀ wire,
      (target.val.wires (forwardWire wire)).sig =
        (source.val.wires wire).sig
  backwardSignature :
    ∀ wire,
      (source.val.wires (backwardWire wire)).sig =
        (target.val.wires wire).sig
  private forward_visible :
    ∀ wire, wire ∈ sourceContext.ids → forwardWire wire ∈ targetContext.ids
  private backward_visible :
    ∀ wire, wire ∈ targetContext.ids → backwardWire wire ∈ sourceContext.ids

def checkVisibleWireAlignment
    (source target : CheckedDiagram definitions)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val)
    (forwardWire : source.val.WireId → target.val.WireId)
    (backwardWire : target.val.WireId → source.val.WireId)
    (forwardSignature :
      ∀ wire,
        (target.val.wires (forwardWire wire)).sig =
          (source.val.wires wire).sig)
    (backwardSignature :
      ∀ wire,
        (source.val.wires (backwardWire wire)).sig =
          (target.val.wires wire).sig) :
    Option
      (VisibleWireAlignment source target sourceContext targetContext) :=
  if forwardExact :
      sourceContext.ids.all fun wire =>
        decide (forwardWire wire ∈ targetContext.ids) then
    if backwardExact :
        targetContext.ids.all fun wire =>
          decide (backwardWire wire ∈ sourceContext.ids) then
      some
        {
          forwardWire := forwardWire
          backwardWire := backwardWire
          forwardSignature := forwardSignature
          backwardSignature := backwardSignature
          forward_visible := by
            intro wire member
            exact of_decide_eq_true
              ((List.all_eq_true.mp forwardExact) wire member)
          backward_visible := by
            intro wire member
            exact of_decide_eq_true
              ((List.all_eq_true.mp backwardExact) wire member)
        }
    else
      none
  else
    none

namespace VisibleWireAlignment

def forward
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    (alignment :
      VisibleWireAlignment source target sourceContext targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    source.val target.val sourceContext.ids targetContext.ids
    alignment.forwardWire alignment.forwardSignature
    alignment.forward_visible

def backward
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    (alignment :
      VisibleWireAlignment source target sourceContext targetContext) :
    WireRenaming targetContext.sigs sourceContext.sigs :=
  InsertionCompilation.NaturalityInternal.contextEmbedding
    target.val source.val targetContext.ids sourceContext.ids
    alignment.backwardWire alignment.backwardSignature
    alignment.backward_visible

theorem forward_origin
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    (alignment :
      VisibleWireAlignment source target sourceContext targetContext)
    {signature : Sig}
    (value : Var sourceContext.sigs signature) :
    ConcreteElaboration.WireContext.origin target.val targetContext.ids
        (alignment.forward value) =
      alignment.forwardWire
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids value) :=
  InsertionCompilation.NaturalityInternal.contextEmbedding_origin
    source.val target.val sourceContext.ids targetContext.ids
    alignment.forwardWire alignment.forwardSignature
    alignment.forward_visible value

theorem backward_origin
    {definitions : List (List Sig)}
    {source target : CheckedDiagram definitions}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    (alignment :
      VisibleWireAlignment source target sourceContext targetContext)
    {signature : Sig}
    (value : Var targetContext.sigs signature) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (alignment.backward value) =
      alignment.backwardWire
        (ConcreteElaboration.WireContext.origin target.val
          targetContext.ids value) :=
  InsertionCompilation.NaturalityInternal.contextEmbedding_origin
    target.val source.val targetContext.ids sourceContext.ids
    alignment.backwardWire alignment.backwardSignature
    alignment.backward_visible value

end VisibleWireAlignment

private def varDecEq :
    (left right : Var context signature) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match varDecEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private instance : DecidableEq (Var context signature) :=
  varDecEq

/-- Add one distinguished variable ahead of a fallback typed renaming. -/
def separateVar
    (distinguished : Var source distinguishedSignature)
    (fallback : WireRenaming source target) :
    WireRenaming source (distinguishedSignature :: target) :=
  fun {signature} value =>
    if sameSignature : signature = distinguishedSignature then
      if sameVariable :
          sameSignature ▸ value = distinguished then
        sameSignature.symm ▸
          (.here :
            Var (distinguishedSignature :: target)
              distinguishedSignature)
      else
        .there (fallback value)
    else
      .there (fallback value)

/-- Weaken every source variable through one fresh common-context slot. -/
def weakenOne :
    WireRenaming source (signature :: source) :=
  fun {_} value => .there value

/-- Weaken every source variable through two fresh common-context slots. -/
def weakenTwo :
    WireRenaming source (first :: second :: source) :=
  fun {_} value => .there (.there value)

/--
The shared outer context around two possibly different local binder blocks.
Every ordinary conjunction frame, cut, and ancestor binder is retained
exactly; only the terminal scope-local binder block may differ.
-/
inductive PairedContext
    (definitions : List (List Sig))
    (sourceLocal targetLocal siteOuter : List Sig) :
    {outer : List Sig} →
      DiagramContext definitions (sourceLocal ++ siteOuter) outer →
      DiagramContext definitions (targetLocal ++ siteOuter) outer →
      Type
  | terminal :
      PairedContext definitions sourceLocal targetLocal siteOuter
        (DiagramContext.bindMany sourceLocal
          (.hole :
            DiagramContext definitions
              (sourceLocal ++ siteOuter) (sourceLocal ++ siteOuter)))
        (DiagramContext.bindMany targetLocal
          (.hole :
            DiagramContext definitions
              (targetLocal ++ siteOuter) (targetLocal ++ siteOuter)))
  | surround
      (leading suffix : ItemSeq definitions outer)
      (inner : PairedContext definitions sourceLocal targetLocal siteOuter
        sourceInner targetInner) :
      PairedContext definitions sourceLocal targetLocal siteOuter
        (.surround leading sourceInner suffix)
        (.surround leading targetInner suffix)
  | cut
      (inner : PairedContext definitions sourceLocal targetLocal siteOuter
        sourceInner targetInner) :
      PairedContext definitions sourceLocal targetLocal siteOuter
        (.cut sourceInner) (.cut targetInner)
  | bind
      {outer : List Sig}
      (signature : Sig)
      {sourceInner :
        DiagramContext definitions
          (sourceLocal ++ siteOuter) (signature :: outer)}
      {targetInner :
        DiagramContext definitions
          (targetLocal ++ siteOuter) (signature :: outer)}
      (inner : PairedContext definitions sourceLocal targetLocal siteOuter
        sourceInner targetInner) :
      PairedContext definitions sourceLocal targetLocal siteOuter
        (.bind signature sourceInner) (.bind signature targetInner)

private def contextDecEq :
    (left right : DiagramContext definitions hole outer) →
      Decidable (left = right)
  | .hole, .hole => isTrue rfl
  | .surround leftLeading leftInner leftSuffix,
      .surround rightLeading rightInner rightSuffix =>
      if leading : leftLeading = rightLeading then
        match contextDecEq leftInner rightInner with
        | isTrue inner =>
            if suffix : leftSuffix = rightSuffix then
              isTrue (by cases leading; cases inner; cases suffix; rfl)
            else
              isFalse (fun equality => by cases equality; exact suffix rfl)
        | isFalse different =>
            isFalse (fun equality => by cases equality; exact different rfl)
      else
        isFalse (fun equality => by cases equality; exact leading rfl)
  | .cut leftInner, .cut rightInner =>
      match contextDecEq leftInner rightInner with
      | isTrue inner => isTrue (by cases inner; rfl)
      | isFalse different =>
          isFalse (fun equality => by cases equality; exact different rfl)
  | .bind leftSignature leftInner, .bind rightSignature rightInner =>
      if signature : leftSignature = rightSignature then
        by
          subst rightSignature
          exact
            match contextDecEq leftInner rightInner with
            | isTrue inner => isTrue (by cases inner; rfl)
            | isFalse different =>
                isFalse (fun equality => by
                  cases equality
                  exact different rfl)
      else
        isFalse (fun equality => by cases equality; exact signature rfl)
  | .hole, .surround _ _ _ =>
      isFalse (fun equality => by cases equality)
  | .hole, .cut _ => isFalse (fun equality => by cases equality)
  | .hole, .bind _ _ => isFalse (fun equality => by cases equality)
  | .surround _ _ _, .hole =>
      isFalse (fun equality => by cases equality)
  | .surround _ _ _, .cut _ =>
      isFalse (fun equality => by cases equality)
  | .surround _ _ _, .bind _ _ =>
      isFalse (fun equality => by cases equality)
  | .cut _, .hole => isFalse (fun equality => by cases equality)
  | .cut _, .surround _ _ _ =>
      isFalse (fun equality => by cases equality)
  | .cut _, .bind _ _ => isFalse (fun equality => by cases equality)
  | .bind _ _, .hole => isFalse (fun equality => by cases equality)
  | .bind _ _, .surround _ _ _ =>
      isFalse (fun equality => by cases equality)
  | .bind _ _, .cut _ => isFalse (fun equality => by cases equality)

private instance :
    DecidableEq (DiagramContext definitions hole outer) :=
  contextDecEq

private def checkPairedTerminal
    (sourceLocal targetLocal siteOuter : List Sig)
    {outer : List Sig}
    (sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer)
    (targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer) :
    Option
      (PairedContext definitions sourceLocal targetLocal siteOuter
        sourceContext targetContext) :=
  if outerExact : outer = siteOuter then
    by
      subst outer
      let sourceTerminal :=
        DiagramContext.bindMany sourceLocal
          (.hole :
            DiagramContext definitions
              (sourceLocal ++ siteOuter) (sourceLocal ++ siteOuter))
      let targetTerminal :=
        DiagramContext.bindMany targetLocal
          (.hole :
            DiagramContext definitions
              (targetLocal ++ siteOuter) (targetLocal ++ siteOuter))
      if sourceExact : sourceContext = sourceTerminal then
        if targetExact : targetContext = targetTerminal then
          subst sourceContext
          subst targetContext
          exact some .terminal
        else
          exact none
      else
        exact none
  else
    none

/--
Check that two site contexts retain the same complete outer spine while their
terminal scope-local binder blocks are exactly the supplied ordered lists.
-/
def checkPairedContext
    (sourceLocal targetLocal siteOuter : List Sig)
    {outer : List Sig}
    (sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer)
    (targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer) :
    Option
      (PairedContext definitions sourceLocal targetLocal siteOuter
        sourceContext targetContext) :=
  match checkPairedTerminal sourceLocal targetLocal siteOuter
      sourceContext targetContext with
  | some terminalReceipt => some terminalReceipt
  | none =>
      match sourceContext, targetContext with
      | .surround sourceLeading sourceInner sourceSuffix,
          .surround targetLeading targetInner targetSuffix =>
          if leading : sourceLeading = targetLeading then
            if suffix : sourceSuffix = targetSuffix then
              by
                subst targetLeading
                subst targetSuffix
                exact
                  (checkPairedContext sourceLocal targetLocal siteOuter
                    sourceInner targetInner).map
                    (PairedContext.surround sourceLeading sourceSuffix)
            else
              none
          else
            none
      | .cut sourceInner, .cut targetInner =>
          (checkPairedContext sourceLocal targetLocal siteOuter
            sourceInner targetInner).map PairedContext.cut
      | .bind sourceSignature sourceInner,
          .bind targetSignature targetInner =>
          if signature : sourceSignature = targetSignature then
            by
              subst targetSignature
              exact
                (checkPairedContext sourceLocal targetLocal siteOuter
                  sourceInner targetInner).map
                  (PairedContext.bind sourceSignature)
          else
            none
      | _, _ => none
termination_by sizeOf sourceContext

/--
The paired context checker is semantically complete: one equivalence at the
two terminal local-binder blocks propagates through the entire retained outer
spine.
-/
theorem PairedContext.denotes
    {sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer}
    {targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer}
    (paired :
      PairedContext definitions sourceLocal targetLocal siteOuter
        sourceContext targetContext)
    (sourceBody : Region definitions (sourceLocal ++ siteOuter))
    (targetBody : Region definitions (targetLocal ++ siteOuter))
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre outer)
    (localLaw :
      ∀ siteEnv : Env pre siteOuter,
        denoteRegion pre definitionEnv siteEnv
            ((DiagramContext.bindMany sourceLocal
              (.hole :
                DiagramContext definitions
                  (sourceLocal ++ siteOuter)
                  (sourceLocal ++ siteOuter))).fill sourceBody) ↔
          denoteRegion pre definitionEnv siteEnv
            ((DiagramContext.bindMany targetLocal
              (.hole :
                DiagramContext definitions
                  (targetLocal ++ siteOuter)
                  (targetLocal ++ siteOuter))).fill targetBody)) :
    denoteRegion pre definitionEnv env (sourceContext.fill sourceBody) ↔
      denoteRegion pre definitionEnv env (targetContext.fill targetBody) := by
  induction paired with
  | terminal =>
      exact localLaw env
  | surround leading suffix inner induction =>
      simp only [DiagramContext.fill, Region.denote_surround]
      exact
        and_congr Iff.rfl
          (and_congr (induction env) Iff.rfl)
  | cut inner induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      exact not_congr (induction env)
  | bind signature inner induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      constructor
      · rintro ⟨value, holds⟩
        exact ⟨value, (induction (env.extend value)).mp holds⟩
      · rintro ⟨value, holds⟩
        exact ⟨value, (induction (env.extend value)).mpr holds⟩

/-- Ordered signatures bound directly at one concrete region. -/
def localSignatures
    (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) : List Sig :=
  (diagram.wiresAt region).map fun wire => (diagram.wires wire).sig

/--
Checker-owned decomposition of two compiled sites into their possibly
different local binder blocks and one exactly shared outer context.
-/
structure SiteContextFactorization
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    (sourceScope : SiteCompilation source sourceSite)
    (targetScope : SiteCompilation target targetSite) where
  siteOuter : List Sig
  private source_visible_exact :
    sourceScope.frame.visible.sigs =
      localSignatures source.val sourceSite ++ siteOuter
  private target_visible_exact :
    targetScope.frame.visible.sigs =
      localSignatures target.val targetSite ++ siteOuter
  paired :
    PairedContext definitions
      (localSignatures source.val sourceSite)
      (localSignatures target.val targetSite)
      siteOuter
      (source_visible_exact ▸ sourceScope.frame.context)
      (target_visible_exact ▸ targetScope.frame.context)

theorem SiteContextFactorization.sourceVisibleExact
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope) :
    sourceScope.frame.visible.sigs =
      localSignatures source.val sourceSite ++ context.siteOuter :=
  context.source_visible_exact

theorem SiteContextFactorization.targetVisibleExact
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope) :
    targetScope.frame.visible.sigs =
      localSignatures target.val targetSite ++ context.siteOuter :=
  context.target_visible_exact

def SiteContextFactorization.pairedExact
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope) :
    PairedContext definitions
      (localSignatures source.val sourceSite)
      (localSignatures target.val targetSite)
      context.siteOuter
      (context.sourceVisibleExact ▸ sourceScope.frame.context)
      (context.targetVisibleExact ▸ targetScope.frame.context) := by
  have sourceProof :
      context.source_visible_exact = context.sourceVisibleExact :=
    Subsingleton.elim _ _
  have targetProof :
      context.target_visible_exact = context.targetVisibleExact :=
    Subsingleton.elim _ _
  simpa [sourceProof, targetProof] using context.paired

def SiteContextFactorization.sourceBody
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (body : Region definitions sourceScope.frame.visible.sigs) :
    Region definitions
      (localSignatures source.val sourceSite ++ context.siteOuter) :=
  context.source_visible_exact ▸ body

def SiteContextFactorization.targetBody
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (body : Region definitions targetScope.frame.visible.sigs) :
    Region definitions
      (localSignatures target.val targetSite ++ context.siteOuter) :=
  context.target_visible_exact ▸ body

/-- Transport a source local-block environment back to its compiled frame. -/
def SiteContextFactorization.sourceEnvironment
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env :
      Env pre
        (localSignatures source.val sourceSite ++ context.siteOuter)) :
    Env pre sourceScope.frame.visible.sigs :=
  context.source_visible_exact.symm ▸ env

/-- Transport a target local-block environment back to its compiled frame. -/
def SiteContextFactorization.targetEnvironment
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env :
      Env pre
        (localSignatures target.val targetSite ++ context.siteOuter)) :
    Env pre targetScope.frame.visible.sigs :=
  context.target_visible_exact.symm ▸ env

/-- Transport a compiled source-frame environment to its local-block view. -/
def SiteContextFactorization.sourceLocalEnvironment
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre sourceScope.frame.visible.sigs) :
    Env pre
      (localSignatures source.val sourceSite ++ context.siteOuter) :=
  context.source_visible_exact ▸ env

/-- Transport a compiled target-frame environment to its local-block view. -/
def SiteContextFactorization.targetLocalEnvironment
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre targetScope.frame.visible.sigs) :
    Env pre
      (localSignatures target.val targetSite ++ context.siteOuter) :=
  context.target_visible_exact ▸ env

private theorem transportedEnvironment_apply
    {left right : List Sig}
    (same : left = right)
    (env : Env pre left)
    {signature : Sig}
    (value : Var left signature) :
    (same ▸ env) signature (same ▸ value) =
      env signature value := by
  cases same
  rfl

private theorem transport_symm_transport_var
    {left right : List Sig}
    (same : left = right)
    {signature : Sig}
    (value : Var right signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem transport_symm_transport
    {left right : List Sig}
    (same : left = right)
    {motive : List Sig → Sort _}
    (value : motive left) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem denoteTransportedBody
    {left right : List Sig}
    (same : left = right)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre right)
    (body : Region definitions left) :
    denoteRegion pre definitionEnv env (same ▸ body) ↔
      denoteRegion pre definitionEnv (same.symm ▸ env) body := by
  cases same
  rfl

/-- Localizing and restoring a compiled source environment is exact. -/
theorem SiteContextFactorization.sourceEnvironment_local
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre sourceScope.frame.visible.sigs) :
    context.sourceEnvironment
        (context.sourceLocalEnvironment env) =
      env := by
  simpa [SiteContextFactorization.sourceEnvironment,
    SiteContextFactorization.sourceLocalEnvironment] using
      transport_symm_transport context.source_visible_exact env

/-- Localizing and restoring a compiled target environment is exact. -/
theorem SiteContextFactorization.targetEnvironment_local
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre targetScope.frame.visible.sigs) :
    context.targetEnvironment
        (context.targetLocalEnvironment env) =
      env := by
  simpa [SiteContextFactorization.targetEnvironment,
    SiteContextFactorization.targetLocalEnvironment] using
      transport_symm_transport context.target_visible_exact env

/-- Source-body transport preserves denotation exactly. -/
theorem SiteContextFactorization.sourceBody_denotes
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        (localSignatures source.val sourceSite ++ context.siteOuter))
    (body : Region definitions sourceScope.frame.visible.sigs) :
    denoteRegion pre definitionEnv env (context.sourceBody body) ↔
      denoteRegion pre definitionEnv
        (context.sourceEnvironment env) body := by
  simpa [SiteContextFactorization.sourceBody,
    SiteContextFactorization.sourceEnvironment] using
      denoteTransportedBody context.source_visible_exact pre definitionEnv
        env body

/-- Target-body transport preserves denotation exactly. -/
theorem SiteContextFactorization.targetBody_denotes
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        (localSignatures target.val targetSite ++ context.siteOuter))
    (body : Region definitions targetScope.frame.visible.sigs) :
    denoteRegion pre definitionEnv env (context.targetBody body) ↔
      denoteRegion pre definitionEnv
        (context.targetEnvironment env) body := by
  simpa [SiteContextFactorization.targetBody,
    SiteContextFactorization.targetEnvironment] using
      denoteTransportedBody context.target_visible_exact pre definitionEnv
        env body

private theorem castContextFill
    {left right outer : List Sig}
    (same : left = right)
    (context : DiagramContext definitions left outer)
    (body : Region definitions left) :
    (same ▸ context).fill (same ▸ body) = context.fill body := by
  cases same
  rfl

/-- Close one terminal equivalence through the original compiled contexts. -/
theorem SiteContextFactorization.closeDenotes
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (localLaw :
      ∀ siteEnv : Env pre context.siteOuter,
        denoteRegion pre definitionEnv siteEnv
            ((DiagramContext.bindMany
              (localSignatures source.val sourceSite)
              (.hole :
                DiagramContext definitions
                  (localSignatures source.val sourceSite ++
                    context.siteOuter)
                  (localSignatures source.val sourceSite ++
                    context.siteOuter))).fill
              (context.sourceBody sourceScope.frame.siteBody)) ↔
          denoteRegion pre definitionEnv siteEnv
            ((DiagramContext.bindMany
              (localSignatures target.val targetSite)
              (.hole :
                DiagramContext definitions
                  (localSignatures target.val targetSite ++
                    context.siteOuter)
                  (localSignatures target.val targetSite ++
                    context.siteOuter))).fill
              (context.targetBody targetScope.frame.siteBody))) :
    denoteRegion pre definitionEnv Env.empty
        (sourceScope.frame.context.fill sourceScope.frame.siteBody) ↔
      denoteRegion pre definitionEnv Env.empty
        (targetScope.frame.context.fill targetScope.frame.siteBody) := by
  have propagated :=
    context.paired.denotes
      (context.sourceBody sourceScope.frame.siteBody)
      (context.targetBody targetScope.frame.siteBody)
      pre definitionEnv Env.empty localLaw
  simpa [SiteContextFactorization.sourceBody,
    SiteContextFactorization.targetBody, castContextFill] using propagated

/--
Derive the exact shared outer context after splitting off each site's ordered
local binder block.
-/
def checkSiteContextFactorization
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    (sourceScope : SiteCompilation source sourceSite)
    (targetScope : SiteCompilation target targetSite) :
    Option (SiteContextFactorization sourceScope targetScope) := by
  let sourceLocal := localSignatures source.val sourceSite
  let targetLocal := localSignatures target.val targetSite
  let siteOuter := sourceScope.frame.visible.sigs.drop sourceLocal.length
  if sourceExact :
      sourceScope.frame.visible.sigs = sourceLocal ++ siteOuter then
    if targetExact :
        targetScope.frame.visible.sigs = targetLocal ++ siteOuter then
      let sourceContext := sourceExact ▸ sourceScope.frame.context
      let targetContext := targetExact ▸ targetScope.frame.context
      match checkPairedContext sourceLocal targetLocal siteOuter
          sourceContext targetContext with
      | none => exact none
      | some paired =>
          exact
            some
              ⟨siteOuter, sourceExact, targetExact, paired⟩
    else
      exact none
  else
    exact none

/--
One typed renaming maps every variable embedded from a common suffix to the
corresponding variable embedded in the target context.
-/
structure SuffixAgreement
    (suffix source target : List Sig)
    (sourceEmbed : WireRenaming suffix source)
    (targetEmbed : WireRenaming suffix target)
    (rho : WireRenaming source target) : Type where
  agrees :
    ∀ {signature : Sig} (value : Var suffix signature),
      rho (sourceEmbed value) = targetEmbed value

/-- Exhaustively check a typed renaming on every variable of one suffix. -/
def checkSuffixAgreement
    (suffix : List Sig)
    (sourceEmbed : WireRenaming suffix source)
    (targetEmbed : WireRenaming suffix target)
    (rho : WireRenaming source target) :
    Option
      (SuffixAgreement suffix source target sourceEmbed targetEmbed
        rho) := by
  match suffix with
  | [] =>
      exact
        some
          ⟨fun value => nomatch value⟩
  | signature :: rest =>
      if headExact :
          rho
              (sourceEmbed
                (.here : Var (signature :: rest) signature)) =
            targetEmbed
              (.here : Var (signature :: rest) signature) then
        let sourceTail : WireRenaming rest source :=
          fun {_} value => sourceEmbed (.there value)
        let targetTail : WireRenaming rest target :=
          fun {_} value => targetEmbed (.there value)
        match checkSuffixAgreement rest sourceTail targetTail rho with
        | none => exact none
        | some tail =>
            exact
              some
                ⟨by
                  intro current value
                  cases value with
                  | here => exact headExact
                  | there value => exact tail.agrees value⟩
      else
        exact none

def SiteContextFactorization.sourceOuterEmbedding
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope) :
    WireRenaming context.siteOuter sourceScope.frame.visible.sigs :=
  fun {_} value =>
    context.source_visible_exact.symm ▸
      Var.appendRight
        (localSignatures source.val sourceSite) value

def SiteContextFactorization.targetOuterEmbedding
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope) :
    WireRenaming context.siteOuter targetScope.frame.visible.sigs :=
  fun {_} value =>
    context.target_visible_exact.symm ▸
      Var.appendRight
        (localSignatures target.val targetSite) value

/-- Reading the source outer suffix ignores the transported local prefix. -/
theorem SiteContextFactorization.sourceEnvironment_outer
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env :
      Env pre
        (localSignatures source.val sourceSite ++ context.siteOuter))
    {signature : Sig}
    (value : Var context.siteOuter signature) :
    context.sourceEnvironment env signature
        (context.sourceOuterEmbedding value) =
      env signature
        (Var.appendRight
          (localSignatures source.val sourceSite) value) := by
  simpa [SiteContextFactorization.sourceEnvironment,
    SiteContextFactorization.sourceOuterEmbedding] using
      transportedEnvironment_apply context.source_visible_exact.symm env
        (Var.appendRight
          (localSignatures source.val sourceSite) value)

/-- Reading the target outer suffix ignores the transported local prefix. -/
theorem SiteContextFactorization.targetEnvironment_outer
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env :
      Env pre
        (localSignatures target.val targetSite ++ context.siteOuter))
    {signature : Sig}
    (value : Var context.siteOuter signature) :
    context.targetEnvironment env signature
        (context.targetOuterEmbedding value) =
      env signature
        (Var.appendRight
          (localSignatures target.val targetSite) value) := by
  simpa [SiteContextFactorization.targetEnvironment,
    SiteContextFactorization.targetOuterEmbedding] using
      transportedEnvironment_apply context.target_visible_exact.symm env
        (Var.appendRight
          (localSignatures target.val targetSite) value)

/-- Localizing a compiled source environment preserves every outer value. -/
theorem SiteContextFactorization.sourceLocalEnvironment_outer
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre sourceScope.frame.visible.sigs)
    {signature : Sig}
    (value : Var context.siteOuter signature) :
    context.sourceLocalEnvironment env signature
        (Var.appendRight
          (localSignatures source.val sourceSite) value) =
      env signature (context.sourceOuterEmbedding value) := by
  simpa [SiteContextFactorization.sourceLocalEnvironment,
    SiteContextFactorization.sourceOuterEmbedding,
    transport_symm_transport_var] using
      transportedEnvironment_apply context.source_visible_exact env
        (context.sourceOuterEmbedding value)

/-- Localizing a compiled target environment preserves every outer value. -/
theorem SiteContextFactorization.targetLocalEnvironment_outer
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (env : Env pre targetScope.frame.visible.sigs)
    {signature : Sig}
    (value : Var context.siteOuter signature) :
    context.targetLocalEnvironment env signature
        (Var.appendRight
          (localSignatures target.val targetSite) value) =
      env signature (context.targetOuterEmbedding value) := by
  simpa [SiteContextFactorization.targetLocalEnvironment,
    SiteContextFactorization.targetOuterEmbedding,
    transport_symm_transport_var] using
      transportedEnvironment_apply context.target_visible_exact env
        (context.targetOuterEmbedding value)

/-- Executable pointwise agreement of a visible alignment on the shared suffix. -/
structure AlignedSiteContext
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source target sourceScope.frame.visible
        targetScope.frame.visible) : Type where
  forwardOuter :
    SuffixAgreement context.siteOuter
      sourceScope.frame.visible.sigs targetScope.frame.visible.sigs
      context.sourceOuterEmbedding context.targetOuterEmbedding
      alignment.forward
  backwardOuter :
    SuffixAgreement context.siteOuter
      targetScope.frame.visible.sigs sourceScope.frame.visible.sigs
      context.targetOuterEmbedding context.sourceOuterEmbedding
      alignment.backward

def checkAlignedSiteContext
    {source : CheckedDiagram definitions}
    {target : CheckedDiagram definitions}
    {sourceSite : source.val.RegionId}
    {targetSite : target.val.RegionId}
    {sourceScope : SiteCompilation source sourceSite}
    {targetScope : SiteCompilation target targetSite}
    (context :
      SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source target sourceScope.frame.visible
        targetScope.frame.visible) :
    Option (AlignedSiteContext context alignment) := do
  let forward ←
    checkSuffixAgreement context.siteOuter
      context.sourceOuterEmbedding context.targetOuterEmbedding
      alignment.forward
  let backward ←
    checkSuffixAgreement context.siteOuter
      context.targetOuterEmbedding context.sourceOuterEmbedding
      alignment.backward
  pure ⟨forward, backward⟩

private def identityRenaming : WireRenaming context context :=
  fun {_} value => value

private def weakenRightOne :
    WireRenaming context (signature :: context) :=
  fun {_} value => .there value

private def weakenRightTwo :
    WireRenaming context (first :: second :: context) :=
  fun {_} value => .there (.there value)

private def weakenRightThree :
    WireRenaming context (first :: second :: third :: context) :=
  fun {_} value => .there (.there (.there value))

private theorem restoreSeparatedOne
    (distinguished : Var context distinguishedSignature)
    (env : Env pre context)
    (extra : pre.Domain extraSignature) :
    Env.comp
        ((env.extend extra).extend
          (env distinguishedSignature distinguished))
        (separateVar distinguished weakenRightOne) =
      env := by
  funext signature value
  by_cases sameSignature : signature = distinguishedSignature
  · subst signature
    by_cases sameVariable : value = distinguished
    · subst value
      simp [Env.comp, separateVar]
    · simp [Env.comp, separateVar, sameVariable, weakenRightOne]
  · simp [Env.comp, separateVar, sameSignature, weakenRightOne]

private theorem restoreSeparatedTwo
    (first second : Var context distinguishedSignature)
    (env : Env pre context)
    (extra : pre.Domain extraSignature) :
    Env.comp
        (((env.extend extra).extend
            (env distinguishedSignature second)).extend
          (env distinguishedSignature first))
        (separateVar first
          (separateVar second weakenRightOne)) =
      env := by
  funext signature value
  by_cases sameSignature : signature = distinguishedSignature
  · subst signature
    by_cases firstVariable : value = first
    · subst value
      simp [Env.comp, separateVar]
    · by_cases secondVariable : value = second
      · subst value
        simp [Env.comp, separateVar, firstVariable, weakenRightOne]
      · simp [Env.comp, separateVar, firstVariable, secondVariable,
          weakenRightOne]
  · simp [Env.comp, separateVar, sameSignature, weakenRightOne]

/--
Flatten the target-through-source cut construction into one symbolic
environment containing the target witness, source witness, and target frame.
-/
def cutTargetReconstruction
    (targetToCommon : WireRenaming target (signature :: source))
    (sourceToTarget : WireRenaming source (signature :: target)) :
    WireRenaming target (signature :: signature :: target) :=
  fun {_} value =>
    match targetToCommon value with
    | .here => .here
    | .there sourceValue => .there (sourceToTarget sourceValue)

/-- Environment reconstruction certificates for the cut factorization. -/
structure CutEnvironmentAlignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope}
    (arguments : List Sig)
    (sourceHead : Var sourceScope.frame.visible.sigs (.rel arguments))
    (targetHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (context : SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) : Type where
  sourceOuter :
    SuffixAgreement context.siteOuter sourceScope.frame.visible.sigs
      ((.rel arguments) :: targetScope.frame.visible.sigs)
      context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (separateVar sourceHead alignment.forward)
  targetOuter :
    SuffixAgreement context.siteOuter targetScope.frame.visible.sigs
      ((.rel arguments) :: sourceScope.frame.visible.sigs)
      context.targetOuterEmbedding
      (fun {_} value => .there (context.sourceOuterEmbedding value))
      (separateVar targetHead alignment.backward)
  targetReconstruction :
    SuffixAgreement targetScope.frame.visible.sigs
      targetScope.frame.visible.sigs
      ((.rel arguments) :: (.rel arguments) ::
        targetScope.frame.visible.sigs)
      identityRenaming
      (separateVar targetHead weakenRightOne)
      (cutTargetReconstruction
        (separateVar targetHead alignment.backward)
        (separateVar sourceHead alignment.forward))

def checkCutEnvironmentAlignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope}
    (arguments : List Sig)
    (sourceHead : Var sourceScope.frame.visible.sigs (.rel arguments))
    (targetHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (context : SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) :
    Option
      (CutEnvironmentAlignment arguments sourceHead targetHead context
        alignment) := do
  let sourceOuter ←
    checkSuffixAgreement context.siteOuter context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (separateVar sourceHead alignment.forward)
  let targetOuter ←
    checkSuffixAgreement context.siteOuter context.targetOuterEmbedding
      (fun {_} value => .there (context.sourceOuterEmbedding value))
      (separateVar targetHead alignment.backward)
  let targetReconstruction ←
    checkSuffixAgreement targetScope.frame.visible.sigs identityRenaming
      (separateVar targetHead weakenRightOne)
      (cutTargetReconstruction
        (separateVar targetHead alignment.backward)
        (separateVar sourceHead alignment.forward))
  pure ⟨sourceOuter, targetOuter, targetReconstruction⟩

/-- The checked cut maps reconstruct every original target-frame value. -/
theorem CutEnvironmentAlignment.reconstructTarget
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope}
    {arguments : List Sig}
    {sourceHead :
      Var sourceScope.frame.visible.sigs (.rel arguments)}
    {targetHead :
      Var targetScope.frame.visible.sigs (.rel arguments)}
    {context : SiteContextFactorization sourceScope targetScope}
    {alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible}
    (certificate :
      CutEnvironmentAlignment arguments sourceHead targetHead context
        alignment)
    (targetEnv : Env pre targetScope.frame.visible.sigs)
    (sourceWitness : pre.Domain (.rel arguments)) :
    Env.comp
        ((Env.comp (targetEnv.extend sourceWitness)
            (separateVar sourceHead alignment.forward)).extend
          (targetEnv _ targetHead))
        (separateVar targetHead alignment.backward) =
      targetEnv := by
  let stack :
      Env pre
        ((.rel arguments) :: (.rel arguments) ::
          targetScope.frame.visible.sigs) :=
    (targetEnv.extend sourceWitness).extend (targetEnv _ targetHead)
  have restored :
      Env.comp stack
          (separateVar targetHead weakenRightOne) =
        targetEnv :=
    restoreSeparatedOne targetHead targetEnv sourceWitness
  funext signature value
  calc
    _ =
        stack signature
          (cutTargetReconstruction
            (separateVar targetHead alignment.backward)
            (separateVar sourceHead alignment.forward) value) := by
          cases mappedExact :
              separateVar targetHead alignment.backward value with
          | here =>
              simp [Env.comp, cutTargetReconstruction, mappedExact, stack]
          | there mapped =>
              simp [Env.comp, cutTargetReconstruction, mappedExact, stack]
    _ =
        stack signature
          (separateVar targetHead weakenRightOne value) := by
          have mapped :=
            certificate.targetReconstruction.agrees value
          simpa [identityRenaming] using
            congrArg (fun mapped => stack signature mapped) mapped
    _ = targetEnv signature value := by
          exact congrFun (congrFun restored signature) value

/-- Checker-owned simultaneous factorization for a complete cut-wrap body. -/
structure CutFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (sourceScope :
      SiteCompilation source (source.val.wires wire).scope)
    (targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope) where
  arguments : List Sig
  sourceHead :
    Var sourceScope.frame.visible.sigs (.rel arguments)
  targetHead :
    Var targetScope.frame.visible.sigs (.rel arguments)
  alignment :
    VisibleWireAlignment source result.checked sourceScope.frame.visible
      targetScope.frame.visible
  context :
    SiteContextFactorization sourceScope targetScope
  outerAlignment :
    AlignedSiteContext context alignment
  environmentAlignment :
    CutEnvironmentAlignment arguments sourceHead targetHead context alignment
  private accepted :
    UniformIntrinsicRegion.checkCutShape
      (.there sourceHead)
      (.here :
        Var ((.rel arguments) :: sourceScope.frame.visible.sigs)
          (.rel arguments))
      (sourceScope.frame.siteBody.renameWires weakenOne)
      (targetScope.frame.siteBody.renameWires
        (separateVar targetHead alignment.backward)) =
      true

/-- Derive and check the complete intrinsic cut-wrap factorization. -/
def checkCutFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (sourceScope :
      SiteCompilation source (source.val.wires wire).scope)
    (targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) :
    Option (CutFactorization result sourceScope targetScope) := by
  refine
    (checkSiteContextFactorization sourceScope targetScope).bind
      (fun context => ?_)
  refine
    (checkAlignedSiteContext context alignment).bind
      (fun outerAlignment => ?_)
  match signature : (source.val.wires wire).sig with
  | .iota => exact none
  | .rel arguments =>
      let sourceMember :=
        sourceScope.visible_of_encloses wire
          (ConcreteDiagram.encloses_refl source.val
            (source.val.wires wire).scope)
      let targetMember :=
        targetScope.visible_of_encloses result.targetWire
          (ConcreteDiagram.encloses_refl result.checked.val
            (result.checked.val.wires result.targetWire).scope)
      let sourceHead :
          Var sourceScope.frame.visible.sigs (.rel arguments) :=
        InsertionCompilation.NaturalityInternal.castVar signature
          (InsertionCompilation.NaturalityInternal.varForMember source.val
            sourceScope.frame.visible.ids wire sourceMember)
      let targetSignature :
          (result.checked.val.wires result.targetWire).sig =
            .rel arguments :=
        result.targetWire_signature.trans signature
      let targetHead :
          Var targetScope.frame.visible.sigs (.rel arguments) :=
        InsertionCompilation.NaturalityInternal.castVar targetSignature
          (InsertionCompilation.NaturalityInternal.varForMember
            result.checked.val targetScope.frame.visible.ids
            result.targetWire targetMember)
      refine
        (checkCutEnvironmentAlignment arguments sourceHead targetHead context
          alignment).bind (fun environmentAlignment => ?_)
      if accepted :
          UniformIntrinsicRegion.checkCutShape
            (.there sourceHead)
            (.here :
              Var ((.rel arguments) :: sourceScope.frame.visible.sigs)
                (.rel arguments))
            (sourceScope.frame.siteBody.renameWires weakenOne)
            (targetScope.frame.siteBody.renameWires
              (separateVar targetHead alignment.backward)) then
        exact
          some
            ⟨arguments, sourceHead, targetHead, alignment, context,
              outerAlignment, environmentAlignment, accepted⟩
      else
        exact none

namespace CutFactorization

/-- The checked cut factorization is sound in every common environment. -/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope}
    (factorization :
      CutFactorization result sourceScope targetScope)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        ((.rel factorization.arguments) ::
          sourceScope.frame.visible.sigs))
    (pointwise :
      ∀ values,
        pre.apply (env _ (.there factorization.sourceHead)) values ↔
          ¬pre.apply
            (env _ (.here :
              Var
                ((.rel factorization.arguments) ::
                  sourceScope.frame.visible.sigs)
                (.rel factorization.arguments)))
            values) :
    denoteRegion pre definitionEnv
        (Env.comp env weakenOne) sourceScope.frame.siteBody ↔
      denoteRegion pre definitionEnv
        (Env.comp env
          (separateVar factorization.targetHead
            factorization.alignment.backward))
        targetScope.frame.siteBody := by
  have shape :=
    UniformIntrinsicRegion.checkCutShape_denotes pre definitionEnv env
      (.there factorization.sourceHead)
      (.here :
        Var
          ((.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs)
          (.rel factorization.arguments))
      (sourceScope.frame.siteBody.renameWires weakenOne)
      (targetScope.frame.siteBody.renameWires
        (separateVar factorization.targetHead
          factorization.alignment.backward))
      factorization.accepted pointwise
  exact
    (denoteRegion_renameWires pre definitionEnv env weakenOne
      sourceScope.frame.siteBody).symm.trans
      (shape.trans
        (denoteRegion_renameWires pre definitionEnv env
          (separateVar factorization.targetHead
            factorization.alignment.backward)
          targetScope.frame.siteBody))

end CutFactorization

/--
Flatten target-through-source parallel reconstruction into the two target
witnesses, one source witness, and the original target frame.
-/
def parallelTargetReconstruction
    (targetToCommon :
      WireRenaming target (signature :: signature :: source))
    (sourceToTarget : WireRenaming source (signature :: target)) :
    WireRenaming target
      (signature :: signature :: signature :: target) :=
  fun {_} value =>
    match targetToCommon value with
    | .here => .here
    | .there (.here) => .there .here
    | .there (.there sourceValue) =>
        .there (.there (sourceToTarget sourceValue))

/-- Environment reconstruction certificates for parallel factorization. -/
structure ParallelEnvironmentAlignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope}
    (arguments : List Sig)
    (sourceHead : Var sourceScope.frame.visible.sigs (.rel arguments))
    (firstHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (secondHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (context : SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) : Type where
  sourceOuter :
    SuffixAgreement context.siteOuter sourceScope.frame.visible.sigs
      ((.rel arguments) :: targetScope.frame.visible.sigs)
      context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (separateVar sourceHead alignment.forward)
  targetOuter :
    SuffixAgreement context.siteOuter targetScope.frame.visible.sigs
      ((.rel arguments) :: (.rel arguments) ::
        sourceScope.frame.visible.sigs)
      context.targetOuterEmbedding
      (fun {_} value =>
        .there (.there (context.sourceOuterEmbedding value)))
      (separateVar firstHead
        (separateVar secondHead alignment.backward))
  targetReconstruction :
    SuffixAgreement targetScope.frame.visible.sigs
      targetScope.frame.visible.sigs
      ((.rel arguments) :: (.rel arguments) :: (.rel arguments) ::
        targetScope.frame.visible.sigs)
      identityRenaming
      (separateVar firstHead
        (separateVar secondHead weakenRightOne))
      (parallelTargetReconstruction
        (separateVar firstHead
          (separateVar secondHead alignment.backward))
        (separateVar sourceHead alignment.forward))

def checkParallelEnvironmentAlignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope}
    (arguments : List Sig)
    (sourceHead : Var sourceScope.frame.visible.sigs (.rel arguments))
    (firstHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (secondHead : Var targetScope.frame.visible.sigs (.rel arguments))
    (context : SiteContextFactorization sourceScope targetScope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) :
    Option
      (ParallelEnvironmentAlignment arguments sourceHead firstHead
        secondHead context alignment) := do
  let sourceOuter ←
    checkSuffixAgreement context.siteOuter context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (separateVar sourceHead alignment.forward)
  let targetOuter ←
    checkSuffixAgreement context.siteOuter context.targetOuterEmbedding
      (fun {_} value =>
        .there (.there (context.sourceOuterEmbedding value)))
      (separateVar firstHead
        (separateVar secondHead alignment.backward))
  let targetReconstruction ←
    checkSuffixAgreement targetScope.frame.visible.sigs identityRenaming
      (separateVar firstHead
        (separateVar secondHead weakenRightOne))
      (parallelTargetReconstruction
        (separateVar firstHead
          (separateVar secondHead alignment.backward))
        (separateVar sourceHead alignment.forward))
  pure ⟨sourceOuter, targetOuter, targetReconstruction⟩

/-- The checked split maps reconstruct every original target-frame value. -/
theorem ParallelEnvironmentAlignment.reconstructTarget
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope}
    {arguments : List Sig}
    {sourceHead :
      Var sourceScope.frame.visible.sigs (.rel arguments)}
    {firstHead secondHead :
      Var targetScope.frame.visible.sigs (.rel arguments)}
    {context : SiteContextFactorization sourceScope targetScope}
    {alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible}
    (certificate :
      ParallelEnvironmentAlignment arguments sourceHead firstHead
        secondHead context alignment)
    (targetEnv : Env pre targetScope.frame.visible.sigs)
    (sourceWitness : pre.Domain (.rel arguments)) :
    Env.comp
        ((Env.comp (targetEnv.extend sourceWitness)
            (separateVar sourceHead alignment.forward)).extend
          (targetEnv _ secondHead) |>.extend
            (targetEnv _ firstHead))
        (separateVar firstHead
          (separateVar secondHead alignment.backward)) =
      targetEnv := by
  let stack :
      Env pre
        ((.rel arguments) :: (.rel arguments) :: (.rel arguments) ::
          targetScope.frame.visible.sigs) :=
    ((targetEnv.extend sourceWitness).extend
      (targetEnv _ secondHead)).extend (targetEnv _ firstHead)
  have restored :
      Env.comp stack
          (separateVar firstHead
            (separateVar secondHead weakenRightOne)) =
        targetEnv :=
    restoreSeparatedTwo firstHead secondHead targetEnv sourceWitness
  funext signature value
  calc
    _ =
        stack signature
          (parallelTargetReconstruction
            (separateVar firstHead
              (separateVar secondHead alignment.backward))
            (separateVar sourceHead alignment.forward) value) := by
          cases mappedExact :
              separateVar firstHead
                  (separateVar secondHead alignment.backward) value with
          | here =>
              simp [Env.comp, parallelTargetReconstruction, mappedExact,
                stack]
          | there mapped =>
              cases mapped with
              | here =>
                  simp [Env.comp, parallelTargetReconstruction, mappedExact,
                    stack]
              | there mapped =>
                  simp [Env.comp, parallelTargetReconstruction, mappedExact,
                    stack]
    _ =
        stack signature
          (separateVar firstHead
            (separateVar secondHead weakenRightOne) value) := by
          have mapped :=
            certificate.targetReconstruction.agrees value
          simpa [identityRenaming] using
            congrArg (fun mapped => stack signature mapped) mapped
    _ = targetEnv signature value := by
          exact congrFun (congrFun restored signature) value

/-- Checker-owned simultaneous factorization for a complete parallel body. -/
structure ParallelFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (sourceScope :
      SiteCompilation source (source.val.wires wire).scope)
    (targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope) where
  arguments : List Sig
  sourceHead :
    Var sourceScope.frame.visible.sigs (.rel arguments)
  firstHead :
    Var targetScope.frame.visible.sigs (.rel arguments)
  secondHead :
    Var targetScope.frame.visible.sigs (.rel arguments)
  alignment :
    VisibleWireAlignment source result.checked sourceScope.frame.visible
      targetScope.frame.visible
  context :
    SiteContextFactorization sourceScope targetScope
  outerAlignment :
    AlignedSiteContext context alignment
  environmentAlignment :
    ParallelEnvironmentAlignment arguments sourceHead firstHead secondHead
      context alignment
  private accepted :
    UniformIntrinsicRegion.checkParallelShape
      (.there (.there sourceHead))
      (.here :
        Var
          ((.rel arguments) :: (.rel arguments) ::
            sourceScope.frame.visible.sigs)
          (.rel arguments))
      (.there (.here :
        Var ((.rel arguments) :: sourceScope.frame.visible.sigs)
          (.rel arguments)))
      (sourceScope.frame.siteBody.renameWires weakenTwo)
      (targetScope.frame.siteBody.renameWires
        (separateVar firstHead
          (separateVar secondHead alignment.backward))) =
      true

/-- Derive and check the complete intrinsic parallel factorization. -/
def checkParallelFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (sourceScope :
      SiteCompilation source (source.val.wires wire).scope)
    (targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope)
    (alignment :
      VisibleWireAlignment source result.checked sourceScope.frame.visible
        targetScope.frame.visible) :
    Option (ParallelFactorization result sourceScope targetScope) := by
  refine
    (checkSiteContextFactorization sourceScope targetScope).bind
      (fun context => ?_)
  refine
    (checkAlignedSiteContext context alignment).bind
      (fun outerAlignment => ?_)
  match signature : (source.val.wires wire).sig with
  | .iota => exact none
  | .rel arguments =>
      let sourceMember :=
        sourceScope.visible_of_encloses wire
          (ConcreteDiagram.encloses_refl source.val
            (source.val.wires wire).scope)
      let firstMember :=
        targetScope.visible_of_encloses result.firstWire
          (ConcreteDiagram.encloses_refl result.checked.val
            (result.checked.val.wires result.firstWire).scope)
      let secondMember :=
        targetScope.visible_of_encloses result.secondWire (by
          rw [result.wireScopes_eq]
          exact
            ConcreteDiagram.encloses_refl result.checked.val
              (result.checked.val.wires result.secondWire).scope)
      let sourceHead :
          Var sourceScope.frame.visible.sigs (.rel arguments) :=
        InsertionCompilation.NaturalityInternal.castVar signature
          (InsertionCompilation.NaturalityInternal.varForMember source.val
            sourceScope.frame.visible.ids wire sourceMember)
      let firstSignature :
          (result.checked.val.wires result.firstWire).sig =
            .rel arguments :=
        result.firstWire_signature.trans signature
      let secondSignature :
          (result.checked.val.wires result.secondWire).sig =
            .rel arguments :=
        result.secondWire_signature.trans signature
      let firstHead :
          Var targetScope.frame.visible.sigs (.rel arguments) :=
        InsertionCompilation.NaturalityInternal.castVar firstSignature
          (InsertionCompilation.NaturalityInternal.varForMember
            result.checked.val targetScope.frame.visible.ids
            result.firstWire firstMember)
      let secondHead :
          Var targetScope.frame.visible.sigs (.rel arguments) :=
        InsertionCompilation.NaturalityInternal.castVar secondSignature
          (InsertionCompilation.NaturalityInternal.varForMember
            result.checked.val targetScope.frame.visible.ids
            result.secondWire secondMember)
      refine
        (checkParallelEnvironmentAlignment arguments sourceHead firstHead
          secondHead context alignment).bind
          (fun environmentAlignment => ?_)
      if accepted :
          UniformIntrinsicRegion.checkParallelShape
            (.there (.there sourceHead))
            (.here :
              Var
                ((.rel arguments) :: (.rel arguments) ::
                  sourceScope.frame.visible.sigs)
                (.rel arguments))
            (.there (.here :
              Var ((.rel arguments) :: sourceScope.frame.visible.sigs)
                (.rel arguments)))
            (sourceScope.frame.siteBody.renameWires weakenTwo)
            (targetScope.frame.siteBody.renameWires
              (separateVar firstHead
                (separateVar secondHead alignment.backward))) then
        exact
          some
            ⟨arguments, sourceHead, firstHead, secondHead, alignment,
              context, outerAlignment, environmentAlignment, accepted⟩
      else
        exact none

namespace ParallelFactorization

/-- The checked parallel factorization is sound in every common environment. -/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope}
    (factorization :
      ParallelFactorization result sourceScope targetScope)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        ((.rel factorization.arguments) ::
          (.rel factorization.arguments) ::
          sourceScope.frame.visible.sigs))
    (pointwise :
      ∀ values,
        pre.apply
            (env _ (.there (.there factorization.sourceHead))) values ↔
          (pre.apply
              (env _ (.here :
                Var
                  ((.rel factorization.arguments) ::
                    (.rel factorization.arguments) ::
                    sourceScope.frame.visible.sigs)
                  (.rel factorization.arguments)))
              values ∧
            pre.apply
              (env _ (.there (.here :
                Var
                  ((.rel factorization.arguments) ::
                    sourceScope.frame.visible.sigs)
                  (.rel factorization.arguments))))
              values)) :
    denoteRegion pre definitionEnv
        (Env.comp env weakenTwo) sourceScope.frame.siteBody ↔
      denoteRegion pre definitionEnv
        (Env.comp env
          (separateVar factorization.firstHead
            (separateVar factorization.secondHead
              factorization.alignment.backward)))
        targetScope.frame.siteBody := by
  have shape :=
    UniformIntrinsicRegion.checkParallelShape_denotes pre definitionEnv env
      (.there (.there factorization.sourceHead))
      (.here :
        Var
          ((.rel factorization.arguments) ::
            (.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs)
          (.rel factorization.arguments))
      (.there (.here :
        Var
          ((.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs)
          (.rel factorization.arguments)))
      (sourceScope.frame.siteBody.renameWires weakenTwo)
      (targetScope.frame.siteBody.renameWires
        (separateVar factorization.firstHead
          (separateVar factorization.secondHead
            factorization.alignment.backward)))
      factorization.accepted pointwise
  exact
    (denoteRegion_renameWires pre definitionEnv env weakenTwo
      sourceScope.frame.siteBody).symm.trans
      (shape.trans
        (denoteRegion_renameWires pre definitionEnv env
          (separateVar factorization.firstHead
            (separateVar factorization.secondHead
              factorization.alignment.backward))
          targetScope.frame.siteBody))

end ParallelFactorization

end ContentAlignment

end ConcreteWirePrimitive

end VisualProof
