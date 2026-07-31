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
      if accepted :
          UniformIntrinsicRegion.checkCutShape
            (.there sourceHead)
            (.here :
              Var ((.rel arguments) :: sourceScope.frame.visible.sigs)
                (.rel arguments))
            (sourceScope.frame.siteBody.renameWires weakenOne)
            (targetScope.frame.siteBody.renameWires
              (separateVar targetHead alignment.backward)) then
        exact some ⟨arguments, sourceHead, targetHead, alignment, accepted⟩
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
              accepted⟩
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
