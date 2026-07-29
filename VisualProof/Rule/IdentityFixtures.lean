import VisualProof.Diagram.Concrete.Examples
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics
import VisualProof.Rule.IdentityRetargetSemantics

namespace VisualProof
namespace IdentityFixtures

open ConcreteExamples
open ConcreteDiagram

/-! Orderless identity incidence is exercised at arity three and above. -/

example :
    (normalizeIdentities threePortIdentity_checked).target.val.wireCount = 1 := by
  native_decide

example :
    (fuseSameRegion identityOrderOriginal_checked
      ⟨0, by decide⟩ ⟨1, by decide⟩).isSome = true := by
  native_decide

example :
    (fuseSameRegion identityOrderPermuted_checked
      ⟨0, by decide⟩ ⟨1, by decide⟩).isSome = true := by
  native_decide

example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv identityOrderOriginal_checked =
      denoteChecked pre definitionEnv identityOrderPermuted_checked :=
  identityIncidencePermutation_denotation pre definitionEnv

/-!
The retarget host has one three-port same-signature identity. Its region
strictly dominates the nested insertion site but not the sibling site.
-/

def retargetHostRaw : ConcreteDiagram 0 where
  regionCount := 4
  nodeCount := 1
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
    | ⟨2, _⟩ => .cut 1
    | ⟨3, _⟩ => .cut 0
  nodes := fun _ => .identity 1 .iota 3
  wires
    | ⟨0, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 2⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints := [⟨0, .identity 1⟩] }

theorem retargetHostRaw_wellFormed : retargetHostRaw.WellFormed [] := by
  native_decide

def retargetHost : CheckedDiagram [] :=
  ⟨retargetHostRaw, retargetHostRaw_wellFormed⟩

def nestedSite : retargetHost.val.RegionId := ⟨2, by decide⟩
def siblingSite : retargetHost.val.RegionId := ⟨3, by decide⟩
def identityNode : retargetHost.val.NodeId := ⟨0, by decide⟩
def sourceWire : retargetHost.val.WireId := ⟨0, by decide⟩
def targetWire : retargetHost.val.WireId := ⟨1, by decide⟩
def thirdWire : retargetHost.val.WireId := ⟨2, by decide⟩

def sourceTarget :
    Fin repeatedBoundaryAlias_checked.val.boundary.length →
      retargetHost.val.WireId :=
  fun _ => sourceWire

def sourceAttachment? :
    Option
      (ConcreteSpliceAttachment retargetHost nestedSite
        repeatedBoundaryAlias_checked) :=
  checkConcreteSpliceAttachment retargetHost nestedSite
    repeatedBoundaryAlias_checked sourceTarget

example : sourceAttachment?.isSome = true := by
  native_decide

def sourceAttachment :
    ConcreteSpliceAttachment retargetHost nestedSite
      repeatedBoundaryAlias_checked :=
  sourceAttachment?.get (by native_decide)

def retargetInput (boundary : Nat) : IdentityRetargetInput retargetHost where
  boundary := boundary
  identity := identityNode
  sourceWire := sourceWire
  targetWire := targetWire

example :
    (checkIdentityRetarget retargetHost nestedSite .iteration
      (orderedAttachmentTuple sourceAttachment)
      (retargetInput 0)).isSome = true := by
  native_decide

example :
    (checkIdentityRetarget retargetHost siblingSite .iteration
      [sourceWire] (retargetInput 0)).isSome = false := by
  native_decide

def forwardBatch :
    CheckedIdentityRetargets retargetHost nestedSite .iteration
      (orderedAttachmentTuple sourceAttachment) :=
  (checkIdentityRetargets retargetHost nestedSite .iteration
    (orderedAttachmentTuple sourceAttachment)
    [retargetInput 0, retargetInput 1]).get (by native_decide)

def reverseBatch :
    CheckedIdentityRetargets retargetHost nestedSite .iteration
      (orderedAttachmentTuple sourceAttachment) :=
  (checkIdentityRetargets retargetHost nestedSite .iteration
    (orderedAttachmentTuple sourceAttachment)
    [retargetInput 1, retargetInput 0]).get (by native_decide)

/-- Batch input order cannot alter the ordered attachment result. -/
example :
    forwardBatch.retargetAttachments =
      reverseBatch.retargetAttachments := by
  native_decide

example :
    forwardBatch.retargetAttachments = [targetWire, targetWire] := by
  native_decide

def checkedRetarget? :
    Option
      (CheckedIdentityRetargetedSplice retargetHost nestedSite
        repeatedBoundaryAlias_checked .iteration) :=
  checkIdentityRetargetedSplice retargetHost nestedSite
    repeatedBoundaryAlias_checked .iteration sourceAttachment
    [retargetInput 1, retargetInput 0]

example : checkedRetarget?.isSome = true := by
  native_decide

def checkedRetarget :
    CheckedIdentityRetargetedSplice retargetHost nestedSite
      repeatedBoundaryAlias_checked .iteration :=
  checkedRetarget?.get (by native_decide)

/-- Repeated ordered aliases are retargeted positionally and remain aliases. -/
example :
    checkedRetarget.target.target ⟨0, by decide⟩ =
        checkedRetarget.target.target ⟨1, by decide⟩ ∧
      checkedRetarget.target.target ⟨0, by decide⟩ = targetWire := by
  native_decide

def siblingSourceTarget :
    Fin repeatedBoundaryAlias_checked.val.boundary.length →
      retargetHost.val.WireId :=
  fun _ => sourceWire

def siblingSourceAttachment :
    ConcreteSpliceAttachment retargetHost siblingSite
      repeatedBoundaryAlias_checked :=
  (checkConcreteSpliceAttachment retargetHost siblingSite
    repeatedBoundaryAlias_checked siblingSourceTarget).get
      (by native_decide)

/-- The full checker refuses the same identity at the sibling site. -/
example :
    (checkIdentityRetargetedSplice retargetHost siblingSite
      repeatedBoundaryAlias_checked .iteration siblingSourceAttachment
      [retargetInput 0]).isSome = false := by
  native_decide

def fragmentCompiled : OpenCompilation repeatedBoundaryAlias_checked :=
  (compileOpen repeatedBoundaryAlias_checked).get (by native_decide)

theorem sourceSucceeds :
    ∃ result, splice checkedRetarget.source = .ok result := by
  cases accepted : splice checkedRetarget.source with
  | error error =>
      have possible :
          (match splice checkedRetarget.source with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [accepted] at possible
  | ok result => exact ⟨result, rfl⟩

noncomputable def sourceResult :
    ConcreteSpliceResult checkedRetarget.source :=
  Classical.choose sourceSucceeds

theorem sourceAccepted :
    splice checkedRetarget.source = .ok sourceResult := by
  exact Classical.choose_spec sourceSucceeds

theorem targetSucceeds :
    ∃ result, splice checkedRetarget.target = .ok result := by
  cases accepted : splice checkedRetarget.target with
  | error error =>
      have possible :
          (match splice checkedRetarget.target with
            | .ok _ => true
            | .error _ => false) = true := by
        native_decide
      simp [accepted] at possible
  | ok result => exact ⟨result, rfl⟩

noncomputable def targetResult :
    ConcreteSpliceResult checkedRetarget.target :=
  Classical.choose targetSucceeds

theorem targetAccepted :
    splice checkedRetarget.target = .ok targetResult := by
  exact Classical.choose_spec targetSucceeds

example (pre : PreModel) (definitionEnv : DefinitionEnv pre []) :
    denoteChecked pre definitionEnv targetResult.checked ↔
      denoteChecked pre definitionEnv sourceResult.checked :=
  identity_retarget_sound fragmentCompiled checkedRetarget
    sourceResult sourceAccepted targetResult targetAccepted pre definitionEnv

end IdentityFixtures
end VisualProof
