import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsSemantics

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

open WirePrimitive

private def weakenArgumentHead :
    WireRenaming context (signature :: context) :=
  fun {_} value => .there value

namespace ContentAlignment.PairedContext

/-- Reverse a paired outer spine without changing any retained constructor. -/
def symm
    {sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer}
    {targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer} :
    ContentAlignment.PairedContext definitions sourceLocal targetLocal
        siteOuter sourceContext targetContext →
      ContentAlignment.PairedContext definitions targetLocal sourceLocal
        siteOuter targetContext sourceContext
  | .terminal => .terminal
  | .surround leading suffix inner =>
      .surround leading suffix (symm inner)
  | .cut inner => .cut (symm inner)
  | .bind signature inner => .bind signature (symm inner)

private theorem bindMany_cutDepth
    (bound : List Sig)
    (inner :
      DiagramContext definitions hole (bound ++ outer)) :
    (DiagramContext.bindMany bound inner).cutDepth = inner.cutDepth := by
  induction bound generalizing outer with
  | nil => rfl
  | cons signature rest induction =>
      simpa [DiagramContext.bindMany, DiagramContext.cutDepth] using
        induction (.bind signature inner)

/-- Paired contexts have the same number of surrounding cuts. -/
theorem cutDepth_eq
    {sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer}
    {targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer}
    (paired :
      ContentAlignment.PairedContext definitions sourceLocal targetLocal
        siteOuter sourceContext targetContext) :
    sourceContext.cutDepth = targetContext.cutDepth := by
  induction paired with
  | terminal =>
      exact
        (bindMany_cutDepth sourceLocal
          (.hole :
            DiagramContext definitions
              (sourceLocal ++ siteOuter)
              (sourceLocal ++ siteOuter))).trans
          (bindMany_cutDepth targetLocal
            (.hole :
              DiagramContext definitions
                (targetLocal ++ siteOuter)
                (targetLocal ++ siteOuter))).symm
  | surround leading suffix inner induction =>
      simpa [DiagramContext.cutDepth] using induction
  | cut inner induction =>
      simpa [DiagramContext.cutDepth] using congrArg Nat.succ induction
  | bind signature inner induction =>
      simpa [DiagramContext.cutDepth] using induction

/--
A terminal source-to-target implication follows the common outer spine.
Even cut depth preserves its direction; odd cut depth reverses it.
-/
theorem sourceToTarget
    {sourceContext :
      DiagramContext definitions (sourceLocal ++ siteOuter) outer}
    {targetContext :
      DiagramContext definitions (targetLocal ++ siteOuter) outer}
    (paired :
      ContentAlignment.PairedContext definitions sourceLocal targetLocal
        siteOuter sourceContext targetContext)
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
                  (sourceLocal ++ siteOuter))).fill sourceBody) →
          denoteRegion pre definitionEnv siteEnv
            ((DiagramContext.bindMany targetLocal
              (.hole :
                DiagramContext definitions
                  (targetLocal ++ siteOuter)
                  (targetLocal ++ siteOuter))).fill targetBody)) :
    (sourceContext.cutDepth % 2 = 0 →
      denoteRegion pre definitionEnv env
          (sourceContext.fill sourceBody) →
        denoteRegion pre definitionEnv env
          (targetContext.fill targetBody)) ∧
    (sourceContext.cutDepth % 2 = 1 →
      denoteRegion pre definitionEnv env
          (targetContext.fill targetBody) →
        denoteRegion pre definitionEnv env
          (sourceContext.fill sourceBody)) := by
  induction paired with
  | terminal =>
      constructor
      · intro _ sourceHolds
        exact localLaw env sourceHolds
      · intro odd
        rw [bindMany_cutDepth] at odd
        simp only [DiagramContext.cutDepth] at odd
        omega
  | surround leading suffix inner induction =>
      constructor
      · intro even sourceHolds
        simp only [DiagramContext.cutDepth, DiagramContext.fill,
          Region.denote_surround] at sourceHolds ⊢
        exact
          ⟨sourceHolds.1,
            (induction env).1 even sourceHolds.2.1,
            sourceHolds.2.2⟩
      · intro odd targetHolds
        simp only [DiagramContext.cutDepth, DiagramContext.fill,
          Region.denote_surround] at targetHolds ⊢
        exact
          ⟨targetHolds.1,
            (induction env).2 odd targetHolds.2.1,
            targetHolds.2.2⟩
  | cut inner induction =>
      constructor
      · intro even sourceHolds
        simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
          denoteItem, and_true] at sourceHolds ⊢
        intro targetHolds
        exact sourceHolds ((induction env).2 (by
          simp only [DiagramContext.cutDepth] at even
          omega) targetHolds)
      · intro odd targetHolds
        simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
          denoteItem, and_true] at targetHolds ⊢
        intro sourceHolds
        exact targetHolds ((induction env).1 (by
          simp only [DiagramContext.cutDepth] at odd
          omega) sourceHolds)
  | bind signature inner induction =>
      constructor
      · intro even sourceHolds
        simp only [DiagramContext.cutDepth, DiagramContext.fill,
          denoteRegion, denoteItemSeq, denoteItem, and_true] at sourceHolds ⊢
        rcases sourceHolds with ⟨value, holds⟩
        exact ⟨value, (induction (env.extend value)).1 even holds⟩
      · intro odd targetHolds
        simp only [DiagramContext.cutDepth, DiagramContext.fill,
          denoteRegion, denoteItemSeq, denoteItem, and_true] at targetHolds ⊢
        rcases targetHolds with ⟨value, holds⟩
        exact ⟨value, (induction (env.extend value)).2 odd holds⟩

end ContentAlignment.PairedContext

private theorem castContext_fill
    {left right outer : List Sig}
    (same : left = right)
    (context : DiagramContext definitions left outer)
    (body : Region definitions left) :
    (same ▸ context).fill (same ▸ body) = context.fill body := by
  cases same
  rfl

private theorem castContext_cutDepth
    {left right outer : List Sig}
    (same : left = right)
    (context : DiagramContext definitions left outer) :
    (same ▸ context).cutDepth = context.cutDepth := by
  cases same
  rfl

namespace TypedArguments

/-- Duplicate the selected signature directly after itself. -/
def duplicatedArguments : List Sig → Nat → List Sig
  | [], _ => []
  | head :: tail, 0 => head :: head :: tail
  | head :: tail, position + 1 =>
      head :: duplicatedArguments tail position

/-- Duplicate the selected intrinsic variable directly after itself. -/
def duplicateVars :
    {arguments : List Sig} →
      (position : Nat) →
      Vars context arguments →
      Vars context (duplicatedArguments arguments position)
  | [], _, .nil => .nil
  | _ :: _, 0, .cons head tail =>
      .cons head (.cons head tail)
  | _ :: _, position + 1, .cons head tail =>
      .cons head (duplicateVars position tail)

/-- Duplicate the selected semantic value directly after itself. -/
def duplicateValues :
    {arguments : List Sig} →
      (position : Nat) →
      PreModel.Args Domain arguments →
      PreModel.Args Domain (duplicatedArguments arguments position)
  | [], _, PUnit.unit => PUnit.unit
  | _ :: _, 0, ⟨head, tail⟩ =>
      ⟨head, head, tail⟩
  | _ :: _, position + 1, ⟨head, tail⟩ =>
      ⟨head, duplicateValues position tail⟩

/-- Remove the second member of the selected duplicated pair. -/
def contractValues :
    {arguments : List Sig} →
      (position : Nat) →
      PreModel.Args Domain (duplicatedArguments arguments position) →
      PreModel.Args Domain arguments
  | [], _, PUnit.unit => PUnit.unit
  | _ :: _, 0, ⟨head, _, tail⟩ =>
      ⟨head, tail⟩
  | _ :: _, position + 1, ⟨head, tail⟩ =>
      ⟨head, contractValues position tail⟩

@[simp] theorem denote_duplicateVars
    (position : Nat)
    (env : Env pre context)
    (values : Vars context arguments) :
    Vars.denote env (duplicateVars position values) =
      duplicateValues position (Vars.denote env values) := by
  induction arguments generalizing position with
  | nil =>
      cases values
      cases position <;> rfl
  | cons signature rest induction =>
      cases values with
      | cons head tail =>
          cases position with
          | zero => rfl
          | succ position =>
              simp only [duplicateVars, Vars.denote_cons, duplicateValues]
              exact congrArg (fun suffix => (env _ head, suffix))
                (induction position tail)

@[simp] theorem contractValues_duplicateValues
    (position : Nat)
    (values : PreModel.Args Domain arguments) :
    contractValues position (duplicateValues position values) = values := by
  induction arguments generalizing position with
  | nil =>
      cases values
      cases position <;> rfl
  | cons signature rest induction =>
      rcases values with ⟨head, tail⟩
      cases position with
      | zero => rfl
      | succ position =>
          simp only [duplicateValues, contractValues]
          exact congrArg (fun suffix => (head, suffix))
            (induction position tail)

/--
Model-independent evidence that one signature vector is exactly a duplicate
of another. Its methods remain universe-polymorphic because the evidence
stores only the position and type equality.
-/
structure DuplicationEvidence (source target : List Sig) where
  position : Nat
  targetExact : duplicatedArguments source position = target

namespace DuplicationEvidence

def forwardVars
    (evidence : DuplicationEvidence source target)
    (values : Vars context source) :
    Vars context target :=
  evidence.targetExact ▸ duplicateVars evidence.position values

def forwardValues
    (evidence : DuplicationEvidence source target)
    (values : PreModel.Args Domain source) :
    PreModel.Args Domain target :=
  evidence.targetExact ▸ duplicateValues evidence.position values

def backwardValues
    (evidence : DuplicationEvidence source target)
    (values : PreModel.Args Domain target) :
    PreModel.Args Domain source :=
  contractValues evidence.position (evidence.targetExact.symm ▸ values)

theorem denote_forward
    (evidence : DuplicationEvidence source target)
    (env : Env pre context)
    (values : Vars context source) :
    Vars.denote env (evidence.forwardVars values) =
      evidence.forwardValues (Vars.denote env values) := by
  cases evidence with
  | mk position targetExact =>
      subst target
      simp only [forwardVars, forwardValues]
      exact denote_duplicateVars position env values

theorem backward_forward
    (evidence : DuplicationEvidence source target)
    (values : PreModel.Args Domain source) :
    evidence.backwardValues (evidence.forwardValues values) = values := by
  cases evidence with
  | mk position targetExact =>
      subst target
      simp only [forwardValues, backwardValues]
      exact contractValues_duplicateValues position values

end DuplicationEvidence

end TypedArguments

/-- Source-to-target relation for an embedding such as duplication. -/
def embeddingRelation
    (retraction :
      TypedArguments.DuplicationEvidence sourceArguments targetArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context targetArguments) : Bool :=
  TypedArguments.sameVars (retraction.forwardVars source) target

/-- Source-to-target relation for the inverse of an embedding. -/
def projectionRelation
    (retraction :
      TypedArguments.DuplicationEvidence targetArguments sourceArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context targetArguments) : Bool :=
  TypedArguments.sameVars source (retraction.forwardVars target)

/-- Complete semantic ledger for checked argument duplication. -/
structure DuplicateLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  retraction :
    TypedArguments.DuplicationEvidence sourceArguments
      result.targetArguments
  factorization :
    ArgumentFactorization result sourceArguments
      (embeddingRelation retraction)

/-- Complete semantic ledger for checked adjacent contraction. -/
structure ContractLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  retraction :
    TypedArguments.DuplicationEvidence result.targetArguments
      sourceArguments
  factorization :
    ArgumentFactorization result sourceArguments
      (projectionRelation retraction)

/-- Derive and validate the complete duplicate ledger. -/
def checkDuplicateLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat) :
    Option (DuplicateLedger result sourceArguments) := do
  if targetExact :
      TypedArguments.duplicatedArguments sourceArguments position =
        result.targetArguments then
    let retraction :
        TypedArguments.DuplicationEvidence sourceArguments
          result.targetArguments :=
      ⟨position, targetExact⟩
    let factorization ←
      checkArgumentFactorization result sourceArguments sourceSignature
        (embeddingRelation retraction)
    pure ⟨retraction, factorization⟩
  else
    none

/-- Derive and validate the complete contraction ledger. -/
def checkContractLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat) :
    Option (ContractLedger result sourceArguments) := do
  if sourceExact :
      TypedArguments.duplicatedArguments result.targetArguments position =
        sourceArguments then
    let retraction :
        TypedArguments.DuplicationEvidence result.targetArguments
          sourceArguments :=
      ⟨position, sourceExact⟩
    let factorization ←
      checkArgumentFactorization result sourceArguments sourceSignature
        (projectionRelation retraction)
    pure ⟨retraction, factorization⟩
  else
    none

namespace DuplicateLedger

noncomputable def witness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : DuplicateLedger result sourceArguments)
    (model : Model.{u}) :
    ArgumentFactorization.EquivalenceWitness
      ledger.factorization model where
  forward := fun sourceRelation =>
    reifyRelation model fun targetValues =>
      model.toPreModel.apply sourceRelation
        (ledger.retraction.backwardValues targetValues)
  backward := fun targetRelation =>
    reifyRelation model fun sourceValues =>
      model.toPreModel.apply targetRelation
        (ledger.retraction.forwardValues sourceValues)
  forward_pointwise := by
    intro sourceRelation nested nestedEnv left right accepted
    have exact :
        ledger.retraction.forwardVars left = right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [← exact, ledger.retraction.denote_forward,
      ledger.retraction.backward_forward]
  backward_pointwise := by
    intro targetRelation nested nestedEnv left right accepted
    have exact :
        ledger.retraction.forwardVars left = right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [← exact, ledger.retraction.denote_forward]

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : DuplicateLedger result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked :=
  ledger.factorization.equivalent model definitionEnv
    (ledger.witness model)

end DuplicateLedger

namespace ContractLedger

noncomputable def witness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : ContractLedger result sourceArguments)
    (model : Model.{u}) :
    ArgumentFactorization.EquivalenceWitness
      ledger.factorization model where
  forward := fun sourceRelation =>
    reifyRelation model fun targetValues =>
      model.toPreModel.apply sourceRelation
        (ledger.retraction.forwardValues targetValues)
  backward := fun targetRelation =>
    reifyRelation model fun sourceValues =>
      model.toPreModel.apply targetRelation
        (ledger.retraction.backwardValues sourceValues)
  forward_pointwise := by
    intro sourceRelation nested nestedEnv left right accepted
    have exact :
        left = ledger.retraction.forwardVars right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [exact, ledger.retraction.denote_forward]
  backward_pointwise := by
    intro targetRelation nested nestedEnv left right accepted
    have exact :
        left = ledger.retraction.forwardVars right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [exact, ledger.retraction.denote_forward,
      ledger.retraction.backward_forward]

theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : ContractLedger result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked :=
  ledger.factorization.equivalent model definitionEnv
    (ledger.witness model)

end ContractLedger

/-!
## Argument deletion and extension

The same deletion evidence describes both directions. Drop presents the
deletion as source-to-target; extend presents it as target-to-source.
-/

namespace TypedArguments

structure DeletionEvidence (source target : List Sig) where
  position : Nat
  targetExact :
    ConcreteWirePrimitive.eraseAt source position = target

namespace DeletionEvidence

def forwardVars
    (evidence : DeletionEvidence source target)
    (values : Vars context source) :
    Vars context target :=
  evidence.targetExact ▸ eraseVars evidence.position values

def forwardValues
    (evidence : DeletionEvidence source target)
    (values : PreModel.Args Domain source) :
    PreModel.Args Domain target :=
  evidence.targetExact ▸ eraseValues evidence.position values

theorem denote_forward
    (evidence : DeletionEvidence source target)
    (env : Env pre context)
    (values : Vars context source) :
    Vars.denote env (evidence.forwardVars values) =
      evidence.forwardValues (Vars.denote env values) := by
  cases evidence with
  | mk position targetExact =>
      subst target
      simp only [forwardVars, forwardValues]
      exact denote_eraseVars position env values

end DeletionEvidence

end TypedArguments

def deletionRelation
    (deletion :
      TypedArguments.DeletionEvidence sourceArguments targetArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context targetArguments) : Bool :=
  TypedArguments.sameVars (deletion.forwardVars source) target

def extensionRelation
    (deletion :
      TypedArguments.DeletionEvidence targetArguments sourceArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context targetArguments) : Bool :=
  TypedArguments.sameVars source (deletion.forwardVars target)

structure DropLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  deletion :
    TypedArguments.DeletionEvidence sourceArguments result.targetArguments
  factorization :
    ArgumentFactorization result sourceArguments
      (deletionRelation deletion)

structure ExtendLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig) where
  deletion :
    TypedArguments.DeletionEvidence result.targetArguments sourceArguments
  factorization :
    ArgumentFactorization result sourceArguments
      (extensionRelation deletion)

def checkDropLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat) :
    Option (DropLedger result sourceArguments) := do
  if targetExact :
      ConcreteWirePrimitive.eraseAt sourceArguments position =
        result.targetArguments then
    let deletion :
        TypedArguments.DeletionEvidence sourceArguments
          result.targetArguments :=
      ⟨position, targetExact⟩
    let factorization ←
      checkArgumentFactorization result sourceArguments sourceSignature
        (deletionRelation deletion)
    pure ⟨deletion, factorization⟩
  else
    none

def checkExtendLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (position : Nat) :
    Option (ExtendLedger result sourceArguments) := do
  if sourceExact :
      ConcreteWirePrimitive.eraseAt result.targetArguments position =
        sourceArguments then
    let deletion :
        TypedArguments.DeletionEvidence result.targetArguments
          sourceArguments :=
      ⟨position, sourceExact⟩
    let factorization ←
      checkArgumentFactorization result sourceArguments sourceSignature
        (extensionRelation deletion)
    pure ⟨deletion, factorization⟩
  else
    none

namespace ArgumentFactorization

structure IntroducingWitness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u}) where
  forward :
    model.toPreModel.Domain (.rel sourceArguments) →
      model.toPreModel.Domain (.rel result.targetArguments)
  pointwise :
    ∀ (sourceRelation) {nested : List Sig}
      (nestedEnv : Env model.toPreModel nested)
      (left : Vars nested sourceArguments)
      (right : Vars nested result.targetArguments),
      relation left right = true →
        (model.toPreModel.apply sourceRelation
            (Vars.denote nestedEnv left) ↔
          model.toPreModel.apply (forward sourceRelation)
            (Vars.denote nestedEnv right))

structure EliminatingWitness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u}) where
  backward :
    model.toPreModel.Domain (.rel result.targetArguments) →
      model.toPreModel.Domain (.rel sourceArguments)
  pointwise :
    ∀ (targetRelation) {nested : List Sig}
      (nestedEnv : Env model.toPreModel nested)
      (left : Vars nested sourceArguments)
      (right : Vars nested result.targetArguments),
      relation left right = true →
        (model.toPreModel.apply (backward targetRelation)
            (Vars.denote nestedEnv left) ↔
          model.toPreModel.apply targetRelation
            (Vars.denote nestedEnv right))

theorem localIntroducing
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : IntroducingWitness factorization model)
    (siteEnv :
      Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody)) →
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody)) := by
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  rintro ⟨sourceValues, sourceLocalHolds⟩
  let sourceLocalEnv :=
    ContentShapeSemantics.extendValues sourceValues siteEnv
  let sourceEnv :=
    factorization.context.sourceEnvironment sourceLocalEnv
  let sourceRelation := sourceEnv _ factorization.sourceHead
  let targetRelation := witness.forward sourceRelation
  let targetEnv :
      Env model.toPreModel factorization.targetScope.frame.visible.sigs :=
    Env.comp (sourceEnv.extend targetRelation)
      (factorization.alignment.targetRenaming result.targetWire_signature)
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  have sourceHolds :
      denoteRegion model.toPreModel definitionEnv sourceEnv
        factorization.sourceScope.frame.siteBody :=
    (factorization.context.sourceBody_denotes model.toPreModel
      definitionEnv sourceLocalEnv
      factorization.sourceScope.frame.siteBody).mp sourceLocalHolds
  have reconstructed :
      Env.comp commonEnv
          (factorization.alignment.sourceRenaming
            factorization.sourceSignature) =
        sourceEnv := by
    simpa [commonEnv, sourceRelation, targetEnv] using
      factorization.reconstructSource sourceEnv targetRelation
  have targetHolds :
      denoteRegion model.toPreModel definitionEnv targetEnv
        factorization.targetScope.frame.siteBody := by
    have moved :=
      (factorization.denotes model.toPreModel definitionEnv commonEnv
        (fun nestedEnv left right accepted => by
          have targetHeadMap :=
            factorization.alignment.targetRenaming_head
              result.targetWire_signature factorization.targetHead
              factorization.targetHead_origin
          simpa [commonEnv, targetEnv, sourceRelation, targetRelation,
            Env.comp, targetHeadMap] using
              witness.pointwise sourceRelation nestedEnv left right
                accepted)).mp
        (by rw [reconstructed]; exact sourceHolds)
    simpa [commonEnv, targetEnv, weakenArgumentHead, Env.comp]
      using moved
  let targetLocalEnv :=
    factorization.context.targetLocalEnvironment targetEnv
  have targetLocalHolds :
      denoteRegion model.toPreModel definitionEnv targetLocalEnv
        (factorization.context.targetBody
          factorization.targetScope.frame.siteBody) := by
    apply
      (factorization.context.targetBody_denotes model.toPreModel
        definitionEnv targetLocalEnv
        factorization.targetScope.frame.siteBody).mpr
    dsimp only [targetLocalEnv]
    rw [factorization.context.targetEnvironment_local]
    exact targetHolds
  have targetOuter :
      ∀ {signature : Sig}
        (value : Var factorization.context.siteOuter signature),
        targetLocalEnv signature
            (Var.appendRight
              (ContentAlignment.localSignatures result.checked.val
                (result.checked.val.wires result.targetWire).scope)
              value) =
          siteEnv signature value := by
    intro signature value
    dsimp only [targetLocalEnv]
    rw [factorization.context.targetLocalEnvironment_outer]
    calc
      targetEnv signature
          (factorization.context.targetOuterEmbedding value) =
        (sourceEnv.extend targetRelation) signature
          (factorization.alignment.targetRenaming
            result.targetWire_signature
            (factorization.context.targetOuterEmbedding value)) := rfl
      _ =
        (sourceEnv.extend targetRelation) signature
          (.there
            (factorization.context.sourceOuterEmbedding value)) := by
              rw [factorization.targetOuter.agrees value]
      _ =
        sourceEnv signature
          (factorization.context.sourceOuterEmbedding value) := rfl
      _ =
        sourceLocalEnv signature
          (Var.appendRight
            (ContentAlignment.localSignatures source.val
              (source.val.wires wire).scope) value) :=
          factorization.context.sourceEnvironment_outer sourceLocalEnv value
      _ = siteEnv signature value :=
        ContentShapeSemantics.extendValues_outer sourceValues siteEnv value
  refine
    ⟨ContentShapeSemantics.valuesFromEnv
        (ContentAlignment.localSignatures result.checked.val
          (result.checked.val.wires result.targetWire).scope)
        targetLocalEnv, ?_⟩
  rw [ContentShapeSemantics.extendValues_from
    (ContentAlignment.localSignatures result.checked.val
      (result.checked.val.wires result.targetWire).scope)
    targetLocalEnv siteEnv targetOuter]
  exact targetLocalHolds

theorem localEliminating
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : EliminatingWitness factorization model)
    (siteEnv :
      Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody)) →
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody)) := by
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  rintro ⟨targetValues, targetLocalHolds⟩
  let targetLocalEnv :=
    ContentShapeSemantics.extendValues targetValues siteEnv
  let targetEnv :=
    factorization.context.targetEnvironment targetLocalEnv
  let targetRelation := targetEnv _ factorization.targetHead
  let sourceRelation := witness.backward targetRelation
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceEnv :
      Env model.toPreModel factorization.sourceScope.frame.visible.sigs :=
    Env.comp commonEnv
      (factorization.alignment.sourceRenaming
        factorization.sourceSignature)
  have targetHolds :
      denoteRegion model.toPreModel definitionEnv targetEnv
        factorization.targetScope.frame.siteBody :=
    (factorization.context.targetBody_denotes model.toPreModel
      definitionEnv targetLocalEnv
      factorization.targetScope.frame.siteBody).mp targetLocalHolds
  have sourceHolds :
      denoteRegion model.toPreModel definitionEnv sourceEnv
        factorization.sourceScope.frame.siteBody := by
    apply
      (factorization.denotes model.toPreModel definitionEnv commonEnv
        (fun nestedEnv left right accepted =>
          witness.pointwise targetRelation nestedEnv left right
            accepted)).mpr
    simpa [commonEnv, Env.comp] using targetHolds
  let sourceLocalEnv :=
    factorization.context.sourceLocalEnvironment sourceEnv
  have sourceLocalHolds :
      denoteRegion model.toPreModel definitionEnv sourceLocalEnv
        (factorization.context.sourceBody
          factorization.sourceScope.frame.siteBody) := by
    apply
      (factorization.context.sourceBody_denotes model.toPreModel
        definitionEnv sourceLocalEnv
        factorization.sourceScope.frame.siteBody).mpr
    dsimp only [sourceLocalEnv]
    rw [factorization.context.sourceEnvironment_local]
    exact sourceHolds
  have sourceOuter :
      ∀ {signature : Sig}
        (value : Var factorization.context.siteOuter signature),
        sourceLocalEnv signature
            (Var.appendRight
              (ContentAlignment.localSignatures source.val
                (source.val.wires wire).scope)
              value) =
          siteEnv signature value := by
    intro signature value
    dsimp only [sourceLocalEnv]
    rw [factorization.context.sourceLocalEnvironment_outer]
    calc
      sourceEnv signature
          (factorization.context.sourceOuterEmbedding value) =
        commonEnv signature
          (factorization.alignment.sourceRenaming
            factorization.sourceSignature
            (factorization.context.sourceOuterEmbedding value)) := rfl
      _ =
        commonEnv signature
          (.there
            (factorization.context.targetOuterEmbedding value)) := by
              rw [factorization.sourceOuter.agrees value]
      _ =
        targetEnv signature
          (factorization.context.targetOuterEmbedding value) := rfl
      _ =
        targetLocalEnv signature
          (Var.appendRight
            (ContentAlignment.localSignatures result.checked.val
              (result.checked.val.wires result.targetWire).scope)
            value) :=
          factorization.context.targetEnvironment_outer targetLocalEnv value
      _ = siteEnv signature value :=
        ContentShapeSemantics.extendValues_outer targetValues siteEnv value
  refine
    ⟨ContentShapeSemantics.valuesFromEnv
        (ContentAlignment.localSignatures source.val
          (source.val.wires wire).scope)
        sourceLocalEnv, ?_⟩
  rw [ContentShapeSemantics.extendValues_from
    (ContentAlignment.localSignatures source.val
      (source.val.wires wire).scope)
    sourceLocalEnv siteEnv sourceOuter]
  exact sourceLocalHolds

/--
Close an introducing terminal implication through the retained outer context.
An even number of cuts preserves source-to-target direction; an odd number
reverses it.
-/
theorem introducingDirections
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : IntroducingWitness factorization model) :
    (factorization.sourceScope.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) ∧
    (factorization.sourceScope.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) := by
  have propagated :=
    _root_.VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ContentAlignment.PairedContext.sourceToTarget
      factorization.context.pairedExact
      (factorization.context.sourceBody
        factorization.sourceScope.frame.siteBody)
      (factorization.context.targetBody
        factorization.targetScope.frame.siteBody)
      model.toPreModel definitionEnv Env.empty
      (fun siteEnv =>
        factorization.localIntroducing model definitionEnv witness siteEnv)
  have sourceCutDepth :
      (factorization.context.sourceVisibleExact ▸
          factorization.sourceScope.frame.context).cutDepth =
        factorization.sourceScope.frame.context.cutDepth :=
    castContext_cutDepth factorization.context.sourceVisibleExact
      factorization.sourceScope.frame.context
  have sourceFill :
      (factorization.context.sourceVisibleExact ▸
          factorization.sourceScope.frame.context).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody) =
        factorization.sourceScope.frame.context.fill
          factorization.sourceScope.frame.siteBody := by
    simpa [ContentAlignment.SiteContextFactorization.sourceBody]
      using
        castContext_fill factorization.context.sourceVisibleExact
          factorization.sourceScope.frame.context
          factorization.sourceScope.frame.siteBody
  have targetFill :
      (factorization.context.targetVisibleExact ▸
          factorization.targetScope.frame.context).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody) =
        factorization.targetScope.frame.context.fill
          factorization.targetScope.frame.siteBody := by
    simpa [ContentAlignment.SiteContextFactorization.targetBody]
      using
        castContext_fill factorization.context.targetVisibleExact
          factorization.targetScope.frame.context
          factorization.targetScope.frame.siteBody
  constructor
  · intro even sourceHolds
    have sourceRoot :=
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.sourceScope model.toPreModel definitionEnv).mp
        sourceHolds
    have sourceCasted :
        denoteRegion model.toPreModel definitionEnv Env.empty
          ((factorization.context.sourceVisibleExact ▸
              factorization.sourceScope.frame.context).fill
            (factorization.context.sourceBody
              factorization.sourceScope.frame.siteBody)) := by
      simpa only [sourceFill] using sourceRoot
    have targetCasted :=
      propagated.1
        ((congrArg (fun depth => depth % 2) sourceCutDepth).trans even)
        sourceCasted
    have targetRoot :
        denoteRegion model.toPreModel definitionEnv Env.empty
          (factorization.targetScope.frame.context.fill
            factorization.targetScope.frame.siteBody) := by
      exact targetFill ▸ targetCasted
    apply
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.targetScope model.toPreModel definitionEnv).mpr
    exact targetRoot
  · intro odd targetHolds
    have targetRoot :=
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.targetScope model.toPreModel definitionEnv).mp
        targetHolds
    have targetCasted :
        denoteRegion model.toPreModel definitionEnv Env.empty
          ((factorization.context.targetVisibleExact ▸
              factorization.targetScope.frame.context).fill
            (factorization.context.targetBody
              factorization.targetScope.frame.siteBody)) := by
      simpa only [targetFill] using targetRoot
    have sourceCasted :=
      propagated.2
        ((congrArg (fun depth => depth % 2) sourceCutDepth).trans odd)
        targetCasted
    have sourceRoot :
        denoteRegion model.toPreModel definitionEnv Env.empty
          (factorization.sourceScope.frame.context.fill
            factorization.sourceScope.frame.siteBody) := by
      simpa only [sourceFill] using sourceCasted
    apply
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.sourceScope model.toPreModel definitionEnv).mpr
    exact sourceRoot

/--
Close an eliminating terminal implication through the retained outer context.
An even number of cuts preserves target-to-source direction; an odd number
reverses it.
-/
theorem eliminatingDirections
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (witness : EliminatingWitness factorization model) :
    (factorization.sourceScope.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) ∧
    (factorization.sourceScope.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) := by
  have propagated :=
    _root_.VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ContentAlignment.PairedContext.sourceToTarget
      (_root_.VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ContentAlignment.PairedContext.symm
        factorization.context.pairedExact)
      (factorization.context.targetBody
        factorization.targetScope.frame.siteBody)
      (factorization.context.sourceBody
        factorization.sourceScope.frame.siteBody)
      model.toPreModel definitionEnv Env.empty
      (fun siteEnv =>
        factorization.localEliminating model definitionEnv witness siteEnv)
  have sourceCutDepth :
      (factorization.context.sourceVisibleExact ▸
          factorization.sourceScope.frame.context).cutDepth =
        factorization.sourceScope.frame.context.cutDepth :=
    castContext_cutDepth factorization.context.sourceVisibleExact
      factorization.sourceScope.frame.context
  have sourceFill :
      (factorization.context.sourceVisibleExact ▸
          factorization.sourceScope.frame.context).fill
          (factorization.context.sourceBody
            factorization.sourceScope.frame.siteBody) =
        factorization.sourceScope.frame.context.fill
          factorization.sourceScope.frame.siteBody := by
    simpa [ContentAlignment.SiteContextFactorization.sourceBody]
      using
        castContext_fill factorization.context.sourceVisibleExact
          factorization.sourceScope.frame.context
          factorization.sourceScope.frame.siteBody
  have targetFill :
      (factorization.context.targetVisibleExact ▸
          factorization.targetScope.frame.context).fill
          (factorization.context.targetBody
            factorization.targetScope.frame.siteBody) =
        factorization.targetScope.frame.context.fill
          factorization.targetScope.frame.siteBody := by
    simpa [ContentAlignment.SiteContextFactorization.targetBody]
      using
        castContext_fill factorization.context.targetVisibleExact
          factorization.targetScope.frame.context
          factorization.targetScope.frame.siteBody
  have targetCutDepth :
      (factorization.context.targetVisibleExact ▸
          factorization.targetScope.frame.context).cutDepth =
        factorization.targetScope.frame.context.cutDepth :=
    castContext_cutDepth factorization.context.targetVisibleExact
      factorization.targetScope.frame.context
  have cutDepths :
      factorization.targetScope.frame.context.cutDepth =
        factorization.sourceScope.frame.context.cutDepth := by
    calc
      factorization.targetScope.frame.context.cutDepth =
          (factorization.context.targetVisibleExact ▸
            factorization.targetScope.frame.context).cutDepth :=
        targetCutDepth.symm
      _ =
          (factorization.context.sourceVisibleExact ▸
            factorization.sourceScope.frame.context).cutDepth := by
        exact
          (_root_.VisualProof.ConcreteWirePrimitive.ArgumentsSemantics.ContentAlignment.PairedContext.cutDepth_eq
            factorization.context.pairedExact).symm
      _ = factorization.sourceScope.frame.context.cutDepth :=
        sourceCutDepth
  constructor
  · intro even targetHolds
    have targetRoot :=
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.targetScope model.toPreModel definitionEnv).mp
        targetHolds
    have targetCasted :
        denoteRegion model.toPreModel definitionEnv Env.empty
          ((factorization.context.targetVisibleExact ▸
              factorization.targetScope.frame.context).fill
            (factorization.context.targetBody
              factorization.targetScope.frame.siteBody)) := by
      simpa only [targetFill] using targetRoot
    have targetEven :
        (factorization.context.targetVisibleExact ▸
            factorization.targetScope.frame.context).cutDepth % 2 = 0 :=
      (congrArg (fun depth => depth % 2) targetCutDepth).trans
        ((congrArg (fun depth => depth % 2) cutDepths).trans even)
    have sourceCasted := propagated.1 targetEven targetCasted
    have sourceRoot :
        denoteRegion model.toPreModel definitionEnv Env.empty
          (factorization.sourceScope.frame.context.fill
            factorization.sourceScope.frame.siteBody) := by
      simpa only [sourceFill] using sourceCasted
    apply
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.sourceScope model.toPreModel definitionEnv).mpr
    exact sourceRoot
  · intro odd sourceHolds
    have sourceRoot :=
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.sourceScope model.toPreModel definitionEnv).mp
        sourceHolds
    have sourceCasted :
        denoteRegion model.toPreModel definitionEnv Env.empty
          ((factorization.context.sourceVisibleExact ▸
              factorization.sourceScope.frame.context).fill
            (factorization.context.sourceBody
              factorization.sourceScope.frame.siteBody)) := by
      simpa only [sourceFill] using sourceRoot
    have targetOdd :
        (factorization.context.targetVisibleExact ▸
            factorization.targetScope.frame.context).cutDepth % 2 = 1 :=
      (congrArg (fun depth => depth % 2) targetCutDepth).trans
        ((congrArg (fun depth => depth % 2) cutDepths).trans odd)
    have targetCasted := propagated.2 targetOdd sourceCasted
    have targetRoot :
        denoteRegion model.toPreModel definitionEnv Env.empty
          (factorization.targetScope.frame.context.fill
            factorization.targetScope.frame.siteBody) := by
      exact targetFill ▸ targetCasted
    apply
      (ContentShapeSemantics.SiteCompilation.denotes
        factorization.targetScope model.toPreModel definitionEnv).mpr
    exact targetRoot

end ArgumentFactorization

namespace DropLedger

/--
Dropping one argument always has the eliminating witness: a target relation
is pulled back along tuple deletion.
-/
noncomputable def eliminatingWitness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : DropLedger result sourceArguments)
    (model : Model.{u}) :
    ArgumentFactorization.EliminatingWitness
      ledger.factorization model where
  backward := fun targetRelation =>
    reifyRelation model fun sourceValues =>
      model.toPreModel.apply targetRelation
        (ledger.deletion.forwardValues sourceValues)
  pointwise := by
    intro targetRelation nested nestedEnv left right accepted
    have exact :
        ledger.deletion.forwardVars left = right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [← exact, ledger.deletion.denote_forward]

/-- The complete checked drop implication in each admissible cut parity. -/
theorem directions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : DropLedger result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    (ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) ∧
    (ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) :=
  ledger.factorization.eliminatingDirections model definitionEnv
    (ledger.eliminatingWitness model)

end DropLedger

namespace ExtendLedger

/--
Extending one argument always has the introducing witness: a source relation
is pulled back along deletion of the newly introduced coordinate.
-/
noncomputable def introducingWitness
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : ExtendLedger result sourceArguments)
    (model : Model.{u}) :
    ArgumentFactorization.IntroducingWitness
      ledger.factorization model where
  forward := fun sourceRelation =>
    reifyRelation model fun targetValues =>
      model.toPreModel.apply sourceRelation
        (ledger.deletion.forwardValues targetValues)
  pointwise := by
    intro sourceRelation nested nestedEnv left right accepted
    have exact :
        left = ledger.deletion.forwardVars right :=
      TypedArguments.sameVars_eq_true accepted
    rw [apply_reifyRelation]
    rw [exact, ledger.deletion.denote_forward]

/-- The complete checked extend implication in each admissible cut parity. -/
theorem directions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger : ExtendLedger result sourceArguments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    (ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 0 →
      denoteChecked model.toPreModel definitionEnv source →
        denoteChecked model.toPreModel definitionEnv result.checked) ∧
    (ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 1 →
      denoteChecked model.toPreModel definitionEnv result.checked →
        denoteChecked model.toPreModel definitionEnv source) :=
  ledger.factorization.introducingDirections model definitionEnv
    (ledger.introducingWitness model)

end ExtendLedger

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
