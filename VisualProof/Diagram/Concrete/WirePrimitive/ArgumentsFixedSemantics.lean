import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsTupleSemantics

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

open WirePrimitive

namespace TypedArguments

/--
Typed evidence that `larger` is obtained by inserting one fixed-signature
coordinate into `smaller`.
-/
structure InsertionEvidence
    (larger smaller : List Sig) (fixedSignature : Sig) where
  position : Nat
  largerExact :
    ConcreteWirePrimitive.insertAt smaller position fixedSignature = larger

namespace InsertionEvidence

def forwardVars
    (evidence : InsertionEvidence larger smaller fixedSignature)
    (fixed : Var context fixedSignature)
    (values : Vars context smaller) :
    Vars context larger :=
  evidence.largerExact ▸
    insertVars evidence.position fixed values

def forwardValues
    (evidence : InsertionEvidence larger smaller fixedSignature)
    (fixed : Domain fixedSignature)
    (values : PreModel.Args Domain smaller) :
    PreModel.Args Domain larger :=
  evidence.largerExact ▸
    insertValues evidence.position fixed values

theorem denote_forward
    (evidence : InsertionEvidence larger smaller fixedSignature)
    (fixed : Var context fixedSignature)
    (env : Env pre context)
    (values : Vars context smaller) :
    Vars.denote env (evidence.forwardVars fixed values) =
      evidence.forwardValues (env _ fixed) (Vars.denote env values) := by
  cases evidence with
  | mk position largerExact =>
      subst larger
      simp only [forwardVars, forwardValues]
      exact denote_insertVars position fixed env values

end InsertionEvidence

end TypedArguments

/-!
## One scope-visible parameter threaded through every intrinsic binder

The ordinary paired-shape checker accepts an arbitrary relation between hole
tuples.  Uniform drop/extend needs a stronger receipt: every larger tuple is
obtained by inserting the *same outer variable*.  The checker below threads
that variable through nested binders with `Var.there`, so a successful receipt
cannot be manufactured from unrelated per-site attachments.
-/

private def checkFixedHoles
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (fixed : Var context fixedSignature) :
    List (Vars context largerArguments) →
      List (Vars context smallerArguments) → Bool
  | [], [] => true
  | larger :: largerRest, smaller :: smallerRest =>
      TypedArguments.sameVars
          (insertion.forwardVars fixed smaller) larger &&
        checkFixedHoles insertion fixed largerRest smallerRest
  | _, _ => false

mutual

def checkFixedArgumentShape
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (fixed : Var context fixedSignature) :
    UniformIntrinsicRegion definitions largerArguments context →
      UniformIntrinsicRegion definitions smallerArguments context → Bool
  | .mk largerOrdinary largerHoles, .mk smallerOrdinary smallerHoles =>
      checkFixedArgumentItemSeq insertion fixed
          largerOrdinary smallerOrdinary &&
        checkFixedHoles insertion fixed
          largerHoles.values smallerHoles.values
termination_by larger => sizeOf larger

def checkFixedArgumentItem
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (fixed : Var context fixedSignature) :
    UniformIntrinsicItem definitions largerArguments context →
      UniformIntrinsicItem definitions smallerArguments context → Bool
  | .leaf largerItem, .leaf smallerItem =>
      decide (largerItem = smallerItem)
  | .cut largerBody, .cut smallerBody =>
      checkFixedArgumentShape insertion fixed largerBody smallerBody
  | .bind largerSignature largerBody,
      .bind smallerSignature smallerBody =>
      if same : largerSignature = smallerSignature then
        by
          subst smallerSignature
          exact
            checkFixedArgumentShape insertion (.there fixed)
              largerBody smallerBody
      else
        false
  | _, _ => false
termination_by larger => sizeOf larger

def checkFixedArgumentItemSeq
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (fixed : Var context fixedSignature) :
    UniformIntrinsicItemSeq definitions largerArguments context →
      UniformIntrinsicItemSeq definitions smallerArguments context → Bool
  | .nil, .nil => true
  | .cons largerHead largerTail, .cons smallerHead smallerTail =>
      checkFixedArgumentItem insertion fixed largerHead smallerHead &&
        checkFixedArgumentItemSeq insertion fixed largerTail smallerTail
  | _, _ => false
termination_by larger => sizeOf larger

end

private theorem checkFixedHoles_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger : List (Vars context largerArguments)}
    {smaller : List (Vars context smallerArguments)}
    (accepted :
      checkFixedHoles insertion fixed larger smaller = true)
    (pre : PreModel.{u})
    (env : Env pre context)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop)
    (pointwise :
      ∀ (largerValues : Vars context largerArguments)
        (smallerValues : Vars context smallerArguments),
        TypedArguments.sameVars
            (insertion.forwardVars fixed smallerValues)
            largerValues = true →
          (largerSite (Vars.denote env largerValues) ↔
            smallerSite (Vars.denote env smallerValues))) :
    (∀ value, value ∈ larger →
        largerSite (Vars.denote env value)) ↔
      (∀ value, value ∈ smaller →
        smallerSite (Vars.denote env value)) := by
  induction larger generalizing smaller with
  | nil =>
      cases smaller <;>
        simp [checkFixedHoles] at accepted ⊢
  | cons largerHead largerTail induction =>
      cases smaller with
      | nil =>
          simp [checkFixedHoles] at accepted
      | cons smallerHead smallerTail =>
          simp only [checkFixedHoles, Bool.and_eq_true] at accepted
          rw [List.forall_mem_cons, List.forall_mem_cons]
          exact and_congr
            (pointwise largerHead smallerHead accepted.1)
            (induction accepted.2)

mutual

theorem checkFixedArgumentShape_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicRegion definitions largerArguments context}
    {smaller :
      UniformIntrinsicRegion definitions smallerArguments context}
    (accepted :
      checkFixedArgumentShape insertion fixed larger smaller = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedFixed : Var nested fixedSignature)
        (nestedEnv : Env pre nested)
        (largerValues : Vars nested largerArguments)
        (smallerValues : Vars nested smallerArguments),
        TypedArguments.sameVars
            (insertion.forwardVars nestedFixed smallerValues)
            largerValues = true →
          (largerSite (Vars.denote nestedEnv largerValues) ↔
            smallerSite (Vars.denote nestedEnv smallerValues))) :
    larger.denote pre definitionEnv env largerSite ↔
      smaller.denote pre definitionEnv env smallerSite := by
  cases larger with
  | mk largerOrdinary largerHoles =>
    cases smaller with
    | mk smallerOrdinary smallerHoles =>
      simp only [checkFixedArgumentShape, Bool.and_eq_true] at accepted
      change
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv env largerSite _ ∧
          (∀ value, value ∈ _ →
            largerSite (Vars.denote env value))) ↔
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv env smallerSite _ ∧
          (∀ value, value ∈ _ →
            smallerSite (Vars.denote env value)))
      exact and_congr
        (checkFixedArgumentItemSeq_denotes accepted.1 pre definitionEnv env
          largerSite smallerSite pointwise)
        (checkFixedHoles_denotes accepted.2 pre env largerSite smallerSite
          (fun largerValues smallerValues matched =>
            pointwise fixed env largerValues smallerValues matched))

theorem checkFixedArgumentItem_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicItem definitions largerArguments context}
    {smaller :
      UniformIntrinsicItem definitions smallerArguments context}
    (accepted :
      checkFixedArgumentItem insertion fixed larger smaller = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedFixed : Var nested fixedSignature)
        (nestedEnv : Env pre nested)
        (largerValues : Vars nested largerArguments)
        (smallerValues : Vars nested smallerArguments),
        TypedArguments.sameVars
            (insertion.forwardVars nestedFixed smallerValues)
            largerValues = true →
          (largerSite (Vars.denote nestedEnv largerValues) ↔
            smallerSite (Vars.denote nestedEnv smallerValues))) :
    UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv env largerSite larger ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv env smallerSite smaller := by
  cases larger <;> cases smaller
  case leaf.leaf largerItem smallerItem =>
    simp only [checkFixedArgumentItem, decide_eq_true_eq] at accepted
    subst smallerItem
    exact Iff.rfl
  case cut.cut largerBody smallerBody =>
    simp only [checkFixedArgumentItem] at accepted
    exact not_congr
      (checkFixedArgumentShape_denotes accepted pre definitionEnv env
        largerSite smallerSite pointwise)
  case bind.bind largerSignature largerBody
      smallerSignature smallerBody =>
    simp only [checkFixedArgumentItem] at accepted
    split at accepted
    next same =>
      subst smallerSignature
      constructor
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkFixedArgumentShape_denotes accepted pre definitionEnv
              (env.extend value) largerSite smallerSite pointwise).mp holds⟩
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkFixedArgumentShape_denotes accepted pre definitionEnv
              (env.extend value) largerSite smallerSite pointwise).mpr holds⟩
    next different => contradiction
  all_goals simp [checkFixedArgumentItem] at accepted

theorem checkFixedArgumentItemSeq_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicItemSeq definitions largerArguments context}
    {smaller :
      UniformIntrinsicItemSeq definitions smallerArguments context}
    (accepted :
      checkFixedArgumentItemSeq insertion fixed larger smaller = true)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop)
    (pointwise :
      ∀ {nested : List Sig}
        (nestedFixed : Var nested fixedSignature)
        (nestedEnv : Env pre nested)
        (largerValues : Vars nested largerArguments)
        (smallerValues : Vars nested smallerArguments),
        TypedArguments.sameVars
            (insertion.forwardVars nestedFixed smallerValues)
            largerValues = true →
          (largerSite (Vars.denote nestedEnv largerValues) ↔
            smallerSite (Vars.denote nestedEnv smallerValues))) :
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv env largerSite larger ↔
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv env smallerSite smaller := by
  cases larger <;> cases smaller
  case nil.nil => exact Iff.rfl
  case cons.cons largerHead largerTail smallerHead smallerTail =>
    simp only [checkFixedArgumentItemSeq, Bool.and_eq_true] at accepted
    exact and_congr
      (checkFixedArgumentItem_denotes accepted.1 pre definitionEnv env
        largerSite smallerSite pointwise)
      (checkFixedArgumentItemSeq_denotes accepted.2 pre definitionEnv env
        largerSite smallerSite pointwise)
  all_goals simp [checkFixedArgumentItemSeq] at accepted

end

/-!
The specialized semantic closure below keeps the fixed value tied to the
threaded variable.  Under a binder, `Env.extend` evaluates `.there fixed` to
the same ambient value definitionally; no caller-supplied coherence premise
is needed.
-/

private theorem checkFixedHoles_reified
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger : List (Vars context largerArguments)}
    {smaller : List (Vars context smallerArguments)}
    (accepted :
      checkFixedHoles insertion fixed larger smaller = true)
    (model : Model.{u})
    (env : Env model.toPreModel context)
    (largerRelation :
      model.toPreModel.Domain (.rel largerArguments)) :
    (∀ value, value ∈ larger →
        model.toPreModel.apply largerRelation
          (Vars.denote env value)) ↔
      (∀ value, value ∈ smaller →
        model.toPreModel.apply largerRelation
          (insertion.forwardValues (env _ fixed)
            (Vars.denote env value))) := by
  induction larger generalizing smaller with
  | nil =>
      cases smaller <;>
        simp [checkFixedHoles] at accepted ⊢
  | cons largerHead largerTail induction =>
      cases smaller with
      | nil =>
          simp [checkFixedHoles] at accepted
      | cons smallerHead smallerTail =>
          simp only [checkFixedHoles, Bool.and_eq_true] at accepted
          rw [List.forall_mem_cons, List.forall_mem_cons]
          apply and_congr
          · have exact :
                insertion.forwardVars fixed smallerHead = largerHead :=
              TypedArguments.sameVars_eq_true accepted.1
            rw [← exact, insertion.denote_forward]
          · exact induction accepted.2

mutual

theorem checkFixedArgumentShape_reified
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicRegion definitions largerArguments context}
    {smaller :
      UniformIntrinsicRegion definitions smallerArguments context}
    (accepted :
      checkFixedArgumentShape insertion fixed larger smaller = true)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (env : Env model.toPreModel context)
    (largerRelation :
      model.toPreModel.Domain (.rel largerArguments)) :
    larger.denote model.toPreModel definitionEnv env
        (model.toPreModel.apply largerRelation) ↔
      smaller.denote model.toPreModel definitionEnv env
        (fun smallerValues =>
          model.toPreModel.apply largerRelation
            (insertion.forwardValues (env _ fixed) smallerValues)) := by
  cases larger with
  | mk largerOrdinary largerHoles =>
    cases smaller with
    | mk smallerOrdinary smallerHoles =>
      simp only [checkFixedArgumentShape, Bool.and_eq_true] at accepted
      change
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            model.toPreModel definitionEnv env
            (model.toPreModel.apply largerRelation) _ ∧
          (∀ value, value ∈ _ →
            model.toPreModel.apply largerRelation
              (Vars.denote env value))) ↔
        (UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            model.toPreModel definitionEnv env
            (fun smallerValues =>
              model.toPreModel.apply largerRelation
                (insertion.forwardValues (env _ fixed)
                  smallerValues)) _ ∧
          (∀ value, value ∈ _ →
            model.toPreModel.apply largerRelation
              (insertion.forwardValues (env _ fixed)
                (Vars.denote env value))))
      apply and_congr
      · exact
          checkFixedArgumentItemSeq_reified accepted.1 model
            definitionEnv env largerRelation
      · exact
          checkFixedHoles_reified accepted.2 model env largerRelation

theorem checkFixedArgumentItem_reified
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicItem definitions largerArguments context}
    {smaller :
      UniformIntrinsicItem definitions smallerArguments context}
    (accepted :
      checkFixedArgumentItem insertion fixed larger smaller = true)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (env : Env model.toPreModel context)
    (largerRelation :
      model.toPreModel.Domain (.rel largerArguments)) :
    UniformIntrinsicRegion.UniformIntrinsicItem.denote
        model.toPreModel definitionEnv env
        (model.toPreModel.apply largerRelation) larger ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
        model.toPreModel definitionEnv env
        (fun smallerValues =>
          model.toPreModel.apply largerRelation
            (insertion.forwardValues (env _ fixed) smallerValues))
        smaller := by
  cases larger <;> cases smaller
  case leaf.leaf largerItem smallerItem =>
    simp only [checkFixedArgumentItem, decide_eq_true_eq] at accepted
    subst smallerItem
    exact Iff.rfl
  case cut.cut largerBody smallerBody =>
    simp only [checkFixedArgumentItem] at accepted
    exact not_congr
      (checkFixedArgumentShape_reified accepted model definitionEnv env
        largerRelation)
  case bind.bind largerSignature largerBody
      smallerSignature smallerBody =>
    simp only [checkFixedArgumentItem] at accepted
    split at accepted
    next same =>
      subst smallerSignature
      constructor
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkFixedArgumentShape_reified accepted model definitionEnv
              (env.extend value) largerRelation).mp holds⟩
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (checkFixedArgumentShape_reified accepted model definitionEnv
              (env.extend value) largerRelation).mpr holds⟩
    next different => contradiction
  all_goals simp [checkFixedArgumentItem] at accepted

theorem checkFixedArgumentItemSeq_reified
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {fixed : Var context fixedSignature}
    {larger :
      UniformIntrinsicItemSeq definitions largerArguments context}
    {smaller :
      UniformIntrinsicItemSeq definitions smallerArguments context}
    (accepted :
      checkFixedArgumentItemSeq insertion fixed larger smaller = true)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (env : Env model.toPreModel context)
    (largerRelation :
      model.toPreModel.Domain (.rel largerArguments)) :
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        model.toPreModel definitionEnv env
        (model.toPreModel.apply largerRelation) larger ↔
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        model.toPreModel definitionEnv env
        (fun smallerValues =>
          model.toPreModel.apply largerRelation
            (insertion.forwardValues (env _ fixed) smallerValues))
        smaller := by
  cases larger <;> cases smaller
  case nil.nil => exact Iff.rfl
  case cons.cons largerHead largerTail smallerHead smallerTail =>
    simp only [checkFixedArgumentItemSeq, Bool.and_eq_true] at accepted
    exact and_congr
      (checkFixedArgumentItem_reified accepted.1 model definitionEnv env
        largerRelation)
      (checkFixedArgumentItemSeq_reified accepted.2 model definitionEnv env
        largerRelation)
  all_goals simp [checkFixedArgumentItemSeq] at accepted

end

/-!
## Checker-owned fixed-parameter receipts
-/

private def sourceArgumentShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation) :
    UniformIntrinsicRegion definitions sourceArguments
      ((.rel sourceArguments) ::
        factorization.targetScope.frame.visible.sigs) :=
  UniformIntrinsicRegion.abstractApplied
    (.here :
      Var
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs)
        (.rel sourceArguments))
    (factorization.sourceScope.frame.siteBody.renameWires
      (factorization.alignment.sourceRenaming
        factorization.sourceSignature))

private def targetArgumentShape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {relation :
      {context : List Sig} →
        Vars context sourceArguments →
        Vars context result.targetArguments → Bool}
    (factorization :
      ArgumentFactorization result sourceArguments relation) :
    UniformIntrinsicRegion definitions result.targetArguments
      ((.rel sourceArguments) ::
        factorization.targetScope.frame.visible.sigs) :=
  UniformIntrinsicRegion.abstractApplied
    (.there factorization.targetHead :
      Var
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs)
        (.rel result.targetArguments))
    (factorization.targetScope.frame.siteBody.renameWires
      (fun {_} value => .there value))

structure FixedDropLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (drop : DropLedger result sourceArguments) where
  attachment : source.val.WireId
  insertion :
    TypedArguments.InsertionEvidence sourceArguments
      result.targetArguments (source.val.wires attachment).sig
  sourceFixed :
    Var drop.factorization.sourceScope.frame.visible.sigs
      (source.val.wires attachment).sig
  sourceFixed_origin :
    ConcreteElaboration.WireContext.origin source.val
        drop.factorization.sourceScope.frame.visible.ids sourceFixed =
      attachment
  private accepted :
    checkFixedArgumentShape insertion
        (drop.factorization.alignment.sourceRenaming
          drop.factorization.sourceSignature sourceFixed)
        (sourceArgumentShape drop.factorization)
        (targetArgumentShape drop.factorization) =
      true

structure FixedExtendLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (extend : ExtendLedger result sourceArguments) where
  attachment : source.val.WireId
  insertion :
    TypedArguments.InsertionEvidence result.targetArguments
      sourceArguments (source.val.wires attachment).sig
  sourceFixed :
    Var extend.factorization.sourceScope.frame.visible.sigs
      (source.val.wires attachment).sig
  sourceFixed_origin :
    ConcreteElaboration.WireContext.origin source.val
        extend.factorization.sourceScope.frame.visible.ids sourceFixed =
      attachment
  attachment_ne_head : attachment ≠ wire
  targetFixed :
    Var extend.factorization.targetScope.frame.visible.sigs
      (source.val.wires attachment).sig
  commonFixed_exact :
    extend.factorization.alignment.sourceRenaming
        extend.factorization.sourceSignature sourceFixed =
      .there targetFixed
  private accepted :
    checkFixedArgumentShape insertion
        (.there targetFixed)
        (targetArgumentShape extend.factorization)
        (sourceArgumentShape extend.factorization) =
      true

def checkFixedDropLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (drop : DropLedger result sourceArguments)
    (attachment : source.val.WireId)
    (position : Nat) :
    Option (FixedDropLedger drop) := by
  if encloses :
      source.val.Encloses
        (source.val.wires attachment).scope
        (source.val.wires wire).scope then
    if largerExact :
        ConcreteWirePrimitive.insertAt result.targetArguments position
            (source.val.wires attachment).sig =
          sourceArguments then
      let insertion :
          TypedArguments.InsertionEvidence sourceArguments
            result.targetArguments (source.val.wires attachment).sig :=
        ⟨position, largerExact⟩
      let member :=
        drop.factorization.sourceScope.visible_of_encloses attachment
          encloses
      let sourceFixed :
          Var drop.factorization.sourceScope.frame.visible.sigs
            (source.val.wires attachment).sig :=
        InsertionCompilation.NaturalityInternal.varForMember source.val
          drop.factorization.sourceScope.frame.visible.ids attachment
          member
      have sourceFixedOrigin :
          ConcreteElaboration.WireContext.origin source.val
              drop.factorization.sourceScope.frame.visible.ids sourceFixed =
            attachment :=
        InsertionCompilation.NaturalityInternal.varForMember_origin
          source.val drop.factorization.sourceScope.frame.visible.ids
          attachment member
      let commonFixed :=
        drop.factorization.alignment.sourceRenaming
          drop.factorization.sourceSignature sourceFixed
      if accepted :
          checkFixedArgumentShape insertion commonFixed
              (sourceArgumentShape drop.factorization)
              (targetArgumentShape drop.factorization) =
            true then
        exact
          some
            ⟨attachment, insertion, sourceFixed, sourceFixedOrigin,
              accepted⟩
      else
        exact none
    else
      exact none
  else
    exact none

def checkFixedExtendLedger
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (extend : ExtendLedger result sourceArguments)
    (attachment : source.val.WireId)
    (position : Nat) :
    Option (FixedExtendLedger extend) := by
  if encloses :
      source.val.Encloses
        (source.val.wires attachment).scope
        (source.val.wires wire).scope then
    if largerExact :
        ConcreteWirePrimitive.insertAt sourceArguments position
            (source.val.wires attachment).sig =
          result.targetArguments then
      let insertion :
          TypedArguments.InsertionEvidence result.targetArguments
            sourceArguments (source.val.wires attachment).sig :=
        ⟨position, largerExact⟩
      let member :=
        extend.factorization.sourceScope.visible_of_encloses attachment
          encloses
      let sourceFixed :
          Var extend.factorization.sourceScope.frame.visible.sigs
            (source.val.wires attachment).sig :=
        InsertionCompilation.NaturalityInternal.varForMember source.val
          extend.factorization.sourceScope.frame.visible.ids attachment
          member
      have sourceFixedOrigin :
          ConcreteElaboration.WireContext.origin source.val
              extend.factorization.sourceScope.frame.visible.ids sourceFixed =
            attachment :=
        InsertionCompilation.NaturalityInternal.varForMember_origin
          source.val extend.factorization.sourceScope.frame.visible.ids
          attachment member
      if different : attachment ≠ wire then
        have notHead :
            ConcreteElaboration.WireContext.origin source.val
                extend.factorization.sourceScope.frame.visible.ids
                sourceFixed ≠
              wire := by
          simpa [sourceFixedOrigin] using different
        let targetFixed :=
          extend.factorization.alignment.sourceFallback sourceFixed notHead
        have commonFixedExact :
            extend.factorization.alignment.sourceRenaming
                extend.factorization.sourceSignature sourceFixed =
              .there targetFixed := by
          simp [RetainedHeadAlignment.sourceRenaming, notHead, targetFixed]
        if accepted :
            checkFixedArgumentShape insertion (.there targetFixed)
                (targetArgumentShape extend.factorization)
                (sourceArgumentShape extend.factorization) =
              true then
          exact
            some
              ⟨attachment, insertion, sourceFixed, sourceFixedOrigin,
                different, targetFixed, commonFixedExact, accepted⟩
        else
          exact none
      else
        exact none
    else
      exact none
  else
    exact none

namespace FixedDropLedger

noncomputable def targetRelation
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (sourceEnv :
      Env model.toPreModel
        drop.factorization.sourceScope.frame.visible.sigs) :
    model.toPreModel.Domain (.rel result.targetArguments) :=
  reifyRelation model fun targetValues =>
    model.toPreModel.apply
      (sourceEnv _ drop.factorization.sourceHead)
      (fixed.insertion.forwardValues
        (sourceEnv _ fixed.sourceFixed) targetValues)

noncomputable def targetEnvironment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (sourceEnv :
      Env model.toPreModel
        drop.factorization.sourceScope.frame.visible.sigs) :
    Env model.toPreModel
      drop.factorization.targetScope.frame.visible.sigs :=
  Env.comp
    (sourceEnv.extend (fixed.targetRelation model sourceEnv))
    (drop.factorization.alignment.targetRenaming
      result.targetWire_signature)

private noncomputable def commonEnvironment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (sourceEnv :
      Env model.toPreModel
        drop.factorization.sourceScope.frame.visible.sigs) :
    Env model.toPreModel
      ((.rel sourceArguments) ::
        drop.factorization.targetScope.frame.visible.sigs) :=
  (fixed.targetEnvironment model sourceEnv).extend
    (sourceEnv _ drop.factorization.sourceHead)

/--
At the acted scope, a fixed-parameter drop equates the source body with the
target body interpreted by the reified fixed-coordinate relation.
-/
theorem scopeDenotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (sourceEnv :
      Env model.toPreModel
        drop.factorization.sourceScope.frame.visible.sigs) :
    denoteRegion model.toPreModel definitionEnv sourceEnv
        drop.factorization.sourceScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv
        (fixed.targetEnvironment model sourceEnv)
        drop.factorization.targetScope.frame.siteBody := by
  let factorization := drop.factorization
  let sourceRelation :=
    sourceEnv _ factorization.sourceHead
  let targetRelation := fixed.targetRelation model sourceEnv
  let targetEnv := fixed.targetEnvironment model sourceEnv
  let commonEnv := fixed.commonEnvironment model sourceEnv
  let commonFixed :=
    factorization.alignment.sourceRenaming
      factorization.sourceSignature fixed.sourceFixed
  have reconstructed :
      Env.comp commonEnv
          (factorization.alignment.sourceRenaming
            factorization.sourceSignature) =
        sourceEnv := by
    simpa [commonEnv, commonEnvironment, targetEnv, targetEnvironment,
      targetRelation] using
      factorization.reconstructSource sourceEnv targetRelation
  have fixedValue :
      commonEnv _ commonFixed =
        sourceEnv _ fixed.sourceFixed := by
    have atFixed :=
      congrFun (congrFun reconstructed
        (source.val.wires fixed.attachment).sig) fixed.sourceFixed
    simpa [Env.comp, commonFixed] using atFixed
  let sourceRenaming :
      WireRenaming factorization.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    fun {_} value =>
      factorization.alignment.sourceRenaming
        factorization.sourceSignature value
  let sourceBody :=
    factorization.sourceScope.frame.siteBody.renameWires sourceRenaming
  let targetRenaming :
      WireRenaming factorization.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  let targetBody :=
    factorization.targetScope.frame.siteBody.renameWires
      targetRenaming
  have fixedShapes :=
    checkFixedArgumentShape_reified fixed.accepted model definitionEnv
      commonEnv sourceRelation
  have targetSiteCongruence :=
    (targetArgumentShape factorization).denote_site_congr
      model.toPreModel definitionEnv commonEnv
      (fun targetValues =>
        model.toPreModel.apply sourceRelation
          (fixed.insertion.forwardValues
            (commonEnv _ commonFixed) targetValues))
      (model.toPreModel.apply targetRelation)
      (fun targetValues => by
        dsimp [targetRelation, FixedDropLedger.targetRelation]
        rw [apply_reifyRelation, fixedValue])
  have paired :
      (sourceArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation) ↔
        (targetArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) :=
    fixedShapes.trans targetSiteCongruence
  have targetHeadValue :
      commonEnv _ (.there factorization.targetHead) =
        targetRelation := by
    dsimp [commonEnv, commonEnvironment, targetEnv, targetEnvironment]
    simp only [Env.extend_there, Env.comp]
    rw [factorization.alignment.targetRenaming_head
      result.targetWire_signature factorization.targetHead
      factorization.targetHead_origin]
    rfl
  have targetAbstract :
      denoteRegion model.toPreModel definitionEnv commonEnv targetBody ↔
        (targetArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) := by
    simpa only [targetHeadValue] using
      UniformIntrinsicRegion.abstractApplied_denotes model.toPreModel
        definitionEnv commonEnv (.there factorization.targetHead)
        targetBody
  have transported :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          factorization.sourceScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          factorization.targetScope.frame.siteBody := by
    exact
      (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
        sourceRenaming
        factorization.sourceScope.frame.siteBody).symm.trans
        ((UniformIntrinsicRegion.abstractApplied_denotes model.toPreModel
          definitionEnv commonEnv
          (.here :
            Var
              ((.rel sourceArguments) ::
                factorization.targetScope.frame.visible.sigs)
              (.rel sourceArguments))
          sourceBody).trans
          (paired.trans
            (targetAbstract.symm.trans
              (denoteRegion_renameWires model.toPreModel definitionEnv
                commonEnv targetRenaming
                factorization.targetScope.frame.siteBody))))
  have sourceEnvironmentExact :
      Env.comp commonEnv sourceRenaming = sourceEnv := by
    simpa [sourceRenaming] using reconstructed
  have targetEnvironmentExact :
      Env.comp commonEnv targetRenaming = targetEnv := by
    funext signature value
    rfl
  simpa only [sourceEnvironmentExact, targetEnvironmentExact] using
    transported

/--
The fixed-coordinate witness supplies the otherwise unavailable introducing
direction of argument drop at the complete local binder block.
-/
theorem localIntroducing
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (siteEnv :
      Env model.toPreModel drop.factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                drop.factorization.context.siteOuter)
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                drop.factorization.context.siteOuter))).fill
          (drop.factorization.context.sourceBody
            drop.factorization.sourceScope.frame.siteBody)) →
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                drop.factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                drop.factorization.context.siteOuter))).fill
          (drop.factorization.context.targetBody
            drop.factorization.targetScope.frame.siteBody)) := by
  let factorization := drop.factorization
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  rintro ⟨sourceValues, sourceLocalHolds⟩
  let sourceLocalEnv :=
    ContentShapeSemantics.extendValues sourceValues siteEnv
  let sourceEnv :=
    factorization.context.sourceEnvironment sourceLocalEnv
  let targetEnv := fixed.targetEnvironment model sourceEnv
  have sourceHolds :
      denoteRegion model.toPreModel definitionEnv sourceEnv
        factorization.sourceScope.frame.siteBody :=
    (factorization.context.sourceBody_denotes model.toPreModel
      definitionEnv sourceLocalEnv
      factorization.sourceScope.frame.siteBody).mp sourceLocalHolds
  have targetHolds :
      denoteRegion model.toPreModel definitionEnv targetEnv
        factorization.targetScope.frame.siteBody :=
    (fixed.scopeDenotes model definitionEnv sourceEnv).mp sourceHolds
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
        (sourceEnv.extend (fixed.targetRelation model sourceEnv)) signature
          (factorization.alignment.targetRenaming
            result.targetWire_signature
            (factorization.context.targetOuterEmbedding value)) := rfl
      _ =
        (sourceEnv.extend (fixed.targetRelation model sourceEnv)) signature
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

/-- A scope-visible uniform drop is an ungated full-model equivalence. -/
theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {drop : DropLedger result sourceArguments}
    (fixed : FixedDropLedger drop)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      drop.factorization.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      drop.factorization.targetScope model.toPreModel definitionEnv]
  exact
    drop.factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        ⟨fixed.localIntroducing model definitionEnv siteEnv,
          drop.factorization.localEliminating model definitionEnv
            (drop.eliminatingWitness model) siteEnv⟩)

end FixedDropLedger

namespace FixedExtendLedger

noncomputable def sourceRelation
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {extend : ExtendLedger result sourceArguments}
    (fixed : FixedExtendLedger extend)
    (model : Model.{u})
    (targetEnv :
      Env model.toPreModel
        extend.factorization.targetScope.frame.visible.sigs) :
    model.toPreModel.Domain (.rel sourceArguments) :=
  reifyRelation model fun sourceValues =>
    model.toPreModel.apply
      (targetEnv _ extend.factorization.targetHead)
      (fixed.insertion.forwardValues
        (targetEnv _ fixed.targetFixed) sourceValues)

noncomputable def sourceEnvironment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {extend : ExtendLedger result sourceArguments}
    (fixed : FixedExtendLedger extend)
    (model : Model.{u})
    (targetEnv :
      Env model.toPreModel
        extend.factorization.targetScope.frame.visible.sigs) :
    Env model.toPreModel
      extend.factorization.sourceScope.frame.visible.sigs :=
  Env.comp
    (targetEnv.extend (fixed.sourceRelation model targetEnv))
    (extend.factorization.alignment.sourceRenaming
      extend.factorization.sourceSignature)

/--
At the acted scope, fixed-parameter extension admits the missing
target-to-source relation witness.
-/
theorem scopeDenotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {extend : ExtendLedger result sourceArguments}
    (fixed : FixedExtendLedger extend)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (targetEnv :
      Env model.toPreModel
        extend.factorization.targetScope.frame.visible.sigs) :
    denoteRegion model.toPreModel definitionEnv targetEnv
        extend.factorization.targetScope.frame.siteBody ↔
      denoteRegion model.toPreModel definitionEnv
        (fixed.sourceEnvironment model targetEnv)
        extend.factorization.sourceScope.frame.siteBody := by
  let factorization := extend.factorization
  let targetRelation :=
    targetEnv _ factorization.targetHead
  let sourceRelation := fixed.sourceRelation model targetEnv
  let commonEnv :
      Env model.toPreModel
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    targetEnv.extend sourceRelation
  let sourceRenaming :
      WireRenaming factorization.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    fun {_} value =>
      factorization.alignment.sourceRenaming
        factorization.sourceSignature value
  let targetRenaming :
      WireRenaming factorization.targetScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    fun {_} value => .there value
  let sourceBody :=
    factorization.sourceScope.frame.siteBody.renameWires sourceRenaming
  let targetBody :=
    factorization.targetScope.frame.siteBody.renameWires targetRenaming
  have fixedShapes :=
    checkFixedArgumentShape_reified fixed.accepted model definitionEnv
      commonEnv targetRelation
  have sourceSiteCongruence :=
    (sourceArgumentShape factorization).denote_site_congr
      model.toPreModel definitionEnv commonEnv
      (fun sourceValues =>
        model.toPreModel.apply targetRelation
          (fixed.insertion.forwardValues
            (commonEnv _ (.there fixed.targetFixed)) sourceValues))
      (model.toPreModel.apply sourceRelation)
      (fun sourceValues => by
        dsimp [commonEnv, targetRelation]
        dsimp [sourceRelation, FixedExtendLedger.sourceRelation]
        rw [apply_reifyRelation])
  have paired :
      (targetArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) ↔
        (sourceArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation) :=
    fixedShapes.trans sourceSiteCongruence
  have targetHeadValue :
      commonEnv _ (.there factorization.targetHead) =
        targetRelation := rfl
  have targetAbstract :
      denoteRegion model.toPreModel definitionEnv commonEnv targetBody ↔
        (targetArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply targetRelation) := by
    simpa only [targetHeadValue] using
      UniformIntrinsicRegion.abstractApplied_denotes model.toPreModel
        definitionEnv commonEnv (.there factorization.targetHead)
        targetBody
  have sourceHeadValue :
      commonEnv _ (.here :
          Var
            ((.rel sourceArguments) ::
              factorization.targetScope.frame.visible.sigs)
            (.rel sourceArguments)) =
        sourceRelation := rfl
  have sourceAbstract :
      denoteRegion model.toPreModel definitionEnv commonEnv sourceBody ↔
        (sourceArgumentShape factorization).denote
          model.toPreModel definitionEnv commonEnv
          (model.toPreModel.apply sourceRelation) := by
    simpa only [sourceHeadValue] using
      UniformIntrinsicRegion.abstractApplied_denotes model.toPreModel
        definitionEnv commonEnv
        (.here :
          Var
            ((.rel sourceArguments) ::
              factorization.targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        sourceBody
  have transported :
      denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv targetRenaming)
          factorization.targetScope.frame.siteBody ↔
        denoteRegion model.toPreModel definitionEnv
          (Env.comp commonEnv sourceRenaming)
          factorization.sourceScope.frame.siteBody := by
    exact
      (denoteRegion_renameWires model.toPreModel definitionEnv commonEnv
        targetRenaming
        factorization.targetScope.frame.siteBody).symm.trans
        (targetAbstract.trans
          (paired.trans
            (sourceAbstract.symm.trans
              (denoteRegion_renameWires model.toPreModel definitionEnv
                commonEnv sourceRenaming
                factorization.sourceScope.frame.siteBody))))
  have targetEnvironmentExact :
      Env.comp commonEnv targetRenaming = targetEnv := by
    funext signature value
    rfl
  have sourceEnvironmentExact :
      Env.comp commonEnv sourceRenaming =
        fixed.sourceEnvironment model targetEnv := by
    rfl
  simpa only [targetEnvironmentExact, sourceEnvironmentExact] using
    transported

/--
The fixed-coordinate witness supplies the otherwise unavailable eliminating
direction of argument extension at the complete local binder block.
-/
theorem localEliminating
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {extend : ExtendLedger result sourceArguments}
    (fixed : FixedExtendLedger extend)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (siteEnv :
      Env model.toPreModel extend.factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                extend.factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                extend.factorization.context.siteOuter))).fill
          (extend.factorization.context.targetBody
            extend.factorization.targetScope.frame.siteBody)) →
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures source.val
            (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                extend.factorization.context.siteOuter)
              (ContentAlignment.localSignatures source.val
                  (source.val.wires wire).scope ++
                extend.factorization.context.siteOuter))).fill
          (extend.factorization.context.sourceBody
            extend.factorization.sourceScope.frame.siteBody)) := by
  let factorization := extend.factorization
  rw [ContentShapeSemantics.denote_bindMany,
    ContentShapeSemantics.denote_bindMany]
  rintro ⟨targetValues, targetLocalHolds⟩
  let targetLocalEnv :=
    ContentShapeSemantics.extendValues targetValues siteEnv
  let targetEnv :=
    factorization.context.targetEnvironment targetLocalEnv
  let sourceEnv := fixed.sourceEnvironment model targetEnv
  have targetHolds :
      denoteRegion model.toPreModel definitionEnv targetEnv
        factorization.targetScope.frame.siteBody :=
    (factorization.context.targetBody_denotes model.toPreModel
      definitionEnv targetLocalEnv
      factorization.targetScope.frame.siteBody).mp targetLocalHolds
  have sourceHolds :
      denoteRegion model.toPreModel definitionEnv sourceEnv
        factorization.sourceScope.frame.siteBody :=
    (fixed.scopeDenotes model definitionEnv targetEnv).mp targetHolds
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
        (targetEnv.extend
            (fixed.sourceRelation model targetEnv)) signature
          (factorization.alignment.sourceRenaming
            factorization.sourceSignature
            (factorization.context.sourceOuterEmbedding value)) := rfl
      _ =
        (targetEnv.extend
            (fixed.sourceRelation model targetEnv)) signature
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

/-- A scope-visible uniform extension is an ungated full-model equivalence. -/
theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    {extend : ExtendLedger result sourceArguments}
    (fixed : FixedExtendLedger extend)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes
      extend.factorization.sourceScope model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes
      extend.factorization.targetScope model.toPreModel definitionEnv]
  exact
    extend.factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        ⟨extend.factorization.localIntroducing model definitionEnv
            (extend.introducingWitness model) siteEnv,
          fixed.localEliminating model definitionEnv siteEnv⟩)

end FixedExtendLedger

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
