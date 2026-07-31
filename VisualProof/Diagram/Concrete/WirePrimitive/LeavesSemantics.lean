import VisualProof.Diagram.Concrete.WirePrimitive.Leaves
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationSemantics
import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof

namespace ConcreteWirePrimitive

namespace LeavesSemantics

universe u

open WirePrimitive
open ArgumentsSemantics

namespace LeafTypedArguments

/-- Convert a homogeneous intrinsic port list into its typed tuple. -/
def varsOfReplicate :
    (ports : List (Var context signature)) →
      Vars context (List.replicate ports.length signature)
  | [] => .nil
  | head :: tail => .cons head (varsOfReplicate tail)

/-- Convert the semantic counterpart of a replicated tuple to a plain list. -/
def valuesOfReplicate :
    (arity : Nat) →
      PreModel.Args Domain (List.replicate arity signature) →
        List (Domain signature)
  | 0, PUnit.unit => []
  | _ + 1, ⟨head, tail⟩ =>
      head :: valuesOfReplicate _ tail

@[simp] theorem denote_varsOfReplicate
    (env : Env pre context)
    (ports : List (Var context signature)) :
    valuesOfReplicate ports.length
        (Vars.denote env (varsOfReplicate ports)) =
      ports.map (env signature) := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [varsOfReplicate, Vars.denote_cons, valuesOfReplicate,
        List.map_cons]
      exact congrArg (List.cons (env signature head)) induction

@[simp] theorem split_forward_values
    (evidence :
      ArgumentsSemantics.TypedArguments.InsertionEvidence
        larger smaller fixedSignature)
    (fixed : Domain fixedSignature)
    (values : PreModel.Args Domain smaller) :
    evidence.splitValues (evidence.forwardValues fixed values) =
      ⟨fixed, values⟩ := by
  cases evidence with
  | mk position largerExact =>
      subst larger
      induction smaller generalizing position with
      | nil =>
          cases position <;> rfl
      | cons signature rest induction =>
          rcases values with ⟨head, tail⟩
          cases position with
          | zero => rfl
          | succ position =>
              simp only [
                ArgumentsSemantics.TypedArguments.InsertionEvidence.splitValues,
                ArgumentsSemantics.TypedArguments.InsertionEvidence.forwardValues,
                ArgumentsSemantics.TypedArguments.insertValues]
              exact congrArg (fun split => (split.1, (head, split.2)))
                (induction tail position)

end LeafTypedArguments

/--
Semantic description of one checked leaf family.  `targetArguments` is the
intrinsic tuple exposed by the replacement leaf; `sourceFromTarget` embeds it
into the consumed relation signature.
-/
inductive LeafKind
    (definitions : List (List Sig))
    (sourceArguments : List Sig) : Type
  | formal
      (rest : List Sig)
      (insertion :
        ArgumentsSemantics.TypedArguments.InsertionEvidence
          sourceArguments rest (.rel rest))
  | identity
      (signature : Sig)
      (arity : Nat)
      (atLeastTwo : 2 ≤ arity)
      (sourceExact :
        List.replicate arity signature = sourceArguments)
  | reference
      (definition : Fin definitions.length)
      (sourceExact :
        definitions.get definition = sourceArguments)

namespace LeafKind

/-- Derive the exact typed insertion evidence for formal application. -/
def checkFormal
    (sourceArguments : List Sig)
    (position : Nat) :
    Option (LeafKind definitions sourceArguments) :=
  let rest := ConcreteWirePrimitive.eraseAt sourceArguments position
  if exact :
      ConcreteWirePrimitive.insertAt rest position (.rel rest) =
        sourceArguments then
    some (.formal rest ⟨position, exact⟩)
  else none

/-- Derive the exact repeated-signature evidence for an identity leaf. -/
def checkIdentity
    (sourceArguments : List Sig) :
    Option (LeafKind definitions sourceArguments) :=
  match sourceArguments with
  | [] => none
  | signature :: tail =>
      let arity := (signature :: tail).length
      if atLeastTwo : 2 ≤ arity then
        if exact :
            List.replicate arity signature = signature :: tail then
          some (.identity signature arity atLeastTwo exact)
        else none
      else none

/-- Derive the exact chronological signature evidence for a folded reference. -/
def checkReference
    (sourceArguments : List Sig)
    (definition : Fin definitions.length) :
    Option (LeafKind definitions sourceArguments) :=
  if exact : definitions.get definition = sourceArguments then
    some (.reference definition exact)
  else none

def targetArguments :
    LeafKind definitions sourceArguments → List Sig
  | .formal rest _ => .rel rest :: rest
  | .identity signature arity _ _ =>
      List.replicate arity signature
  | .reference definition _ =>
      definitions.get definition

def sourceFromTarget
    (kind : LeafKind definitions sourceArguments) :
    Vars context kind.targetArguments → Vars context sourceArguments :=
  match kind with
  | .formal _ insertion =>
      fun
        | .cons head tail => insertion.forwardVars head tail
  | .identity _ _ _ sourceExact =>
      fun values => sourceExact ▸ values
  | .reference _ sourceExact =>
      fun values => sourceExact ▸ values

def sourceValuesFromTarget
    (kind : LeafKind definitions sourceArguments) :
    PreModel.Args Domain kind.targetArguments →
      PreModel.Args Domain sourceArguments :=
  match kind with
  | .formal _ insertion =>
      fun values =>
        insertion.forwardValues values.1 values.2
  | .identity _ _ _ sourceExact =>
      fun values => sourceExact ▸ values
  | .reference _ sourceExact =>
      fun values => sourceExact ▸ values

theorem denote_sourceFromTarget
    (kind : LeafKind definitions sourceArguments)
    (env : Env pre context)
    (values : Vars context kind.targetArguments) :
    Vars.denote env (kind.sourceFromTarget values) =
      kind.sourceValuesFromTarget (Vars.denote env values) := by
  cases kind with
  | formal rest insertion =>
      cases values with
      | cons head tail =>
          exact insertion.denote_forward head env tail
  | identity signature arity atLeastTwo sourceExact =>
      subst sourceArguments
      rfl
  | reference definition sourceExact =>
      subst sourceArguments
      rfl

def targetSite
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    PreModel.Args pre.Domain kind.targetArguments → Prop :=
  match kind with
  | .formal _ _ =>
      fun values => pre.apply values.1 values.2
  | .identity _ arity _ _ =>
      fun values =>
        AllEqual (LeafTypedArguments.valuesOfReplicate arity values)
  | .reference definition _ =>
      fun values =>
        definitionEnv.lookup
          (ConcreteElaboration.Internal.definitionVarAt
            definitions definition)
          values

def sourceSite
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    PreModel.Args pre.Domain sourceArguments → Prop :=
  match kind with
  | .formal _ insertion =>
      fun values =>
        let split := insertion.splitValues values
        pre.apply split.1 split.2
  | .identity _ arity _ sourceExact =>
      fun values =>
        AllEqual
          (LeafTypedArguments.valuesOfReplicate arity
            (sourceExact.symm ▸ values))
  | .reference definition sourceExact =>
      fun values =>
        definitionEnv.lookup
          (ConcreteElaboration.Internal.definitionVarAt
            definitions definition)
          (sourceExact.symm ▸ values)

theorem sourceSite_forward
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (values : PreModel.Args pre.Domain kind.targetArguments) :
    kind.sourceSite pre definitionEnv
        (kind.sourceValuesFromTarget values) ↔
      kind.targetSite pre definitionEnv values := by
  cases kind with
  | formal rest insertion =>
      rcases values with ⟨head, tail⟩
      simp only [sourceSite, sourceValuesFromTarget, targetSite]
      rw [LeafTypedArguments.split_forward_values]
  | identity signature arity atLeastTwo sourceExact =>
      subst sourceArguments
      rfl
  | reference definition sourceExact =>
      subst sourceArguments
      rfl

def relation
    (kind : LeafKind definitions sourceArguments)
    {context : List Sig}
    (source : Vars context sourceArguments)
    (target : Vars context kind.targetArguments) : Bool :=
  TypedArguments.sameVars source (kind.sourceFromTarget target)

theorem relation_denotes
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (source : Vars context sourceArguments)
    (target : Vars context kind.targetArguments)
    (accepted : kind.relation source target = true) :
    kind.sourceSite pre definitionEnv (Vars.denote env source) ↔
      kind.targetSite pre definitionEnv (Vars.denote env target) := by
  have exact :
      source = kind.sourceFromTarget target :=
    TypedArguments.sameVars_eq_true accepted
  rw [exact, kind.denote_sourceFromTarget]
  exact kind.sourceSite_forward pre definitionEnv _

end LeafKind

private def DefVar.decEq :
    (left right : DefVar definitions arguments) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private instance : DecidableEq (DefVar definitions arguments) :=
  DefVar.decEq

/-- Recognize one target leaf and recover its semantic hole tuple. -/
private def matchLeaf?
    (kind : LeafKind definitions sourceArguments) :
    Item definitions context →
      Option (Vars context sourceArguments)
  := match kind with
    | .formal rest insertion =>
      fun
      | .atom (args := arguments) head values =>
          if argumentsExact : arguments = rest then
            some
              (insertion.forwardVars
                (argumentsExact ▸ head)
                (argumentsExact ▸ values))
          else none
      | _ => none
    | .reference expected sourceExact =>
      fun
      | .named (args := arguments) definition values =>
          if argumentsExact : arguments = definitions.get expected then
            let expectedVar :=
              ConcreteElaboration.Internal.definitionVarAt
                definitions expected
            if same : argumentsExact ▸ definition = expectedVar then
              some (by
                exact sourceExact ▸ (argumentsExact ▸ values))
            else none
          else none
      | _ => none
    | .identity expected arity _ sourceExact =>
      fun
      | .identity signature ports _ =>
          if signatureExact : signature = expected then
            if arityExact : ports.length = arity then
              some
                (sourceExact ▸
                  arityExact ▸
                    signatureExact ▸
                      LeafTypedArguments.varsOfReplicate ports)
            else none
          else none
      | _ => none

private def prependOrdinary
    (item : UniformIntrinsicItem definitions arguments context) :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicRegion definitions arguments context
  | .mk ordinary holes => .mk (.cons item ordinary) holes

private def prependHole
    (values : Vars context arguments) :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicRegion definitions arguments context
  | .mk ordinary holes => .mk ordinary ⟨values :: holes.values⟩

private theorem prependOrdinary_denotes
    (item : UniformIntrinsicItem definitions arguments context)
    (rest : UniformIntrinsicRegion definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (site : PreModel.Args pre.Domain arguments → Prop) :
    (prependOrdinary item rest).denote pre definitionEnv env site ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
          pre definitionEnv env site item ∧
        rest.denote pre definitionEnv env site := by
  cases rest
  simp [prependOrdinary, UniformIntrinsicRegion.denote,
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote, and_assoc]

private theorem prependHole_denotes
    (values : Vars context arguments)
    (rest : UniformIntrinsicRegion definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (site : PreModel.Args pre.Domain arguments → Prop) :
    (prependHole values rest).denote pre definitionEnv env site ↔
      site (Vars.denote env values) ∧
        rest.denote pre definitionEnv env site := by
  cases rest
  rename_i ordinary holes
  simp only [prependHole, UniformIntrinsicRegion.denote]
  change
    (_ ∧ (∀ candidate, candidate ∈ values :: holes.values →
      site (Vars.denote env candidate))) ↔
      site (Vars.denote env values) ∧
        (_ ∧ (∀ candidate, candidate ∈ holes.values →
          site (Vars.denote env candidate)))
  constructor
  · rintro ⟨ordinaryHolds, allHolds⟩
    refine
      ⟨allHolds values (by simp), ordinaryHolds, ?_⟩
    intro candidate member
    exact allHolds candidate (by simp [member])
  · rintro ⟨valueHolds, ordinaryHolds, holesHold⟩
    refine ⟨ordinaryHolds, ?_⟩
    intro candidate member
    simp only [List.mem_cons] at member
    rcases member with same | member
    · cases same
      exact valueHolds
    · exact holesHold candidate member

mutual

private def abstractLeafStep
    (kind : LeafKind definitions sourceArguments)
    (item : Item definitions context)
    (rest : UniformIntrinsicRegion definitions sourceArguments context) :
    UniformIntrinsicRegion definitions sourceArguments context :=
  match matchLeaf? kind item with
  | some values => prependHole values rest
  | none =>
      match item with
      | .cut body =>
          prependOrdinary (.cut (abstractLeaf kind body)) rest
      | .bind signature body =>
          prependOrdinary
            (.bind signature (abstractLeaf kind body)) rest
      | ordinary =>
          prependOrdinary (.leaf ordinary) rest

/-- Abstract precisely the direct leaves selected by one semantic kind. -/
def abstractLeaf
    (kind : LeafKind definitions sourceArguments) :
    Region definitions context →
      UniformIntrinsicRegion definitions sourceArguments context
  | .mk items => abstractLeafItems kind items

private def abstractLeafItems
    (kind : LeafKind definitions sourceArguments) :
    ItemSeq definitions context →
      UniformIntrinsicRegion definitions sourceArguments context
  | .nil => .mk .nil ⟨[]⟩
  | .cons item tail =>
      abstractLeafStep kind item (abstractLeafItems kind tail)

end

private theorem abstractLeafItems_cons_some
    (kind : LeafKind definitions sourceArguments)
    (item : Item definitions context)
    (tail : ItemSeq definitions context)
    (values : Vars context sourceArguments)
    (matched : matchLeaf? kind item = some values) :
    abstractLeafItems kind (.cons item tail) =
      prependHole values (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind item (abstractLeafItems kind tail) =
      prependHole values (abstractLeafItems kind tail)
  unfold abstractLeafStep
  rw [matched]

private theorem abstractLeafItems_cons_atom
    (kind : LeafKind definitions sourceArguments)
    (head : Var context (.rel arguments))
    (values : Vars context arguments)
    (tail : ItemSeq definitions context)
    (matched : matchLeaf? kind (.atom head values) = none) :
    abstractLeafItems kind (.cons (.atom head values) tail) =
      prependOrdinary (.leaf (.atom head values))
        (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind (.atom head values)
        (abstractLeafItems kind tail) =
      _
  unfold abstractLeafStep
  rw [matched]

private theorem abstractLeafItems_cons_named
    (kind : LeafKind definitions sourceArguments)
    (definition : DefVar definitions arguments)
    (values : Vars context arguments)
    (tail : ItemSeq definitions context)
    (matched : matchLeaf? kind (.named definition values) = none) :
    abstractLeafItems kind (.cons (.named definition values) tail) =
      prependOrdinary (.leaf (.named definition values))
        (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind (.named definition values)
        (abstractLeafItems kind tail) =
      _
  unfold abstractLeafStep
  rw [matched]

private theorem abstractLeafItems_cons_identity
    (kind : LeafKind definitions sourceArguments)
    (signature : Sig)
    (ports : List (Var context signature))
    (atLeastTwo : 2 ≤ ports.length)
    (tail : ItemSeq definitions context)
    (matched :
      matchLeaf? kind (.identity signature ports atLeastTwo) = none) :
    abstractLeafItems kind
        (.cons (.identity signature ports atLeastTwo) tail) =
      prependOrdinary (.leaf (.identity signature ports atLeastTwo))
        (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind (.identity signature ports atLeastTwo)
        (abstractLeafItems kind tail) =
      _
  unfold abstractLeafStep
  rw [matched]

private theorem abstractLeafItems_cons_cut
    (kind : LeafKind definitions sourceArguments)
    (body : Region definitions context)
    (tail : ItemSeq definitions context) :
    abstractLeafItems kind (.cons (.cut body) tail) =
      prependOrdinary (.cut (abstractLeaf kind body))
        (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind (.cut body) (abstractLeafItems kind tail) = _
  unfold abstractLeafStep
  have matched : matchLeaf? kind (.cut body) = none := by
    cases kind <;> rfl
  rw [matched]

private theorem abstractLeafItems_cons_bind
    (kind : LeafKind definitions sourceArguments)
    (signature : Sig)
    (body : Region definitions (signature :: context))
    (tail : ItemSeq definitions context) :
    abstractLeafItems kind (.cons (.bind signature body) tail) =
      prependOrdinary (.bind signature (abstractLeaf kind body))
        (abstractLeafItems kind tail) := by
  change
    abstractLeafStep kind (.bind signature body)
        (abstractLeafItems kind tail) = _
  unfold abstractLeafStep
  have matched : matchLeaf? kind (.bind signature body) = none := by
    cases kind <;> rfl
  rw [matched]

private theorem matchLeaf_denotes
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (item : Item definitions context)
    (values : Vars context sourceArguments)
    (matched : matchLeaf? kind item = some values) :
    denoteItem pre definitionEnv env item ↔
      kind.sourceSite pre definitionEnv (Vars.denote env values) := by
  cases kind with
  | formal rest insertion =>
      obtain ⟨position, largerExact⟩ := insertion
      subst sourceArguments
      cases item with
      | atom head argumentsVars =>
          simp only [matchLeaf?] at matched
          split at matched
          · rename_i argumentsExact
            subst rest
            cases Option.some.inj matched
            simp only [denoteItem, LeafKind.sourceSite]
            rw [ArgumentsSemantics.TypedArguments.InsertionEvidence.denote_forward]
            rw [LeafTypedArguments.split_forward_values]
          · contradiction
      | _ => simp [matchLeaf?] at matched
  | identity expected arity atLeastTwo sourceExact =>
      subst sourceArguments
      cases item with
      | identity signature ports portsAtLeastTwo =>
          simp only [matchLeaf?] at matched
          split at matched
          · rename_i signatureExact
            subst expected
            split at matched
            · rename_i arityExact
              subst arity
              cases Option.some.inj matched
              simp only [denoteItem, LeafKind.sourceSite]
              exact iff_of_eq
                (congrArg AllEqual
                  (LeafTypedArguments.denote_varsOfReplicate env ports).symm)
            · contradiction
          · contradiction
      | _ => simp [matchLeaf?] at matched
  | reference expected sourceExact =>
      subst sourceArguments
      cases item with
      | named definition valuesVars =>
          simp only [matchLeaf?] at matched
          split at matched
          · rename_i argumentsExact
            cases argumentsExact
            split at matched
            · rename_i same
              cases same
              cases Option.some.inj matched
              rfl
            · contradiction
          · contradiction
      | _ => simp [matchLeaf?] at matched

mutual

/-- Leaf abstraction preserves denotation under its intrinsic site predicate. -/
theorem abstractLeaf_denotes
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (body : Region definitions context) :
    denoteRegion pre definitionEnv env body ↔
      (abstractLeaf kind body).denote pre definitionEnv env
        (kind.sourceSite pre definitionEnv) := by
  cases body with
  | mk items =>
      exact abstractLeafItems_denotes kind pre definitionEnv env items

private theorem abstractLeafItems_denotes
    (kind : LeafKind definitions sourceArguments)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (items : ItemSeq definitions context) :
    denoteItemSeq pre definitionEnv env items ↔
      (abstractLeafItems kind items).denote pre definitionEnv env
        (kind.sourceSite pre definitionEnv) := by
  cases items with
  | nil =>
      simp only [denoteItemSeq, abstractLeafItems,
        UniformIntrinsicRegion.denote,
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote]
      constructor
      · intro _
        refine ⟨True.intro, ?_⟩
        intro value member
        simp at member
      · intro _
        trivial
  | cons item tail =>
      have tailLaw :=
        abstractLeafItems_denotes kind pre definitionEnv env tail
      cases matched : matchLeaf? kind item with
      | some values =>
          have itemLaw :=
            matchLeaf_denotes kind pre definitionEnv env item values matched
          rw [abstractLeafItems_cons_some kind item tail values matched]
          rw [denoteItemSeq, prependHole_denotes]
          exact and_congr itemLaw tailLaw
      | none =>
          cases item with
          | atom head values =>
              rw [abstractLeafItems_cons_atom kind head values tail matched]
              rw [denoteItemSeq, prependOrdinary_denotes]
              exact and_congr Iff.rfl tailLaw
          | named definition values =>
              rw [abstractLeafItems_cons_named kind definition values tail
                matched]
              rw [denoteItemSeq, prependOrdinary_denotes]
              exact and_congr Iff.rfl tailLaw
          | identity signature ports atLeastTwo =>
              rw [abstractLeafItems_cons_identity kind signature ports
                atLeastTwo tail matched]
              rw [denoteItemSeq, prependOrdinary_denotes]
              exact and_congr Iff.rfl tailLaw
          | cut body =>
              have bodyLaw :=
                abstractLeaf_denotes kind pre definitionEnv env body
              rw [abstractLeafItems_cons_cut kind body tail]
              rw [denoteItemSeq, prependOrdinary_denotes]
              exact and_congr (not_congr bodyLaw) tailLaw
          | bind signature body =>
              have bodyLaw :
                  ∀ value : pre.Domain signature,
                    denoteRegion pre definitionEnv (env.extend value) body ↔
                      (abstractLeaf kind body).denote pre definitionEnv
                        (env.extend value)
                        (kind.sourceSite pre definitionEnv) := by
                intro value
                exact abstractLeaf_denotes kind pre definitionEnv
                  (env.extend value) body
              rw [abstractLeafItems_cons_bind kind signature body tail]
              rw [denoteItemSeq, prependOrdinary_denotes]
              exact and_congr (exists_congr bodyLaw) tailLaw

end

namespace LeafResult

/-- Independently erase both rewritten sides to one checked retained core. -/
def checkCommonCore
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ConcreteWirePrimitive.LeafResult source wire) :
    Option
      (WirePrimitive.ConcreteFactorization.CommonCoreReceipt
        source result.checked) :=
  WirePrimitive.ConcreteFactorization.checkCommonCore source result.checked
    [] result.sourceRemovedNodes result.sourceRemovedWires
    [] result.targetRemovedNodes result.targetRemovedWires

end LeafResult

private def sourceSideAligned
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceIds : List source.val.WireId)
    (targetIds : List target.val.WireId)
    (head : source.val.WireId) : Bool :=
  sourceIds.all fun candidate =>
    if candidate = head then true
    else if retained :
        candidate ∈
          ConcreteWireQuantifier.Internal.retainedWires source
            core.sourceRemovedWires then
      decide (core.forwardRetainedWire candidate retained ∈ targetIds)
    else false

/--
Every visible source wire except the consumed relation is transported into
the target context through the independently checked common core.
-/
structure RemovedHeadAlignment
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val)
    (sourceHead : source.val.WireId) : Type where
  sourceHeadRemoved : sourceHead ∈ core.sourceRemovedWires
  sourceRetained :
    ∀ candidate,
      candidate ∈ sourceContext.ids →
      candidate ≠ sourceHead →
      candidate ∈
        ConcreteWireQuantifier.Internal.retainedWires source
          core.sourceRemovedWires
  sourceVisible :
    ∀ candidate member different,
      core.forwardRetainedWire candidate
          (sourceRetained candidate member different) ∈
        targetContext.ids

def checkRemovedHeadAlignment
    {source target : CheckedDiagram definitions}
    (core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext target.val)
    (sourceHead : source.val.WireId)
    (sourceHeadRemoved : sourceHead ∈ core.sourceRemovedWires) :
    Option
      (RemovedHeadAlignment core sourceContext targetContext sourceHead) := by
  if accepted :
      sourceSideAligned core sourceContext.ids targetContext.ids
        sourceHead = true then
    unfold sourceSideAligned at accepted
    let retainedProof :
        ∀ candidate,
          candidate ∈ sourceContext.ids →
          candidate ≠ sourceHead →
          candidate ∈
            ConcreteWireQuantifier.Internal.retainedWires source
              core.sourceRemovedWires := by
      intro candidate member different
      have site := (List.all_eq_true.mp accepted) candidate member
      split at site
      · rename_i same
        exact (different same).elim
      · split at site
        · rename_i retained
          exact retained
        · simp at site
    let visibleProof :
        ∀ candidate member different,
          core.forwardRetainedWire candidate
              (retainedProof candidate member different) ∈
            targetContext.ids := by
      intro candidate member different
      have site := (List.all_eq_true.mp accepted) candidate member
      split at site
      · rename_i same
        exact (different same).elim
      · split at site
        · rename_i retained
          have proofExact :
              retainedProof candidate member different = retained :=
            Subsingleton.elim _ _
          rw [proofExact]
          exact of_decide_eq_true site
        · simp at site
    exact some
      ⟨sourceHeadRemoved, retainedProof, visibleProof⟩
  else
    exact none

namespace RemovedHeadAlignment

def sourceFallback
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    (alignment :
      RemovedHeadAlignment core sourceContext targetContext sourceHead)
    {signature : Sig}
    (value : Var sourceContext.sigs signature)
    (different :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          value ≠
        sourceHead) :
    Var targetContext.sigs signature :=
  let candidate :=
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
      value
  let member :=
    InsertionCompilation.NaturalityInternal.origin_member source.val
      sourceContext.ids value
  let retained := alignment.sourceRetained candidate member different
  let mapped := core.forwardRetainedWire candidate retained
  let visible := alignment.sourceVisible candidate member different
  let signatureExact :
      (target.val.wires mapped).sig = signature :=
    (core.forwardRetainedWire_signature candidate retained).trans
      (ConcreteElaboration.WireContext.origin_signature source.val
        sourceContext.ids value)
  InsertionCompilation.NaturalityInternal.castVar signatureExact
    (InsertionCompilation.NaturalityInternal.varForMember target.val
      targetContext.ids mapped visible)

def sourceRenaming
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    (alignment :
      RemovedHeadAlignment core sourceContext targetContext sourceHead)
    {headSignature : Sig}
    (headExact : (source.val.wires sourceHead).sig = headSignature) :
    WireRenaming sourceContext.sigs
      (headSignature :: targetContext.sigs) :=
  fun {signature} value =>
    let candidate :=
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        value
    if same : candidate = sourceHead then
      let signatureExact : signature = headSignature := by
        have originExact :=
          ConcreteElaboration.WireContext.origin_signature source.val
            sourceContext.ids value
        change (source.val.wires candidate).sig = signature at originExact
        rw [same, headExact] at originExact
        exact originExact.symm
      signatureExact.symm ▸
        (.here : Var (headSignature :: targetContext.sigs) headSignature)
    else
      .there (alignment.sourceFallback value same)

theorem sourceRenaming_head
    {source target : CheckedDiagram definitions}
    {core :
      WirePrimitive.ConcreteFactorization.CommonCoreReceipt source target}
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext : ConcreteElaboration.WireContext target.val}
    {sourceHead : source.val.WireId}
    (alignment :
      RemovedHeadAlignment core sourceContext targetContext sourceHead)
    {headSignature : Sig}
    (headExact : (source.val.wires sourceHead).sig = headSignature)
    (head : Var sourceContext.sigs headSignature)
    (origin :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          head =
        sourceHead) :
    alignment.sourceRenaming headExact head = .here := by
  simp [sourceRenaming, origin]

end RemovedHeadAlignment

private def weakenHead :
    WireRenaming context (signature :: context) :=
  fun {_} value => .there value

/--
Complete checked structural factorization for a relation-to-leaf rewrite.
The source relation is removed; every other constructor and wire is checked
against the target before the intrinsic leaf law is admitted.
-/
structure LeafFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ConcreteWirePrimitive.LeafResult source wire)
    (sourceArguments : List Sig)
    (kind : LeafKind definitions sourceArguments) where
  commonCore :
    WirePrimitive.ConcreteFactorization.CommonCoreReceipt source
      result.checked
  private source_removed_exact :
    commonCore.sourceRemovedWires = result.sourceRemovedWires
  sourceScope :
    SiteCompilation source
      (source.val.wires wire).scope
  targetScope :
    SiteCompilation result.checked result.targetScope
  context :
    ContentAlignment.SiteContextFactorization
      sourceScope targetScope
  alignment :
    RemovedHeadAlignment commonCore sourceScope.frame.visible
      targetScope.frame.visible wire
  sourceHead :
    Var sourceScope.frame.visible.sigs (.rel sourceArguments)
  sourceHead_origin :
    ConcreteElaboration.WireContext.origin source.val
      sourceScope.frame.visible.ids sourceHead = wire
  private source_signature :
    (source.val.wires wire).sig = .rel sourceArguments
  sourceOuter :
    ContentAlignment.SuffixAgreement context.siteOuter
      sourceScope.frame.visible.sigs
      ((.rel sourceArguments) :: targetScope.frame.visible.sigs)
      context.sourceOuterEmbedding
      (fun {_} value => .there (context.targetOuterEmbedding value))
      (alignment.sourceRenaming source_signature)
  private accepted :
    ArgumentsSemantics.checkPairedArgumentShape
      TypedArguments.sameVars
      (UniformIntrinsicRegion.abstractApplied
        (.here :
          Var
            ((.rel sourceArguments) ::
              targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        (sourceScope.frame.siteBody.renameWires
          (alignment.sourceRenaming source_signature)))
      (abstractLeaf kind
        (targetScope.frame.siteBody.renameWires
          (weakenHead (signature := .rel sourceArguments)))) =
      true

theorem LeafFactorization.sourceSignature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ConcreteWirePrimitive.LeafResult source wire}
    {sourceArguments : List Sig}
    {kind : LeafKind definitions sourceArguments}
    (factorization :
      LeafFactorization result sourceArguments kind) :
    (source.val.wires wire).sig = .rel sourceArguments :=
  factorization.source_signature

def checkLeafFactorization
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ConcreteWirePrimitive.LeafResult source wire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (kind : LeafKind definitions sourceArguments) :
    Option (LeafFactorization result sourceArguments kind) := do
  let commonCore ← LeavesSemantics.LeafResult.checkCommonCore result
  if removalsExact :
      commonCore.sourceRemovedWires = result.sourceRemovedWires then
    let sourceScope ←
      compileSite? source
        (source.val.wires wire).scope
    let targetScope ←
      compileSite? result.checked result.targetScope
    let context ←
      ContentAlignment.checkSiteContextFactorization
        sourceScope targetScope
    have sourceHeadRemoved :
        wire ∈ commonCore.sourceRemovedWires := by
      rw [removalsExact]
      simp [ConcreteWirePrimitive.LeafResult.sourceRemovedWires]
    let alignment ←
      checkRemovedHeadAlignment commonCore sourceScope.frame.visible
        targetScope.frame.visible wire sourceHeadRemoved
    let sourceMember :=
      sourceScope.visible_of_encloses wire
        (ConcreteDiagram.encloses_refl source.val
          (source.val.wires wire).scope)
    let sourceHead :
        Var sourceScope.frame.visible.sigs (.rel sourceArguments) :=
      InsertionCompilation.NaturalityInternal.castVar sourceSignature
        (InsertionCompilation.NaturalityInternal.varForMember source.val
          sourceScope.frame.visible.ids wire sourceMember)
    have sourceHeadOrigin :
        ConcreteElaboration.WireContext.origin source.val
            sourceScope.frame.visible.ids sourceHead = wire :=
      (InsertionCompilation.NaturalityInternal.origin_castVar source.val
        sourceScope.frame.visible.ids _ _).trans
        (InsertionCompilation.NaturalityInternal.varForMember_origin
          source.val sourceScope.frame.visible.ids wire sourceMember)
    let sourceOuter ←
      ContentAlignment.checkSuffixAgreement
        context.siteOuter context.sourceOuterEmbedding
        (fun {_} value => .there (context.targetOuterEmbedding value))
        (alignment.sourceRenaming sourceSignature)
    if accepted :
        ArgumentsSemantics.checkPairedArgumentShape
          TypedArguments.sameVars
          (UniformIntrinsicRegion.abstractApplied
            (.here :
              Var
                ((.rel sourceArguments) ::
                  targetScope.frame.visible.sigs)
                (.rel sourceArguments))
            (sourceScope.frame.siteBody.renameWires
              (alignment.sourceRenaming sourceSignature)))
          (abstractLeaf kind
            (targetScope.frame.siteBody.renameWires
              (weakenHead (signature := .rel sourceArguments)))) =
        true then
      pure
        ⟨commonCore, removalsExact, sourceScope, targetScope, context,
          alignment, sourceHead, sourceHeadOrigin, sourceSignature,
          sourceOuter, accepted⟩
    else none
  else none

namespace LeafFactorization

/-- The checked paired intrinsic shapes transport the exact leaf site law. -/
theorem denotes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ConcreteWirePrimitive.LeafResult source wire}
    {sourceArguments : List Sig}
    {kind : LeafKind definitions sourceArguments}
    (factorization :
      LeafFactorization result sourceArguments kind)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs))
    (pointwise :
      ∀ {nested : List Sig}
        (nestedEnv : Env pre nested)
        (left right : Vars nested sourceArguments),
        TypedArguments.sameVars left right = true →
          (pre.apply
              (env _ (.here :
                Var
                  ((.rel sourceArguments) ::
                    factorization.targetScope.frame.visible.sigs)
                  (.rel sourceArguments)))
              (Vars.denote nestedEnv left) ↔
            kind.sourceSite pre definitionEnv
              (Vars.denote nestedEnv right))) :
    denoteRegion pre definitionEnv
        (Env.comp env
          (factorization.alignment.sourceRenaming
            factorization.source_signature))
        factorization.sourceScope.frame.siteBody ↔
      denoteRegion pre definitionEnv
        (Env.comp env
          (weakenHead (signature := .rel sourceArguments)))
        factorization.targetScope.frame.siteBody := by
  let sourceRenaming :
      WireRenaming factorization.sourceScope.frame.visible.sigs
        ((.rel sourceArguments) ::
          factorization.targetScope.frame.visible.sigs) :=
    factorization.alignment.sourceRenaming factorization.source_signature
  let sourceBody :=
    factorization.sourceScope.frame.siteBody.renameWires sourceRenaming
  let targetBody :=
    factorization.targetScope.frame.siteBody.renameWires
      (weakenHead (signature := .rel sourceArguments))
  have paired :=
    ArgumentsSemantics.checkPairedArgumentShape_denotes
      factorization.accepted pre definitionEnv env
      (fun values =>
        pre.apply
          (env _ (.here :
            Var
              ((.rel sourceArguments) ::
                factorization.targetScope.frame.visible.sigs)
              (.rel sourceArguments)))
          values)
      (kind.sourceSite pre definitionEnv)
      (fun nestedEnv left right accepted =>
        pointwise nestedEnv left right accepted)
  exact
    (denoteRegion_renameWires pre definitionEnv env sourceRenaming
      factorization.sourceScope.frame.siteBody).symm.trans
      ((UniformIntrinsicRegion.abstractApplied_denotes pre definitionEnv
        env
        (.here :
          Var
            ((.rel sourceArguments) ::
              factorization.targetScope.frame.visible.sigs)
            (.rel sourceArguments))
        sourceBody).trans
        (paired.trans
          ((abstractLeaf_denotes kind pre definitionEnv env targetBody).symm.trans
            (denoteRegion_renameWires pre definitionEnv env
              (weakenHead (signature := .rel sourceArguments))
              factorization.targetScope.frame.siteBody))))

/--
Fullness synthesizes exactly the intrinsic leaf relation, then reconstructs
the complete source-local binder block from a target-local witness.
-/
theorem localEliminating
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ConcreteWirePrimitive.LeafResult source wire}
    {sourceArguments : List Sig}
    {kind : LeafKind definitions sourceArguments}
    (factorization :
      LeafFactorization result sourceArguments kind)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (siteEnv :
      Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (ContentAlignment.localSignatures result.checked.val
            result.targetScope)
          (.hole :
            DiagramContext definitions
              (ContentAlignment.localSignatures result.checked.val
                  result.targetScope ++ factorization.context.siteOuter)
              (ContentAlignment.localSignatures result.checked.val
                  result.targetScope ++ factorization.context.siteOuter))).fill
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
  let sourceRelation :=
    reifyRelation model (kind.sourceSite model.toPreModel definitionEnv)
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
        (fun nestedEnv left right accepted => by
          have exact :
              left = right :=
            TypedArguments.sameVars_eq_true accepted
          change
            model.toPreModel.apply sourceRelation
                (Vars.denote nestedEnv left) ↔
              kind.sourceSite model.toPreModel definitionEnv
                (Vars.denote nestedEnv right)
          rw [apply_reifyRelation, exact])).mpr
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
              result.targetScope)
            value) :=
          factorization.context.targetEnvironment_outer
            targetLocalEnv value
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

/--
The complete checked leaf implication.  Even cut depth admits target-to-source
join direction; odd cut depth reverses it.
-/
theorem directions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ConcreteWirePrimitive.LeafResult source wire}
    {sourceArguments : List Sig}
    {kind : LeafKind definitions sourceArguments}
    (factorization :
      LeafFactorization result sourceArguments kind)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
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
        factorization.localEliminating model definitionEnv siteEnv)
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

end LeafFactorization

end LeavesSemantics

end ConcreteWirePrimitive

end VisualProof
