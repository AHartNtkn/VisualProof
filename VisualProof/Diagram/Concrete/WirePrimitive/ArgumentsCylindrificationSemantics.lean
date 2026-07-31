import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsFixedSemantics

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

open WirePrimitive

/-!
## Typed insertion decomposition

Arity shift and unshift differ from ordinary argument extension and deletion:
the inserted coordinate is carried by a fresh existential wire at each acted
endpoint.  The receipt below starts by retaining both halves of that fact.
-/

namespace TypedArguments

private def splitInsertedCore
    (smaller : List Sig)
    (position : Nat)
    (fixedSignature : Sig) :
    Vars context
        (ConcreteWirePrimitive.insertAt smaller position fixedSignature) →
      Var context fixedSignature × Vars context smaller :=
  match smaller, position with
  | [], _ => fun
      | .cons fixed .nil => ⟨fixed, .nil⟩
  | _ :: _, 0 => fun
      | .cons fixed rest => ⟨fixed, rest⟩
  | signature :: rest, position + 1 => fun
      | .cons head tail =>
          let split :=
            splitInsertedCore rest position fixedSignature tail
          ⟨split.1, .cons head split.2⟩

/-- Split the checker-selected inserted coordinate from a larger tuple. -/
def InsertionEvidence.splitVars
    (evidence :
      InsertionEvidence larger smaller fixedSignature)
    (values : Vars context larger) :
    Var context fixedSignature × Vars context smaller :=
  splitInsertedCore smaller evidence.position fixedSignature
    (evidence.largerExact.symm ▸ values)

private def splitInsertedValuesCore
    (smaller : List Sig)
    (position : Nat)
    (fixedSignature : Sig) :
    PreModel.Args Domain
        (ConcreteWirePrimitive.insertAt smaller position fixedSignature) →
      Domain fixedSignature × PreModel.Args Domain smaller :=
  match smaller, position with
  | [], _ => fun
      | ⟨fixed, PUnit.unit⟩ => ⟨fixed, PUnit.unit⟩
  | _ :: _, 0 => fun
      | ⟨fixed, rest⟩ => ⟨fixed, rest⟩
  | _ :: rest, position + 1 => fun
      | ⟨head, tail⟩ =>
          let split :=
            splitInsertedValuesCore rest position fixedSignature tail
          ⟨split.1, ⟨head, split.2⟩⟩

/-- Semantic counterpart of `splitVars`. -/
def InsertionEvidence.splitValues
    (evidence :
      InsertionEvidence larger smaller fixedSignature)
    (values : PreModel.Args Domain larger) :
    Domain fixedSignature × PreModel.Args Domain smaller :=
  splitInsertedValuesCore smaller evidence.position fixedSignature
    (evidence.largerExact.symm ▸ values)

private theorem splitInsertedCore_reconstruct
    (smaller : List Sig)
    (position : Nat)
    (fixedSignature : Sig)
    (values :
      Vars context
        (ConcreteWirePrimitive.insertAt smaller position fixedSignature)) :
    let split :=
      splitInsertedCore smaller position fixedSignature values
    insertVars position split.1 split.2 = values :=
  match smaller, position, values with
  | [], 0, .cons _ .nil => rfl
  | [], _ + 1, .cons _ .nil => rfl
  | _ :: _, 0, .cons _ _ => rfl
  | _ :: rest, position + 1, .cons head tail =>
      congrArg (Vars.cons head)
        (splitInsertedCore_reconstruct rest position fixedSignature tail)

/-- Splitting and reinserting is definitionally faithful to the checked tuple. -/
theorem InsertionEvidence.reconstruct
    (evidence :
      InsertionEvidence larger smaller fixedSignature)
    (values : Vars context larger) :
    evidence.forwardVars (evidence.splitVars values).1
        (evidence.splitVars values).2 =
      values := by
  cases evidence with
  | mk position largerExact =>
      subst larger
      exact
        splitInsertedCore_reconstruct smaller position fixedSignature values

private theorem splitInsertedValuesCore_reconstruct
    (smaller : List Sig)
    (position : Nat)
    (fixedSignature : Sig)
    (values :
      PreModel.Args Domain
        (ConcreteWirePrimitive.insertAt smaller position fixedSignature)) :
    let split :=
      splitInsertedValuesCore smaller position fixedSignature values
    insertValues position split.1 split.2 = values :=
  match smaller, position, values with
  | [], 0, ⟨_, PUnit.unit⟩ => rfl
  | [], _ + 1, ⟨_, PUnit.unit⟩ => rfl
  | _ :: _, 0, ⟨_, _⟩ => rfl
  | _ :: rest, position + 1, ⟨head, tail⟩ =>
      congrArg (fun suffix => (head, suffix))
        (splitInsertedValuesCore_reconstruct rest position
          fixedSignature tail)

theorem InsertionEvidence.reconstructValues
    (evidence :
      InsertionEvidence larger smaller fixedSignature)
    (values : PreModel.Args Domain larger) :
    evidence.forwardValues (evidence.splitValues values).1
        (evidence.splitValues values).2 =
      values := by
  cases evidence with
  | mk position largerExact =>
      subst larger
      exact
        splitInsertedValuesCore_reconstruct smaller position
          fixedSignature values

private theorem splitInsertedCore_denote
    (smaller : List Sig)
    (position : Nat)
    (fixedSignature : Sig)
    (env : Env pre context)
    (values :
      Vars context
        (ConcreteWirePrimitive.insertAt smaller position fixedSignature)) :
    splitInsertedValuesCore smaller position fixedSignature
        (Vars.denote env values) =
      ⟨env _ (splitInsertedCore smaller position fixedSignature values).1,
        Vars.denote env
          (splitInsertedCore smaller position fixedSignature values).2⟩ :=
  match smaller, position, values with
  | [], 0, .cons _ .nil => rfl
  | [], _ + 1, .cons _ .nil => rfl
  | _ :: _, 0, .cons _ _ => rfl
  | _ :: rest, position + 1, .cons head tail => by
      simp only [Vars.denote_cons, splitInsertedValuesCore,
        splitInsertedCore]
      exact congrArg
        (fun split => (split.1, (env _ head, split.2)))
        (splitInsertedCore_denote rest position fixedSignature env tail)

theorem InsertionEvidence.denote_split
    (evidence :
      InsertionEvidence larger smaller fixedSignature)
    (env : Env pre context)
    (values : Vars context larger) :
    evidence.splitValues (Vars.denote env values) =
      ⟨env _ (evidence.splitVars values).1,
        Vars.denote env (evidence.splitVars values).2⟩ := by
  cases evidence with
  | mk position largerExact =>
      subst larger
      exact
        splitInsertedCore_denote smaller position fixedSignature env values

private def sameVar
    (left right : Var context signature) : Bool :=
  sameVars (.cons left .nil) (.cons right .nil)

theorem sameVar_eq_true
    {left right : Var context signature}
    (accepted : sameVar left right = true) :
    left = right := by
  have exact :
      (Vars.cons left .nil : Vars context [signature]) =
        Vars.cons right .nil :=
    sameVars_eq_true accepted
  cases exact
  rfl

end TypedArguments

/-!
## Binder-context cylindrification

Each endpoint-local wire contributes one extra binder on the larger side.
`BoundCylindrification` records the retained binders and the fresh binders
without identifying contexts by untyped positions.
-/

inductive BoundCylindrification
    (fixedSignature : Sig) :
    List Sig → List Sig → Nat → Type
  | nil :
      BoundCylindrification fixedSignature [] [] 0
  | retained
      (signature : Sig)
      (rest :
        BoundCylindrification fixedSignature smaller larger freshCount) :
      BoundCylindrification fixedSignature
        (signature :: smaller) (signature :: larger) freshCount
  | fresh
      (rest :
        BoundCylindrification fixedSignature smaller larger freshCount) :
      BoundCylindrification fixedSignature
        smaller (fixedSignature :: larger) (freshCount + 1)

namespace BoundCylindrification

/-- A binder block consisting only of fresh variables of the fixed
signature. -/
def freshSuffix (fixedSignature : Sig) :
    (count : Nat) →
      BoundCylindrification fixedSignature []
        (List.replicate count fixedSignature) count
  | 0 => .nil
  | count + 1 => .fresh (freshSuffix fixedSignature count)

/-- Retain an ordered binder block and append an ordered suffix of fresh
variables.  This is the canonical binder receipt produced by arity shift at
each concrete region. -/
def appendFresh (fixedSignature : Sig) :
    (smaller : List Sig) → (count : Nat) →
      BoundCylindrification fixedSignature smaller
        (smaller ++ List.replicate count fixedSignature) count
  | [], count => freshSuffix fixedSignature count
  | signature :: rest, count =>
      .retained signature (appendFresh fixedSignature rest count)

def count
    (_ :
      BoundCylindrification fixedSignature smaller larger freshCount) :
    Nat :=
  freshCount

/--
Enumerate every typed way the larger local binder block can arise by
inserting fresh binders of one signature into the smaller block.  Retained
and fresh binders can have the same signature, so completeness requires both
branches rather than a greedy first match.
-/
def candidates
    (fixedSignature : Sig) :
    (smaller larger : List Sig) →
      List
        (Σ freshCount,
          BoundCylindrification fixedSignature
            smaller larger freshCount)
  | [], [] => [⟨0, .nil⟩]
  | [], largerSignature :: largerRest =>
      if same : largerSignature = fixedSignature then
        by
          subst largerSignature
          exact (candidates fixedSignature [] largerRest).map fun
            | ⟨freshCount, rest⟩ => ⟨freshCount + 1, .fresh rest⟩
      else
        []
  | _ :: _, [] => []
  | smallerSignature :: smallerRest,
      largerSignature :: largerRest =>
      let retained :=
        if same : largerSignature = smallerSignature then
          by
            subst largerSignature
            exact
              (candidates fixedSignature smallerRest largerRest).map fun
                | ⟨freshCount, rest⟩ =>
                    ⟨freshCount, .retained smallerSignature rest⟩
        else
          []
      let fresh :=
        if same : largerSignature = fixedSignature then
          by
            subst largerSignature
            exact
              (candidates fixedSignature
                (smallerSignature :: smallerRest) largerRest).map fun
                | ⟨freshCount, rest⟩ =>
                    ⟨freshCount + 1, .fresh rest⟩
        else
          []
      retained ++ fresh
termination_by smaller larger => smaller.length + larger.length

theorem mem_candidates
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount) :
    ⟨freshCount, evidence⟩ ∈
      candidates fixedSignature smaller larger :=
  match evidence with
  | .nil => by simp [candidates]
  | .retained signature rest => by
      unfold candidates
      rw [dif_pos rfl]
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_map.mpr
      exact ⟨⟨_, rest⟩, mem_candidates rest, rfl⟩
  | .fresh rest => by
      cases smaller with
      | nil =>
          unfold candidates
          rw [dif_pos rfl]
          apply List.mem_map.mpr
          exact ⟨⟨_, rest⟩, mem_candidates rest, rfl⟩
      | cons signature tail =>
          unfold candidates
          rw [dif_pos rfl]
          apply List.mem_append.mpr
          apply Or.inr
          apply List.mem_map.mpr
          exact ⟨⟨_, rest⟩, mem_candidates rest, rfl⟩

def check
    (fixedSignature : Sig)
    (smaller larger : List Sig) :
    Option
      (Σ freshCount,
        BoundCylindrification fixedSignature
          smaller larger freshCount) :=
  (candidates fixedSignature smaller larger).head?

private def weakenOuter
    (rho : WireRenaming source target)
    (head : Sig) :
    WireRenaming source (head :: target) :=
  fun {_} value => .there (rho value)

/-- Embed the smaller binder context into the larger binder context. -/
def embed
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (outer : WireRenaming smallerOuter largerOuter) :
    WireRenaming (smaller ++ smallerOuter) (larger ++ largerOuter) :=
  match evidence with
  | .nil => outer
  | .retained signature rest =>
      WireRenaming.lift (rest.embed outer) signature
  | .fresh rest =>
      weakenOuter (rest.embed outer) fixedSignature

/-- The intrinsically typed variable owned by each fresh binder. -/
def freshVar
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (outer : WireRenaming smallerOuter largerOuter) :
    Fin freshCount →
      Var (larger ++ largerOuter) fixedSignature :=
  match evidence with
  | .nil => Fin.elim0
  | .retained _ rest =>
      fun index => .there (rest.freshVar outer index)
  | .fresh rest =>
      fun index =>
        Fin.cases .here
          (fun tail => .there (rest.freshVar outer tail))
          index

/-- Forget the fresh values while retaining every shared binder value. -/
def projectValues
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount) :
    ConcreteElaboration.WireValues pre larger →
      ConcreteElaboration.WireValues pre smaller :=
  match evidence with
  | .nil => fun _ => .nil
  | .retained _ rest => fun
      | .cons head tail => .cons head (rest.projectValues tail)
  | .fresh rest => fun
      | .cons _ tail => rest.projectValues tail

/-- Read every fresh value in the same order as `freshVar`. -/
def freshValues
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount) :
    ConcreteElaboration.WireValues pre larger →
      Fin freshCount → pre.Domain fixedSignature :=
  match evidence with
  | .nil => fun _ => Fin.elim0
  | .retained _ rest => fun
      | .cons _ tail => rest.freshValues tail
  | .fresh rest => fun
      | .cons head tail =>
          fun index =>
            Fin.cases head (rest.freshValues tail) index

/-- Reassemble the larger binder tuple from retained and fresh values. -/
def assembleValues
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount) :
    ConcreteElaboration.WireValues pre smaller →
      (Fin freshCount → pre.Domain fixedSignature) →
      ConcreteElaboration.WireValues pre larger :=
  match evidence with
  | .nil => fun _ _ => .nil
  | .retained _ rest =>
      fun values assignment =>
        match values with
        | .cons head tail =>
          .cons head (rest.assembleValues tail assignment)
  | .fresh rest => fun smallerValues assignment =>
      .cons (assignment 0)
        (rest.assembleValues smallerValues
          (fun index => assignment index.succ))

@[simp] theorem project_assemble
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (smallerValues : ConcreteElaboration.WireValues pre smaller)
    (assignment : Fin freshCount → pre.Domain fixedSignature) :
    evidence.projectValues
        (evidence.assembleValues smallerValues assignment) =
      smallerValues := by
  induction evidence with
  | nil =>
      cases smallerValues
      rfl
  | retained signature rest induction =>
      cases smallerValues with
      | cons head tail =>
          simp only [assembleValues, projectValues]
          exact congrArg (ConcreteElaboration.WireValues.cons head)
            (induction tail assignment)
  | fresh rest induction =>
      simp only [assembleValues, projectValues]
      exact induction smallerValues
        (fun index => assignment index.succ)

@[simp] theorem assemble_project_fresh
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (largerValues : ConcreteElaboration.WireValues pre larger) :
    evidence.assembleValues
        (evidence.projectValues largerValues)
        (evidence.freshValues largerValues) =
      largerValues := by
  induction evidence with
  | nil =>
      cases largerValues
      rfl
  | retained signature rest induction =>
      cases largerValues with
      | cons head tail =>
          simp only [projectValues, freshValues, assembleValues]
          exact congrArg (ConcreteElaboration.WireValues.cons head)
            (induction tail)
  | fresh rest induction =>
      cases largerValues with
      | cons head tail =>
          simp only [projectValues, freshValues, assembleValues,
            Fin.cases_zero, Fin.cases_succ]
          exact congrArg (ConcreteElaboration.WireValues.cons head)
            (induction tail)

private noncomputable def arbitraryFresh
    (pre : PreModel.{u})
    (fixedSignature : Sig)
    (freshCount : Nat) :
    Fin freshCount → pre.Domain fixedSignature :=
  fun _ => chooseInhabitant pre fixedSignature

theorem comp_assembled
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (pre : PreModel.{u})
    (smallerValues : ConcreteElaboration.WireValues pre smaller)
    (assignment : Fin freshCount → pre.Domain fixedSignature)
    (smallerOuterEnv : Env pre smallerOuter)
    (largerOuterEnv : Env pre largerOuter)
    (outerExact :
      Env.comp largerOuterEnv outer = smallerOuterEnv) :
    Env.comp
        (ContentShapeSemantics.extendValues
          (evidence.assembleValues smallerValues assignment) largerOuterEnv)
        (evidence.embed outer) =
      ContentShapeSemantics.extendValues
        smallerValues smallerOuterEnv := by
  induction evidence with
  | nil =>
      cases smallerValues
      simpa [embed, assembleValues,
        ContentShapeSemantics.extendValues] using outerExact
  | retained signature rest induction =>
      cases smallerValues with
      | cons head tail =>
          have tailExact := induction tail assignment
          funext currentSignature value
          cases value with
          | here => rfl
          | there value =>
              exact congrFun
                (congrFun tailExact currentSignature) value
  | fresh rest induction =>
      simp only [assembleValues,
        ContentShapeSemantics.extendValues, embed]
      change
        Env.comp
            (ContentShapeSemantics.extendValues
              (rest.assembleValues smallerValues
                (fun index => assignment index.succ))
              largerOuterEnv)
            (rest.embed outer) =
          ContentShapeSemantics.extendValues
            smallerValues smallerOuterEnv
      exact
        induction smallerValues (fun index => assignment index.succ)

theorem freshVar_assembled
    (evidence :
      BoundCylindrification fixedSignature smaller larger freshCount)
    (pre : PreModel.{u})
    (smallerValues : ConcreteElaboration.WireValues pre smaller)
    (assignment : Fin freshCount → pre.Domain fixedSignature)
    (outerEnv : Env pre largerOuter)
    (index : Fin freshCount) :
    ContentShapeSemantics.extendValues
        (evidence.assembleValues smallerValues assignment) outerEnv
        fixedSignature (evidence.freshVar outer index) =
      assignment index := by
  induction evidence with
  | nil => exact Fin.elim0 index
  | retained signature rest induction =>
      simp only [assembleValues, freshVar]
      cases smallerValues with
      | cons head tail =>
          simp only [ContentShapeSemantics.extendValues]
          exact induction tail assignment index
  | fresh rest induction =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simp only [assembleValues, freshVar, Fin.cases_succ,
          ContentShapeSemantics.extendValues]
        exact
          induction smallerValues
            (fun index => assignment index.succ) tail

end BoundCylindrification

/-!
## Intrinsic binder blocks

The concrete elaborator wraps all wires scoped at one region with the same
`bindMany` order.  This intrinsic counterpart exposes the complete block to
the cylindrification checker.
-/

def wrapArgumentBind
    (signature : Sig)
    (body :
      UniformIntrinsicRegion definitions arguments (signature :: outer)) :
    UniformIntrinsicRegion definitions arguments outer :=
  .mk
    (.cons (.bind signature body) .nil)
    ⟨[]⟩

theorem wrapArgumentBind_transport
    {left right : List Sig}
    (equality : left = right)
    (signature : Sig)
    (body :
      UniformIntrinsicRegion definitions arguments (signature :: left)) :
    equality ▸ wrapArgumentBind signature body =
      wrapArgumentBind signature
        (congrArg (List.cons signature) equality ▸ body) := by
  cases equality
  rfl

theorem transportedArgumentRegion_roundtrip
    {left right : List Sig}
    (equality : left = right)
    (items :
      UniformIntrinsicItemSeq definitions arguments right)
    (holes : List (Vars right arguments)) :
    equality ▸
        (.mk
          (equality.symm ▸ items)
          ⟨equality.symm ▸ holes⟩ :
          UniformIntrinsicRegion definitions arguments left) =
      (.mk items ⟨holes⟩ :
        UniformIntrinsicRegion definitions arguments right) := by
  cases equality
  rfl

def wrapArgumentBinds
    (bound : List Sig)
    (body :
      UniformIntrinsicRegion definitions arguments (bound ++ outer)) :
    UniformIntrinsicRegion definitions arguments outer :=
  match bound with
  | [] => body
  | signature :: rest =>
      wrapArgumentBinds rest
        (wrapArgumentBind signature body)

theorem wrapArgumentBinds_denotes
    (bound : List Sig)
    (body :
      UniformIntrinsicRegion definitions arguments (bound ++ outer))
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (outerEnv : Env pre outer)
    (site : PreModel.Args pre.Domain arguments → Prop) :
    (wrapArgumentBinds bound body).denote pre definitionEnv outerEnv site ↔
      ∃ values : ConcreteElaboration.WireValues pre bound,
        body.denote pre definitionEnv
          (ContentShapeSemantics.extendValues values outerEnv) site := by
  induction bound with
  | nil =>
      constructor
      · intro holds
        exact ⟨.nil, holds⟩
      · rintro ⟨values, holds⟩
        cases values
        exact holds
  | cons signature rest induction =>
      simp only [wrapArgumentBinds]
      rw [induction (wrapArgumentBind signature body)]
      constructor
      · rintro ⟨restValues, bodyHolds⟩
        simp only [wrapArgumentBind, UniformIntrinsicRegion.denote,
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote,
          UniformIntrinsicRegion.UniformIntrinsicItem.denote,
          List.not_mem_nil,
          false_implies, and_true] at bodyHolds
        rcases bodyHolds.1 with ⟨head, holds⟩
        exact ⟨.cons head restValues, holds⟩
      · rintro ⟨values, holds⟩
        cases values with
        | cons head restValues =>
            refine ⟨restValues, ?_⟩
            simp only [wrapArgumentBind, UniformIntrinsicRegion.denote,
              UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote,
              UniformIntrinsicRegion.UniformIntrinsicItem.denote,
              List.not_mem_nil,
              false_implies, and_true]
            exact
              ⟨⟨head, holds⟩,
                fun _ member => by simp at member⟩

theorem wrapArgumentBinds_append
    (left right : List Sig)
    (body :
      UniformIntrinsicRegion definitions arguments
        ((left ++ right) ++ outer)) :
    wrapArgumentBinds (left ++ right) body =
      wrapArgumentBinds right
        (wrapArgumentBinds left
          (List.append_assoc left right outer ▸ body)) := by
  induction left with
  | nil =>
      rfl
  | cons signature rest induction =>
      simp only [List.cons_append, wrapArgumentBinds]
      rw [induction]
      congr
      exact
        wrapArgumentBind_transport
          (List.append_assoc rest right outer) signature body

structure PeeledArgumentShape
    (shape :
      UniformIntrinsicRegion definitions arguments outer) where
  bound : List Sig
  items :
    UniformIntrinsicItemSeq definitions arguments (bound ++ outer)
  holes : List (Vars (bound ++ outer) arguments)
  exact :
    shape =
      wrapArgumentBinds bound (.mk items ⟨holes⟩)

def peelArgumentShape
    (shape :
      UniformIntrinsicRegion definitions arguments outer) :
    PeeledArgumentShape shape :=
  match shape with
  | .mk (.cons (.bind signature body) .nil) ⟨[]⟩ => by
      let peeled := peelArgumentShape body
      let contextExact :
          peeled.bound ++ signature :: outer =
            (peeled.bound ++ [signature]) ++ outer :=
        (List.append_assoc peeled.bound [signature] outer).symm
      let items :
          UniformIntrinsicItemSeq definitions arguments
            ((peeled.bound ++ [signature]) ++ outer) :=
        contextExact ▸ peeled.items
      let holes :
          List
            (Vars ((peeled.bound ++ [signature]) ++ outer) arguments) :=
        contextExact ▸ peeled.holes
      refine
        { bound := peeled.bound ++ [signature]
          items := items
          holes := holes
          exact := ?_ }
      let associated :=
        List.append_assoc peeled.bound [signature] outer
      have baseExact :
          associated ▸
              (.mk items ⟨holes⟩ :
                UniformIntrinsicRegion definitions arguments
                  ((peeled.bound ++ [signature]) ++ outer)) =
            (.mk peeled.items ⟨peeled.holes⟩ :
              UniformIntrinsicRegion definitions arguments
                (peeled.bound ++ signature :: outer)) := by
        exact
          transportedArgumentRegion_roundtrip associated
            peeled.items peeled.holes
      calc
        wrapArgumentBind signature body =
            wrapArgumentBind signature
              (wrapArgumentBinds peeled.bound
                (.mk peeled.items ⟨peeled.holes⟩)) :=
          congrArg (wrapArgumentBind signature) peeled.exact
        _ =
            wrapArgumentBinds [signature]
              (wrapArgumentBinds peeled.bound
                (.mk peeled.items ⟨peeled.holes⟩)) := rfl
        _ =
            wrapArgumentBinds [signature]
              (wrapArgumentBinds peeled.bound
                (associated ▸ (.mk items ⟨holes⟩))) := by
          rw [baseExact]
          rfl
        _ =
            wrapArgumentBinds (peeled.bound ++ [signature])
              (.mk items ⟨holes⟩) :=
          (wrapArgumentBinds_append peeled.bound [signature]
            (.mk items ⟨holes⟩)).symm
  | .mk items ⟨holes⟩ =>
      { bound := []
        items := items
        holes := holes
        exact := rfl }

/-!
## Recursive endpoint-local shape certificate

At each concrete region the certificate peels the complete local binder
blocks, relates every retained ordinary item, and pairs every fresh binder
with exactly one acted hole.  Fresh binders are neither shared nor permitted
to escape into nested regions.
-/

private def checkFinBijection (mapping : Fin count → Fin count) : Bool :=
  ((Data.Finite.allFin count).all fun left =>
    (Data.Finite.allFin count).all fun right =>
      ! (mapping left == mapping right) || (left == right)) &&
  ((Data.Finite.allFin count).all fun target =>
    (Data.Finite.allFin count).any fun source =>
      mapping source == target)

private theorem checkFinBijection_eq_true
    (mapping : Fin count → Fin count)
    (accepted : checkFinBijection mapping = true) :
    Function.Injective mapping ∧ Function.Surjective mapping := by
  simp only [checkFinBijection, Bool.and_eq_true] at accepted
  constructor
  · intro left right same
    have checked :=
      (List.all_eq_true.mp
        (List.all_eq_true.mp accepted.1 left
          (Data.Finite.mem_allFin left)) right
        (Data.Finite.mem_allFin right))
    rw [Bool.or_eq_true] at checked
    rcases checked with different | equal
    · have equalMapping : (mapping left == mapping right) = true :=
        beq_iff_eq.mpr same
      rw [equalMapping] at different
      contradiction
    · exact beq_iff_eq.mp equal
  · intro target
    have checked :=
      List.all_eq_true.mp accepted.2 target
        (Data.Finite.mem_allFin target)
    obtain ⟨source, _member, equal⟩ := List.any_eq_true.mp checked
    exact ⟨source, beq_iff_eq.mp equal⟩

private theorem checkFinBijection_complete
    (mapping : Fin count → Fin count)
    (injective : Function.Injective mapping)
    (surjective : Function.Surjective mapping) :
    checkFinBijection mapping = true := by
  rw [checkFinBijection, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro left _
    apply List.all_eq_true.mpr
    intro right _
    rw [Bool.or_eq_true]
    by_cases same : mapping left = mapping right
    · exact Or.inr (beq_iff_eq.mpr (injective same))
    · exact Or.inl (by simp [same])
  · apply List.all_eq_true.mpr
    intro target _
    obtain ⟨source, same⟩ := surjective target
    apply List.any_eq_true.mpr
    exact ⟨source, Data.Finite.mem_allFin source, beq_iff_eq.mpr same⟩

structure CylindricalHoles
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)) : Type where
  smaller_length : smaller.length = freshCount
  larger_length : larger.length = freshCount
  sourceIndex : Fin freshCount → Fin freshCount
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective : Function.Surjective sourceIndex
  freshIndex : Fin freshCount → Fin freshCount
  freshIndex_injective : Function.Injective freshIndex
  freshIndex_surjective : Function.Surjective freshIndex
  inserted_exact :
    ∀ index : Fin freshCount,
      (insertion.splitVars
        (larger.get (Fin.cast larger_length.symm index))).1 =
          bounds.freshVar outer (freshIndex index)
  retained_exact :
    ∀ index : Fin freshCount,
      (insertion.splitVars
        (larger.get (Fin.cast larger_length.symm index))).2 =
          Vars.rename (bounds.embed outer)
            (smaller.get
              (Fin.cast smaller_length.symm (sourceIndex index)))

private def checkSourceIndex
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount) : Bool :=
  checkFinBijection mapping &&
    decide
      (∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).2 =
            Vars.rename (bounds.embed outer)
              (smaller.get
                (Fin.cast smallerLength.symm (mapping index))))

private def checkFreshIndex
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount) : Bool :=
  checkFinBijection mapping &&
    decide
      (∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).1 =
            bounds.freshVar outer (mapping index))

private def findSourceIndex?
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount) :
    Option (Fin freshCount → Fin freshCount) :=
  (Data.Finite.enumerateFinFunctions freshCount freshCount).find? fun mapping =>
    checkSourceIndex insertion bounds outer smaller larger
      smallerLength largerLength mapping

private def findFreshIndex?
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (largerLength : larger.length = freshCount) :
    Option (Fin freshCount → Fin freshCount) :=
  (Data.Finite.enumerateFinFunctions freshCount freshCount).find? fun mapping =>
    checkFreshIndex insertion bounds outer larger largerLength mapping

def checkCylindricalHoles
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)) : Bool :=
  if smallerLength : smaller.length = freshCount then
    if largerLength : larger.length = freshCount then
      (findSourceIndex? insertion bounds outer smaller larger
          smallerLength largerLength).isSome &&
        (findFreshIndex? insertion bounds outer larger
          largerLength).isSome
    else
      false
  else
    false

private theorem checkSourceIndex_eq_true
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount)
    (accepted :
      checkSourceIndex insertion bounds outer smaller larger
        smallerLength largerLength mapping = true) :
    Function.Injective mapping ∧ Function.Surjective mapping ∧
      ∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).2 =
            Vars.rename (bounds.embed outer)
              (smaller.get
                (Fin.cast smallerLength.symm (mapping index))) := by
  rw [checkSourceIndex, Bool.and_eq_true] at accepted
  exact
    ⟨(checkFinBijection_eq_true mapping accepted.1).1,
      (checkFinBijection_eq_true mapping accepted.1).2,
      of_decide_eq_true accepted.2⟩

private theorem checkSourceIndex_complete
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount)
    (injective : Function.Injective mapping)
    (surjective : Function.Surjective mapping)
    (exact :
      ∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).2 =
            Vars.rename (bounds.embed outer)
              (smaller.get
                (Fin.cast smallerLength.symm (mapping index)))) :
    checkSourceIndex insertion bounds outer smaller larger
      smallerLength largerLength mapping = true := by
  rw [checkSourceIndex, Bool.and_eq_true]
  exact
    ⟨checkFinBijection_complete mapping injective surjective,
      decide_eq_true exact⟩

private theorem checkFreshIndex_eq_true
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount)
    (accepted :
      checkFreshIndex insertion bounds outer larger largerLength mapping =
        true) :
    Function.Injective mapping ∧ Function.Surjective mapping ∧
      ∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).1 =
            bounds.freshVar outer (mapping index) := by
  rw [checkFreshIndex, Bool.and_eq_true] at accepted
  exact
    ⟨(checkFinBijection_eq_true mapping accepted.1).1,
      (checkFinBijection_eq_true mapping accepted.1).2,
      of_decide_eq_true accepted.2⟩

private theorem checkFreshIndex_complete
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (largerLength : larger.length = freshCount)
    (mapping : Fin freshCount → Fin freshCount)
    (injective : Function.Injective mapping)
    (surjective : Function.Surjective mapping)
    (exact :
      ∀ index : Fin freshCount,
        (insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index))).1 =
            bounds.freshVar outer (mapping index)) :
    checkFreshIndex insertion bounds outer larger largerLength mapping =
      true := by
  rw [checkFreshIndex, Bool.and_eq_true]
  exact
    ⟨checkFinBijection_complete mapping injective surjective,
      decide_eq_true exact⟩

theorem checkCylindricalHoles_complete
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger) :
    checkCylindricalHoles insertion bounds outer smaller larger =
      true := by
  unfold checkCylindricalHoles
  rw [dif_pos holes.smaller_length, dif_pos holes.larger_length,
    Bool.and_eq_true]
  constructor
  · apply List.find?_isSome.mpr
    refine ⟨holes.sourceIndex,
      Data.Finite.enumerateFinFunctions_complete _ _ holes.sourceIndex, ?_⟩
    apply checkSourceIndex_complete insertion bounds outer smaller larger
      holes.smaller_length holes.larger_length holes.sourceIndex
      holes.sourceIndex_injective holes.sourceIndex_surjective
    intro index
    simpa only [Subsingleton.elim _ holes.smaller_length,
      Subsingleton.elim _ holes.larger_length] using
        holes.retained_exact index
  · apply List.find?_isSome.mpr
    refine ⟨holes.freshIndex,
      Data.Finite.enumerateFinFunctions_complete _ _ holes.freshIndex, ?_⟩
    apply checkFreshIndex_complete insertion bounds outer larger
      holes.larger_length holes.freshIndex holes.freshIndex_injective
      holes.freshIndex_surjective
    intro index
    simpa only [Subsingleton.elim _ holes.larger_length] using
      holes.inserted_exact index

def checkCylindricalHoles_eq_true
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (accepted :
      checkCylindricalHoles insertion bounds outer smaller larger =
        true) :
    CylindricalHoles insertion bounds outer smaller larger := by
  unfold checkCylindricalHoles at accepted
  split at accepted
  next smallerLength =>
    split at accepted
    next largerLength =>
      rw [Bool.and_eq_true] at accepted
      cases sourceFound :
          findSourceIndex? insertion bounds outer smaller larger
            smallerLength largerLength with
      | none =>
          simp [sourceFound] at accepted
      | some sourceIndex =>
          cases freshFound :
              findFreshIndex? insertion bounds outer larger largerLength with
          | none =>
              simp [freshFound] at accepted
          | some freshIndex =>
              have sourceAccepted :
                  checkSourceIndex insertion bounds outer smaller larger
                      smallerLength largerLength sourceIndex = true := by
                unfold findSourceIndex? at sourceFound
                exact List.find?_some sourceFound
              have freshAccepted :
                  checkFreshIndex insertion bounds outer larger largerLength
                      freshIndex = true := by
                unfold findFreshIndex? at freshFound
                exact List.find?_some freshFound
              obtain ⟨sourceInjective, sourceSurjective, retainedExact⟩ :=
                checkSourceIndex_eq_true insertion bounds outer smaller larger
                  smallerLength largerLength sourceIndex sourceAccepted
              obtain ⟨freshInjective, freshSurjective, insertedExact⟩ :=
                checkFreshIndex_eq_true insertion bounds outer larger
                  largerLength freshIndex freshAccepted
              exact
                { smaller_length := smallerLength
                  larger_length := largerLength
                  sourceIndex := sourceIndex
                  sourceIndex_injective := sourceInjective
                  sourceIndex_surjective := sourceSurjective
                  freshIndex := freshIndex
                  freshIndex_injective := freshInjective
                  freshIndex_surjective := freshSurjective
                  inserted_exact := insertedExact
                  retained_exact := retainedExact }
    next => contradiction
  next => contradiction
def cylindricalLift
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (smallerSite :
      PreModel.Args Domain smallerArguments → Prop)
    (largerValues : PreModel.Args Domain largerArguments) : Prop :=
  smallerSite (insertion.splitValues largerValues).2

def cylindricalProject
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (largerSite :
      PreModel.Args Domain largerArguments → Prop)
    (smallerValues : PreModel.Args Domain smallerArguments) : Prop :=
  ∃ fixed : Domain fixedSignature,
    largerSite (insertion.forwardValues fixed smallerValues)

namespace CylindricalHoles

noncomputable def targetForSource
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (source : Fin freshCount) : Fin freshCount :=
  Classical.choose (holes.sourceIndex_surjective source)

theorem sourceIndex_targetForSource
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (source : Fin freshCount) :
    holes.sourceIndex (holes.targetForSource source) = source :=
  Classical.choose_spec (holes.sourceIndex_surjective source)

noncomputable def targetForFresh
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (fresh : Fin freshCount) : Fin freshCount :=
  Classical.choose (holes.freshIndex_surjective fresh)

theorem freshIndex_targetForFresh
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (fresh : Fin freshCount) :
    holes.freshIndex (holes.targetForFresh fresh) = fresh :=
  Classical.choose_spec (holes.freshIndex_surjective fresh)

theorem forward_pointwise
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerEnv : Env pre (largerBound ++ largerOuter))
    (envExact :
      Env.comp largerEnv (bounds.embed outer) = smallerEnv)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop)
    (index : Fin freshCount) :
    cylindricalLift insertion smallerSite
        (Vars.denote largerEnv
          (larger.get (Fin.cast holes.larger_length.symm index))) ↔
      smallerSite
        (Vars.denote smallerEnv
          (smaller.get
            (Fin.cast holes.smaller_length.symm
              (holes.sourceIndex index)))) := by
  unfold cylindricalLift
  rw [insertion.denote_split]
  rw [holes.retained_exact index]
  rw [Vars.denote_rename]
  rw [envExact]

theorem forward
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerEnv : Env pre (largerBound ++ largerOuter))
    (envExact :
      Env.comp largerEnv (bounds.embed outer) = smallerEnv)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop) :
    (∀ value, value ∈ larger →
        cylindricalLift insertion smallerSite
          (Vars.denote largerEnv value)) ↔
      (∀ value, value ∈ smaller →
        smallerSite (Vars.denote smallerEnv value)) := by
  constructor
  · intro largerHolds value member
    obtain ⟨position, valueExact⟩ := List.get_of_mem member
    subst value
    let sourceIndex : Fin freshCount :=
      Fin.cast holes.smaller_length position
    let targetIndex := holes.targetForSource sourceIndex
    have atLarger :=
      largerHolds
        (larger.get (Fin.cast holes.larger_length.symm targetIndex))
        (List.get_mem larger _)
    have result :=
      (holes.forward_pointwise pre smallerEnv largerEnv envExact
        smallerSite targetIndex).mp atLarger
    have mapped := holes.sourceIndex_targetForSource sourceIndex
    have positionExact :
        Fin.cast holes.smaller_length.symm
            (holes.sourceIndex targetIndex) =
          position := by
      rw [show targetIndex = holes.targetForSource sourceIndex by rfl,
        mapped]
      simp [sourceIndex]
    rw [positionExact] at result
    exact result
  · intro smallerHolds value member
    obtain ⟨position, valueExact⟩ := List.get_of_mem member
    subst value
    let targetIndex : Fin freshCount :=
      Fin.cast holes.larger_length position
    have atSmaller :=
      smallerHolds
        (smaller.get
          (Fin.cast holes.smaller_length.symm
            (holes.sourceIndex targetIndex)))
        (List.get_mem smaller _)
    have result :=
      (holes.forward_pointwise pre smallerEnv largerEnv envExact
        smallerSite targetIndex).mpr atSmaller
    simpa [targetIndex] using result

theorem backward_pointwise
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerEnv : Env pre (largerBound ++ largerOuter))
    (envExact :
      Env.comp largerEnv (bounds.embed outer) = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (index : Fin freshCount) :
    largerSite
        (Vars.denote largerEnv
          (larger.get (Fin.cast holes.larger_length.symm index))) →
      cylindricalProject insertion largerSite
        (Vars.denote smallerEnv
          (smaller.get
            (Fin.cast holes.smaller_length.symm
              (holes.sourceIndex index)))) := by
  intro holds
  let largerVars :=
    larger.get (Fin.cast holes.larger_length.symm index)
  let smallerVars :=
    smaller.get
      (Fin.cast holes.smaller_length.symm (holes.sourceIndex index))
  let split := insertion.splitVars largerVars
  refine ⟨largerEnv _ split.1, ?_⟩
  have reconstructed := insertion.reconstruct largerVars
  have retained := holes.retained_exact index
  change split.2 = Vars.rename (bounds.embed outer) smallerVars at retained
  rw [retained] at reconstructed
  have denoted := congrArg (Vars.denote largerEnv) reconstructed
  rw [insertion.denote_forward, Vars.denote_rename, envExact] at denoted
  change
    largerSite
      (insertion.forwardValues (largerEnv _ split.1)
        (Vars.denote smallerEnv smallerVars))
  rw [denoted]
  exact holds

theorem backward_from_larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerEnv : Env pre (largerBound ++ largerOuter))
    (envExact :
      Env.comp largerEnv (bounds.embed outer) = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (largerHolds :
      ∀ value, value ∈ larger →
        largerSite (Vars.denote largerEnv value)) :
    ∀ value, value ∈ smaller →
      cylindricalProject insertion largerSite
        (Vars.denote smallerEnv value) := by
  intro value member
  obtain ⟨position, valueExact⟩ := List.get_of_mem member
  subst value
  let sourceIndex : Fin freshCount :=
    Fin.cast holes.smaller_length position
  let targetIndex := holes.targetForSource sourceIndex
  have atLarger :=
    largerHolds
      (larger.get (Fin.cast holes.larger_length.symm targetIndex))
      (List.get_mem larger _)
  have result :=
    holes.backward_pointwise pre smallerEnv largerEnv envExact
      largerSite targetIndex atLarger
  have mapped := holes.sourceIndex_targetForSource sourceIndex
  have positionExact :
      Fin.cast holes.smaller_length.symm
          (holes.sourceIndex targetIndex) =
        position := by
    rw [show targetIndex = holes.targetForSource sourceIndex by rfl,
      mapped]
    simp [sourceIndex]
  rw [positionExact] at result
  exact result

noncomputable def backwardAssignment
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerHolds :
      ∀ value, value ∈ smaller →
        cylindricalProject insertion largerSite
          (Vars.denote smallerEnv value)) :
    Fin freshCount → pre.Domain fixedSignature :=
  fun fresh =>
    let target := holes.targetForFresh fresh
    Classical.choose <| by
      have holds :=
        smallerHolds
          (smaller.get
            (Fin.cast holes.smaller_length.symm
              (holes.sourceIndex target)))
          (List.get_mem smaller _)
      exact holds

theorem backwardAssignment_spec
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerHolds :
      ∀ value, value ∈ smaller →
        cylindricalProject insertion largerSite
          (Vars.denote smallerEnv value))
    (fresh : Fin freshCount) :
    largerSite
      (insertion.forwardValues
        (holes.backwardAssignment pre smallerEnv largerSite smallerHolds
          fresh)
        (Vars.denote smallerEnv
          (smaller.get
            (Fin.cast holes.smaller_length.symm
              (holes.sourceIndex (holes.targetForFresh fresh)))))) := by
  exact Classical.choose_spec <| by
    have holds :=
      smallerHolds
        (smaller.get
          (Fin.cast holes.smaller_length.symm
            (holes.sourceIndex (holes.targetForFresh fresh))))
        (List.get_mem smaller _)
    exact holds

theorem backward_to_larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount}
    {outer : WireRenaming smallerOuter largerOuter}
    {smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes :
      CylindricalHoles insertion bounds outer smaller larger)
    (pre : PreModel.{u})
    (smallerEnv : Env pre (smallerBound ++ smallerOuter))
    (largerEnv : Env pre (largerBound ++ largerOuter))
    (envExact :
      Env.comp largerEnv (bounds.embed outer) = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop)
    (smallerHolds :
      ∀ value, value ∈ smaller →
        cylindricalProject insertion largerSite
          (Vars.denote smallerEnv value))
    (freshExact :
      ∀ index : Fin freshCount,
        largerEnv _ (bounds.freshVar outer index) =
          holes.backwardAssignment pre smallerEnv largerSite
            smallerHolds index) :
    ∀ value, value ∈ larger →
      largerSite (Vars.denote largerEnv value) := by
  intro value member
  obtain ⟨position, valueExact⟩ := List.get_of_mem member
  subst value
  let targetIndex : Fin freshCount :=
    Fin.cast holes.larger_length position
  let freshIndex := holes.freshIndex targetIndex
  let largerVars :=
    larger.get (Fin.cast holes.larger_length.symm targetIndex)
  let smallerVars :=
    smaller.get
      (Fin.cast holes.smaller_length.symm (holes.sourceIndex targetIndex))
  let split := insertion.splitVars largerVars
  have reconstructed := insertion.reconstruct largerVars
  have inserted := holes.inserted_exact targetIndex
  have retained := holes.retained_exact targetIndex
  change split.1 = bounds.freshVar outer freshIndex at inserted
  change split.2 = Vars.rename (bounds.embed outer) smallerVars at retained
  rw [inserted, retained] at reconstructed
  have denoted := congrArg (Vars.denote largerEnv) reconstructed
  rw [insertion.denote_forward, Vars.denote_rename, envExact,
    freshExact freshIndex] at denoted
  have inverseTarget : holes.targetForFresh freshIndex = targetIndex := by
    apply holes.freshIndex_injective
    exact holes.freshIndex_targetForFresh freshIndex
  have chosen :=
    holes.backwardAssignment_spec pre smallerEnv largerSite
      smallerHolds freshIndex
  rw [inverseTarget] at chosen
  have result : largerSite (Vars.denote largerEnv largerVars) := by
    rw [← denoted]
    exact chosen
  simpa [largerVars, targetIndex] using result

end CylindricalHoles

/--
Semantic certificate synthesized by the recursive cylindrification checker.
The two fields are intentionally operation-generic: arity shift and unshift
select opposite sides of the same checked certificate.
-/
structure CylindricalRegionCertificate
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerOuter)
    (larger :
      UniformIntrinsicRegion definitions largerArguments largerOuter) :
    Prop where
  forward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (smallerSite :
        PreModel.Args pre.Domain smallerArguments → Prop),
        smaller.denote pre definitionEnv smallerEnv smallerSite ↔
          larger.denote pre definitionEnv largerEnv
            (cylindricalLift insertion smallerSite)
  backward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (largerSite :
        PreModel.Args pre.Domain largerArguments → Prop),
        smaller.denote pre definitionEnv smallerEnv
            (cylindricalProject insertion largerSite) ↔
          larger.denote pre definitionEnv largerEnv largerSite

structure CylindricalItemCertificate
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      UniformIntrinsicItem definitions smallerArguments smallerOuter)
    (larger :
      UniformIntrinsicItem definitions largerArguments largerOuter) :
    Prop where
  forward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (smallerSite :
        PreModel.Args pre.Domain smallerArguments → Prop),
        UniformIntrinsicRegion.UniformIntrinsicItem.denote
            pre definitionEnv smallerEnv smallerSite smaller ↔
          UniformIntrinsicRegion.UniformIntrinsicItem.denote
            pre definitionEnv largerEnv
              (cylindricalLift insertion smallerSite) larger
  backward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (largerSite :
        PreModel.Args pre.Domain largerArguments → Prop),
        UniformIntrinsicRegion.UniformIntrinsicItem.denote
            pre definitionEnv smallerEnv
              (cylindricalProject insertion largerSite) smaller ↔
          UniformIntrinsicRegion.UniformIntrinsicItem.denote
            pre definitionEnv largerEnv largerSite larger

structure CylindricalItemSeqCertificate
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      UniformIntrinsicItemSeq definitions smallerArguments smallerOuter)
    (larger :
      UniformIntrinsicItemSeq definitions largerArguments largerOuter) :
    Prop where
  forward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (smallerSite :
        PreModel.Args pre.Domain smallerArguments → Prop),
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv smallerEnv smallerSite smaller ↔
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv largerEnv
              (cylindricalLift insertion smallerSite) larger
  backward :
    ∀ (pre : PreModel.{u})
      (definitionEnv : DefinitionEnv pre definitions)
      (smallerEnv : Env pre smallerOuter)
      (largerEnv : Env pre largerOuter),
      Env.comp largerEnv outer = smallerEnv →
      ∀ (largerSite :
        PreModel.Args pre.Domain largerArguments → Prop),
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv smallerEnv
              (cylindricalProject insertion largerSite) smaller ↔
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
            pre definitionEnv largerEnv largerSite larger

mutual

inductive CylindricalShape
    (definitions : List (List Sig))
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature) :
    List Sig → List Sig → Type
  | block
      {smallerOuter largerOuter : List Sig}
      (outer : WireRenaming smallerOuter largerOuter)
      {smallerBound largerBound : List Sig}
      {freshCount : Nat}
      (bounds :
        BoundCylindrification fixedSignature smallerBound largerBound
          freshCount)
      {smallerHoles :
        List
          (Vars (smallerBound ++ smallerOuter) smallerArguments)}
      {largerHoles :
        List
          (Vars (largerBound ++ largerOuter) largerArguments)}
      (items :
        CylindricalShapeItemSeq definitions insertion
          (smallerBound ++ smallerOuter)
          (largerBound ++ largerOuter))
      (holes :
        CylindricalHoles insertion bounds outer smallerHoles largerHoles) :
      CylindricalShape definitions insertion smallerOuter largerOuter

inductive CylindricalShapeItem
    (definitions : List (List Sig))
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature) :
    List Sig → List Sig → Type
  | leaf
      {smallerContext largerContext : List Sig}
      (embedding : WireRenaming smallerContext largerContext)
      (smaller : Item definitions smallerContext)
      (larger : Item definitions largerContext)
      (exact : smaller.renameWires embedding = larger) :
      CylindricalShapeItem definitions insertion
        smallerContext largerContext
  | cut
      {smallerContext largerContext : List Sig}
      (body :
        CylindricalShape definitions insertion
          smallerContext largerContext) :
      CylindricalShapeItem definitions insertion
        smallerContext largerContext

inductive CylindricalShapeItemSeq
    (definitions : List (List Sig))
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature) :
    List Sig → List Sig → Type
  | nil
      {smallerContext largerContext : List Sig}
      (embedding : WireRenaming smallerContext largerContext) :
      CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext
  | cons
      {smallerContext largerContext : List Sig}
      (head :
        CylindricalShapeItem definitions insertion
          smallerContext largerContext)
      (tail :
        CylindricalShapeItemSeq definitions insertion
          smallerContext largerContext)
      :
      CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext

end

mutual

def CylindricalShape.embedding
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShape definitions insertion smallerContext largerContext →
      WireRenaming smallerContext largerContext
  | .block outer _ _ _ => outer

def CylindricalShapeItem.embedding
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItem definitions insertion
        smallerContext largerContext →
      WireRenaming smallerContext largerContext
  | .leaf embedding _ _ _ => embedding
  | .cut body => body.embedding

def CylindricalShapeItemSeq.embedding
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext →
      WireRenaming smallerContext largerContext
  | .nil embedding => embedding
  | .cons head _ => head.embedding

def CylindricalShape.smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShape definitions insertion smallerContext largerContext →
      UniformIntrinsicRegion definitions smallerArguments smallerContext
  | .block (smallerHoles := smallerHoles) _ bounds items _ =>
      wrapArgumentBinds _
        (.mk items.smaller ⟨smallerHoles⟩)

def CylindricalShape.larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShape definitions insertion smallerContext largerContext →
      UniformIntrinsicRegion definitions largerArguments largerContext
  | .block (largerHoles := largerHoles) _ bounds items _ =>
      wrapArgumentBinds _
        (.mk items.larger ⟨largerHoles⟩)

def CylindricalShapeItem.smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItem definitions insertion
        smallerContext largerContext →
      UniformIntrinsicItem definitions smallerArguments smallerContext
  | .leaf _ smaller _ _ => .leaf smaller
  | .cut body => .cut body.smaller

def CylindricalShapeItem.larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItem definitions insertion
        smallerContext largerContext →
      UniformIntrinsicItem definitions largerArguments largerContext
  | .leaf _ _ larger _ => .leaf larger
  | .cut body => .cut body.larger

def CylindricalShapeItemSeq.smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext →
      UniformIntrinsicItemSeq definitions smallerArguments smallerContext
  | .nil _ => .nil
  | .cons head tail => .cons head.smaller tail.smaller

def CylindricalShapeItemSeq.larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature} :
    CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext →
      UniformIntrinsicItemSeq definitions largerArguments largerContext
  | .nil _ => .nil
  | .cons head tail => .cons head.larger tail.larger

end

mutual

def CylindricalShape.consistent :
    CylindricalShape definitions insertion smallerContext largerContext →
      Prop
  | .block outer bounds items _ =>
      items.consistent ∧
        ∀ {signature : Sig}
          (value : Var _ signature),
          items.embedding value = bounds.embed outer value

def CylindricalShapeItem.consistent :
    CylindricalShapeItem definitions insertion
        smallerContext largerContext →
      Prop
  | .leaf _ _ _ _ => True
  | .cut body => body.consistent

def CylindricalShapeItemSeq.consistent :
    CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext →
      Prop
  | .nil _ => True
  | .cons head tail =>
      head.consistent ∧ tail.consistent ∧
        ∀ {signature : Sig}
          (value : Var smallerContext signature),
          tail.embedding value = head.embedding value

end

structure CheckedCylindricalShape
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicRegion definitions largerArguments largerContext) where
  receipt :
    CylindricalShape definitions insertion smallerContext largerContext
  embedding_exact :
    ∀ {signature : Sig} (value : Var smallerContext signature),
      receipt.embedding value = outer value
  smaller_exact : receipt.smaller = smaller
  larger_exact : receipt.larger = larger
  consistent : receipt.consistent

structure CheckedCylindricalShapeItem
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicItem definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicItem definitions largerArguments largerContext) where
  receipt :
    CylindricalShapeItem definitions insertion
      smallerContext largerContext
  embedding_exact :
    ∀ {signature : Sig} (value : Var smallerContext signature),
      receipt.embedding value = outer value
  smaller_exact : receipt.smaller = smaller
  larger_exact : receipt.larger = larger
  consistent : receipt.consistent

structure CheckedCylindricalShapeItemSeq
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicItemSeq definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicItemSeq definitions largerArguments largerContext) where
  receipt :
    CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext
  embedding_exact :
    ∀ {signature : Sig} (value : Var smallerContext signature),
      receipt.embedding value = outer value
  smaller_exact : receipt.smaller = smaller
  larger_exact : receipt.larger = larger
  consistent : receipt.consistent

mutual

def argumentShapeDepth :
    UniformIntrinsicRegion definitions arguments context → Nat
  | .mk items _ => argumentShapeItemSeqDepth items + 1

def argumentShapeItemDepth :
    UniformIntrinsicItem definitions arguments context → Nat
  | .leaf _ => 1
  | .cut body => argumentShapeDepth body + 1
  | .bind _ body => argumentShapeDepth body + 1

def argumentShapeItemSeqDepth :
    UniformIntrinsicItemSeq definitions arguments context → Nat
  | .nil => 1
  | .cons head tail =>
      argumentShapeItemDepth head + argumentShapeItemSeqDepth tail + 1

end

def checkCylindricalShapeFromPeeled
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicRegion definitions largerArguments largerContext)
    (smallerPeeled : PeeledArgumentShape smaller)
    (largerPeeled : PeeledArgumentShape larger)
    (checkItems :
      ∀ {smallerBound largerBound : List Sig},
        (inner : WireRenaming smallerBound largerBound) →
        (smallerItems :
          UniformIntrinsicItemSeq definitions smallerArguments smallerBound) →
        (largerItems :
          UniformIntrinsicItemSeq definitions largerArguments largerBound) →
        Option
          (CheckedCylindricalShapeItemSeq insertion inner
            smallerItems largerItems)) :
    Option (CheckedCylindricalShape insertion outer smaller larger) :=
  (BoundCylindrification.candidates fixedSignature
      smallerPeeled.bound largerPeeled.bound).findSome? fun candidate =>
    let ⟨_freshCount, bounds⟩ := candidate
    do
      let items ←
        checkItems (bounds.embed outer)
          smallerPeeled.items largerPeeled.items
      if holesAccepted :
          checkCylindricalHoles insertion bounds outer
              smallerPeeled.holes largerPeeled.holes = true then
        let holes := checkCylindricalHoles_eq_true holesAccepted
        let receipt : CylindricalShape definitions insertion
            smallerContext largerContext :=
          .block outer bounds items.receipt holes
        have receiptConsistent : receipt.consistent := by
          exact
            ⟨items.consistent,
              fun value => by
                exact items.embedding_exact value⟩
        have smallerExact : receipt.smaller = smaller := by
          change
            wrapArgumentBinds smallerPeeled.bound
                (.mk items.receipt.smaller ⟨smallerPeeled.holes⟩) =
              smaller
          rw [items.smaller_exact]
          exact smallerPeeled.exact.symm
        have largerExact : receipt.larger = larger := by
          change
            wrapArgumentBinds largerPeeled.bound
                (.mk items.receipt.larger ⟨largerPeeled.holes⟩) =
              larger
          rw [items.larger_exact]
          exact largerPeeled.exact.symm
        some
          { receipt := receipt
            embedding_exact := fun _ => rfl
            smaller_exact := smallerExact
            larger_exact := largerExact
            consistent := receiptConsistent }
      else
        none

mutual

def checkCylindricalShapeFuel
    (fuel : Nat)
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicRegion definitions largerArguments largerContext) :
    Option
      (CheckedCylindricalShape insertion outer smaller larger) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let smallerPeeled := peelArgumentShape smaller
      let largerPeeled := peelArgumentShape larger
      checkCylindricalShapeFromPeeled insertion outer smaller larger
        smallerPeeled largerPeeled fun inner =>
          checkCylindricalShapeItemSeqFuel fuel insertion inner

def checkCylindricalShapeItemFuel
    (fuel : Nat)
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicItem definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicItem definitions largerArguments largerContext) :
    Option
      (CheckedCylindricalShapeItem insertion outer smaller larger) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match smaller, larger with
      | .leaf smallerItem, .leaf largerItem =>
          if exact : smallerItem.renameWires outer = largerItem then
            some
              { receipt := .leaf outer smallerItem largerItem exact
                embedding_exact := fun _ => rfl
                smaller_exact := rfl
                larger_exact := rfl
                consistent := True.intro }
          else
            none
      | .cut smallerBody, .cut largerBody => do
          let body ←
            checkCylindricalShapeFuel fuel insertion outer
              smallerBody largerBody
          some
            { receipt := .cut body.receipt
              embedding_exact := body.embedding_exact
              smaller_exact := congrArg UniformIntrinsicItem.cut
                body.smaller_exact
              larger_exact := congrArg UniformIntrinsicItem.cut
                body.larger_exact
              consistent := body.consistent }
      | _, _ => none

def checkCylindricalShapeItemSeqFuel
    (fuel : Nat)
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicItemSeq definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicItemSeq definitions largerArguments largerContext) :
    Option
      (CheckedCylindricalShapeItemSeq insertion outer smaller larger) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match smaller, larger with
      | .nil, .nil =>
          some
            { receipt := .nil outer
              embedding_exact := fun _ => rfl
              smaller_exact := rfl
              larger_exact := rfl
              consistent := True.intro }
      | .cons smallerHead smallerTail,
          .cons largerHead largerTail => do
          let head ←
            checkCylindricalShapeItemFuel fuel insertion outer
              smallerHead largerHead
          let tail ←
            checkCylindricalShapeItemSeqFuel fuel insertion outer
              smallerTail largerTail
          let receipt :
              CylindricalShapeItemSeq definitions insertion
                smallerContext largerContext :=
            .cons head.receipt tail.receipt
          have receiptConsistent : receipt.consistent := by
            exact
              ⟨head.consistent, tail.consistent,
                fun value => by
                  rw [tail.embedding_exact value,
                    head.embedding_exact value]⟩
          some
            { receipt := receipt
              embedding_exact := head.embedding_exact
              smaller_exact := by
                change
                  UniformIntrinsicItemSeq.cons
                      head.receipt.smaller tail.receipt.smaller =
                    UniformIntrinsicItemSeq.cons
                      smallerHead smallerTail
                rw [head.smaller_exact, tail.smaller_exact]
              larger_exact := by
                change
                  UniformIntrinsicItemSeq.cons
                      head.receipt.larger tail.receipt.larger =
                    UniformIntrinsicItemSeq.cons
                      largerHead largerTail
                rw [head.larger_exact, tail.larger_exact]
              consistent := receiptConsistent }
      | _, _ => none

end

def checkCylindricalShape
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (outer : WireRenaming smallerContext largerContext)
    (smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerContext)
    (larger :
      UniformIntrinsicRegion definitions largerArguments largerContext) :
    Option
      (CheckedCylindricalShape insertion outer smaller larger) :=
  checkCylindricalShapeFuel
    (argumentShapeDepth smaller + argumentShapeDepth larger + 1)
    insertion outer smaller larger

mutual

theorem CylindricalShape.forward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {shape :
      CylindricalShape definitions insertion
        smallerContext largerContext}
    (consistent : shape.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv shape.embedding = smallerEnv)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop) :
    shape.smaller.denote pre definitionEnv smallerEnv smallerSite ↔
      shape.larger.denote pre definitionEnv largerEnv
        (cylindricalLift insertion smallerSite) := by
  cases shape with
  | block outer bounds items holes =>
      have items_consistent := consistent.1
      change Env.comp largerEnv outer = smallerEnv at envExact
      change
        (wrapArgumentBinds _
          (.mk items.smaller ⟨_⟩)).denote
            pre definitionEnv smallerEnv smallerSite ↔
          (wrapArgumentBinds _
            (.mk items.larger ⟨_⟩)).denote
              pre definitionEnv largerEnv
                (cylindricalLift insertion smallerSite)
      rw [wrapArgumentBinds_denotes, wrapArgumentBinds_denotes]
      constructor
      · rintro ⟨smallerValues, smallerHolds⟩
        let assignment : Fin bounds.count → pre.Domain fixedSignature :=
          fun _ => chooseInhabitant pre fixedSignature
        let largerValues :=
          bounds.assembleValues smallerValues assignment
        refine ⟨largerValues, ?_⟩
        let innerSmallerEnv :=
          ContentShapeSemantics.extendValues smallerValues smallerEnv
        let innerLargerEnv :=
          ContentShapeSemantics.extendValues largerValues largerEnv
        have boundsExact :=
          bounds.comp_assembled pre smallerValues assignment
            smallerEnv largerEnv envExact
        have innerExact :
            Env.comp innerLargerEnv items.embedding =
              innerSmallerEnv := by
          funext signature value
          change
            innerLargerEnv _ (items.embedding value) =
              innerSmallerEnv _ value
          rw [consistent.2 value]
          exact congrFun (congrFun boundsExact signature) value
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerSmallerEnv smallerSite
                items.smaller ∧
            (∀ value, value ∈ _ →
              smallerSite (Vars.denote innerSmallerEnv value))
            at smallerHolds
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerLargerEnv
                (cylindricalLift insertion smallerSite)
                items.larger ∧
            (∀ value, value ∈ _ →
              cylindricalLift insertion smallerSite
                (Vars.denote innerLargerEnv value))
        exact
          ⟨(CylindricalShapeItemSeq.forward_denotes items_consistent
              pre definitionEnv
              innerSmallerEnv innerLargerEnv innerExact
              smallerSite).mp smallerHolds.1,
            (holes.forward pre innerSmallerEnv innerLargerEnv
              boundsExact
              smallerSite).mpr smallerHolds.2⟩
      · rintro ⟨largerValues, largerHolds⟩
        let smallerValues := bounds.projectValues largerValues
        let assignment := bounds.freshValues largerValues
        refine ⟨smallerValues, ?_⟩
        let innerSmallerEnv :=
          ContentShapeSemantics.extendValues smallerValues smallerEnv
        let innerLargerEnv :=
          ContentShapeSemantics.extendValues largerValues largerEnv
        have boundsExact :
            Env.comp innerLargerEnv (bounds.embed outer) =
              innerSmallerEnv := by
          have assembled :=
            bounds.comp_assembled pre smallerValues assignment
              smallerEnv largerEnv envExact
          rw [bounds.assemble_project_fresh largerValues] at assembled
          exact assembled
        have innerExact :
            Env.comp innerLargerEnv items.embedding =
              innerSmallerEnv := by
          funext signature value
          change
            innerLargerEnv _ (items.embedding value) =
              innerSmallerEnv _ value
          rw [consistent.2 value]
          exact congrFun (congrFun boundsExact signature) value
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerLargerEnv
                (cylindricalLift insertion smallerSite)
                items.larger ∧
            (∀ value, value ∈ _ →
              cylindricalLift insertion smallerSite
                (Vars.denote innerLargerEnv value))
            at largerHolds
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerSmallerEnv smallerSite
                items.smaller ∧
            (∀ value, value ∈ _ →
              smallerSite (Vars.denote innerSmallerEnv value))
        exact
          ⟨(CylindricalShapeItemSeq.forward_denotes items_consistent
              pre definitionEnv
              innerSmallerEnv innerLargerEnv innerExact
              smallerSite).mpr largerHolds.1,
            (holes.forward pre innerSmallerEnv innerLargerEnv
              boundsExact smallerSite).mp largerHolds.2⟩

theorem CylindricalShapeItem.forward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {item :
      CylindricalShapeItem definitions insertion
        smallerContext largerContext}
    (consistent : item.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv item.embedding = smallerEnv)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop) :
    UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv smallerEnv smallerSite item.smaller ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv largerEnv
          (cylindricalLift insertion smallerSite) item.larger := by
  cases item with
  | leaf embedding smaller larger exact =>
      change Env.comp largerEnv embedding = smallerEnv at envExact
      change
        denoteItem pre definitionEnv smallerEnv smaller ↔
          denoteItem pre definitionEnv largerEnv larger
      subst larger
      simpa only [envExact] using
        (denoteItem_renameWires pre definitionEnv largerEnv embedding
          smaller).symm
  | cut body =>
      have body_consistent := consistent
      change Env.comp largerEnv body.embedding = smallerEnv at envExact
      change
        ¬ body.smaller.denote pre definitionEnv smallerEnv smallerSite ↔
          ¬ body.larger.denote pre definitionEnv largerEnv
            (cylindricalLift insertion smallerSite)
      exact not_congr
        (CylindricalShape.forward_denotes body_consistent
          pre definitionEnv
          smallerEnv largerEnv envExact smallerSite)

theorem CylindricalShapeItemSeq.forward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {items :
      CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext}
    (consistent : items.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv items.embedding = smallerEnv)
    (smallerSite :
      PreModel.Args pre.Domain smallerArguments → Prop) :
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv smallerEnv smallerSite items.smaller ↔
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv largerEnv
          (cylindricalLift insertion smallerSite) items.larger := by
  cases items with
  | nil embedding =>
      exact Iff.rfl
  | cons head tail =>
      have head_consistent := consistent.1
      have tail_consistent := consistent.2.1
      have tailExact :
          Env.comp largerEnv tail.embedding = smallerEnv := by
        funext signature value
        change largerEnv _ (tail.embedding value) = smallerEnv _ value
        rw [consistent.2.2 value]
        exact congrFun (congrFun envExact signature) value
      exact and_congr
        (CylindricalShapeItem.forward_denotes head_consistent
          pre definitionEnv
          smallerEnv largerEnv envExact smallerSite)
        (CylindricalShapeItemSeq.forward_denotes tail_consistent
          pre definitionEnv
          smallerEnv largerEnv tailExact smallerSite)

end

mutual

theorem CylindricalShape.backward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {shape :
      CylindricalShape definitions insertion
        smallerContext largerContext}
    (consistent : shape.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv shape.embedding = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop) :
    shape.smaller.denote pre definitionEnv smallerEnv
        (cylindricalProject insertion largerSite) ↔
      shape.larger.denote pre definitionEnv largerEnv largerSite := by
  cases shape with
  | block outer bounds items holes =>
      have items_consistent := consistent.1
      change Env.comp largerEnv outer = smallerEnv at envExact
      change
        (wrapArgumentBinds _
          (.mk items.smaller ⟨_⟩)).denote
            pre definitionEnv smallerEnv
              (cylindricalProject insertion largerSite) ↔
          (wrapArgumentBinds _
            (.mk items.larger ⟨_⟩)).denote
              pre definitionEnv largerEnv largerSite
      rw [wrapArgumentBinds_denotes, wrapArgumentBinds_denotes]
      constructor
      · rintro ⟨smallerValues, smallerHolds⟩
        let innerSmallerEnv :=
          ContentShapeSemantics.extendValues smallerValues smallerEnv
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerSmallerEnv
                (cylindricalProject insertion largerSite)
                items.smaller ∧
            (∀ value, value ∈ _ →
              cylindricalProject insertion largerSite
                (Vars.denote innerSmallerEnv value))
            at smallerHolds
        let assignment :=
          holes.backwardAssignment pre innerSmallerEnv largerSite
            smallerHolds.2
        let largerValues :=
          bounds.assembleValues smallerValues assignment
        refine ⟨largerValues, ?_⟩
        let innerLargerEnv :=
          ContentShapeSemantics.extendValues largerValues largerEnv
        have boundsExact :=
          bounds.comp_assembled pre smallerValues assignment
            smallerEnv largerEnv envExact
        have innerExact :
            Env.comp innerLargerEnv items.embedding =
              innerSmallerEnv := by
          funext signature value
          change
            innerLargerEnv _ (items.embedding value) =
              innerSmallerEnv _ value
          rw [consistent.2 value]
          exact congrFun (congrFun boundsExact signature) value
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerLargerEnv largerSite
                items.larger ∧
            (∀ value, value ∈ _ →
              largerSite (Vars.denote innerLargerEnv value))
        refine
          ⟨(CylindricalShapeItemSeq.backward_denotes
              items_consistent pre definitionEnv innerSmallerEnv
              innerLargerEnv innerExact largerSite).mp
              smallerHolds.1, ?_⟩
        apply
          holes.backward_to_larger pre innerSmallerEnv innerLargerEnv
            boundsExact largerSite smallerHolds.2
        intro index
        exact
          bounds.freshVar_assembled pre smallerValues assignment
            largerEnv index
      · rintro ⟨largerValues, largerHolds⟩
        let smallerValues := bounds.projectValues largerValues
        let assignment := bounds.freshValues largerValues
        refine ⟨smallerValues, ?_⟩
        let innerSmallerEnv :=
          ContentShapeSemantics.extendValues smallerValues smallerEnv
        let innerLargerEnv :=
          ContentShapeSemantics.extendValues largerValues largerEnv
        have boundsExact :
            Env.comp innerLargerEnv (bounds.embed outer) =
              innerSmallerEnv := by
          have assembled :=
            bounds.comp_assembled pre smallerValues assignment
              smallerEnv largerEnv envExact
          rw [bounds.assemble_project_fresh largerValues] at assembled
          exact assembled
        have innerExact :
            Env.comp innerLargerEnv items.embedding =
              innerSmallerEnv := by
          funext signature value
          change
            innerLargerEnv _ (items.embedding value) =
              innerSmallerEnv _ value
          rw [consistent.2 value]
          exact congrFun (congrFun boundsExact signature) value
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerLargerEnv largerSite
                items.larger ∧
            (∀ value, value ∈ _ →
              largerSite (Vars.denote innerLargerEnv value))
            at largerHolds
        change
          UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
              pre definitionEnv innerSmallerEnv
                (cylindricalProject insertion largerSite)
                items.smaller ∧
            (∀ value, value ∈ _ →
              cylindricalProject insertion largerSite
                (Vars.denote innerSmallerEnv value))
        exact
          ⟨(CylindricalShapeItemSeq.backward_denotes
              items_consistent pre definitionEnv innerSmallerEnv
              innerLargerEnv innerExact largerSite).mpr largerHolds.1,
            holes.backward_from_larger pre innerSmallerEnv
              innerLargerEnv boundsExact largerSite largerHolds.2⟩

theorem CylindricalShapeItem.backward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {item :
      CylindricalShapeItem definitions insertion
        smallerContext largerContext}
    (consistent : item.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv item.embedding = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop) :
    UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv smallerEnv
          (cylindricalProject insertion largerSite) item.smaller ↔
      UniformIntrinsicRegion.UniformIntrinsicItem.denote
        pre definitionEnv largerEnv largerSite item.larger := by
  cases item with
  | leaf embedding smaller larger exact =>
      change Env.comp largerEnv embedding = smallerEnv at envExact
      change
        denoteItem pre definitionEnv smallerEnv smaller ↔
          denoteItem pre definitionEnv largerEnv larger
      subst larger
      simpa only [envExact] using
        (denoteItem_renameWires pre definitionEnv largerEnv embedding
          smaller).symm
  | cut body =>
      have body_consistent := consistent
      change Env.comp largerEnv body.embedding = smallerEnv at envExact
      change
        ¬ body.smaller.denote pre definitionEnv smallerEnv
            (cylindricalProject insertion largerSite) ↔
          ¬ body.larger.denote pre definitionEnv largerEnv largerSite
      exact not_congr
        (CylindricalShape.backward_denotes body_consistent
          pre definitionEnv smallerEnv largerEnv envExact largerSite)

theorem CylindricalShapeItemSeq.backward_denotes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {items :
      CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext}
    (consistent : items.consistent)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (smallerEnv : Env pre smallerContext)
    (largerEnv : Env pre largerContext)
    (envExact :
      Env.comp largerEnv items.embedding = smallerEnv)
    (largerSite :
      PreModel.Args pre.Domain largerArguments → Prop) :
    UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv smallerEnv
          (cylindricalProject insertion largerSite) items.smaller ↔
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.denote
        pre definitionEnv largerEnv largerSite items.larger := by
  cases items with
  | nil embedding =>
      exact Iff.rfl
  | cons head tail =>
      have head_consistent := consistent.1
      have tail_consistent := consistent.2.1
      have tailExact :
          Env.comp largerEnv tail.embedding = smallerEnv := by
        funext signature value
        change largerEnv _ (tail.embedding value) = smallerEnv _ value
        rw [consistent.2.2 value]
        exact congrFun (congrFun envExact signature) value
      exact and_congr
        (CylindricalShapeItem.backward_denotes head_consistent
          pre definitionEnv smallerEnv largerEnv envExact largerSite)
        (CylindricalShapeItemSeq.backward_denotes tail_consistent
          pre definitionEnv smallerEnv largerEnv tailExact largerSite)

end

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
