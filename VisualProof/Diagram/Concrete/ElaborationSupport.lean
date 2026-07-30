import VisualProof.Diagram.Concrete.Isomorphism
import VisualProof.Diagram.Semantics

namespace VisualProof

namespace ItemSeq

def toList : ItemSeq definitions context → List (Item definitions context)
  | .nil => []
  | .cons head tail => head :: tail.toList

theorem denote_iff_mem
    (pre : PreModel) (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context) (items : ItemSeq definitions context) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ item, item ∈ items.toList →
        denoteItem pre definitionEnv env item := by
  cases items with
  | nil => simp [toList, denoteItemSeq]
  | cons head tail =>
      simp only [toList, denoteItemSeq_cons, List.mem_cons, forall_eq_or_imp]
      exact and_congr_right fun _ =>
        denote_iff_mem pre definitionEnv env tail
termination_by items

end ItemSeq

theorem AllEqual.iff_of_mem_iff
    {left right : List α}
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    AllEqual left ↔ AllEqual right := by
  constructor
  · intro leftEqual first firstMember second secondMember
    exact leftEqual first ((sameMembers first).mpr firstMember)
      second ((sameMembers second).mpr secondMember)
  · intro rightEqual first firstMember second secondMember
    exact rightEqual first ((sameMembers first).mp firstMember)
      second ((sameMembers second).mp secondMember)

namespace ConcreteElaboration

/-- Concrete wires currently visible at one lexical region boundary. -/
structure WireContext (diagram : ConcreteDiagram definitionCount) where
  ids : List diagram.WireId

namespace WireContext

def sigs (context : WireContext diagram) : List Sig :=
  context.ids.map fun wire => (diagram.wires wire).sig

/--
Recover the concrete wire named by a typed variable in this ordered context.
This is the structural observation surface for compiler naturality; resolver
search remains private to elaboration.
-/
def origin
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) → {sig : Sig} →
      Var (ids.map fun wire => (diagram.wires wire).sig) sig →
        diagram.WireId
  | [], _, value => nomatch value
  | head :: _, _, .here => head
  | _ :: tail, _, .there value =>
      origin diagram tail value

theorem origin_signature
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) {sig : Sig}
    (value : Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    (diagram.wires (origin diagram ids value)).sig = sig := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

def empty (diagram : ConcreteDiagram definitionCount) : WireContext diagram :=
  ⟨[]⟩

def extend (context : WireContext diagram) (region : diagram.RegionId) :
    WireContext diagram :=
  ⟨diagram.wiresAt region ++ context.ids⟩

@[simp] theorem sigs_empty :
    (empty diagram).sigs = [] := rfl

@[simp] theorem sigs_extend (context : WireContext diagram)
    (region : diagram.RegionId) :
    (context.extend region).sigs =
      (diagram.wiresAt region).map (fun wire => (diagram.wires wire).sig) ++
        context.sigs := by
  simp [extend, sigs]

end WireContext

/-- Concrete wires named by an ordered typed variable tuple. -/
def variableOrigins
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) :
    {args : List Sig} → Vars context.sigs args → List diagram.WireId
  | [], .nil => []
  | _ :: _, .cons head tail =>
      WireContext.origin diagram context.ids head ::
        variableOrigins diagram context tail

/--
Exact concrete endpoint ownership retained by one typed relation-argument
tuple. This is observational compiler evidence; it performs no resolution.
-/
def ArgumentOrigins
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram)
    (node : diagram.NodeId) :
    (index : Nat) → {args : List Sig} → Vars context.sigs args → Prop
  | _, [], .nil => True
  | index, _ :: _, .cons head tail =>
      diagram.endpointOwner? ⟨node, .arg index⟩ =
          some (WireContext.origin diagram context.ids head) ∧
        ArgumentOrigins diagram context node (index + 1) tail

/-- Values for one ordered concrete-wire signature vector. -/
inductive WireValues (pre : PreModel.{u}) : List Sig → Type u
  | nil : WireValues pre []
  | cons (head : pre.Domain sig) (tail : WireValues pre rest) :
      WireValues pre (sig :: rest)

def appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    {rightIds : List diagram.WireId} {sig : Sig} :
    (leftIds : List diagram.WireId) →
    Var (rightIds.map fun id => (diagram.wires id).sig) sig →
    Var ((leftIds ++ rightIds).map fun id => (diagram.wires id).sig) sig
  | [], value => value
  | _ :: tail, value => .there (appendRightVar diagram tail value)

theorem origin_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId)
    {rightIds : List diagram.WireId} {sig : Sig}
    (value : Var (rightIds.map fun id => (diagram.wires id).sig) sig) :
    WireContext.origin diagram (leftIds ++ rightIds)
        (appendRightVar diagram leftIds value) =
      WireContext.origin diagram rightIds value := by
  induction leftIds with
  | nil => rfl
  | cons _ _ induction =>
      simpa [appendRightVar, WireContext.origin] using induction

/-- Extend an environment by an explicit ordered list of local wire values. -/
def extendEnvironmentFor
    (diagram : ConcreteDiagram definitionCount)
    {pre : PreModel}
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
    WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig) →
    Env pre (outerIds.map fun wire => (diagram.wires wire).sig) →
    Env pre
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig)
  | [], .nil, outerEnv => outerEnv
  | _ :: tail, .cons head rest, outerEnv =>
      (extendEnvironmentFor diagram outerIds tail rest outerEnv).extend head

def extendEnvironment
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId)
    {pre : PreModel}
    (values : WireValues pre
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs) :
    Env pre (context.extend region).sigs :=
  extendEnvironmentFor diagram context.ids (diagram.wiresAt region)
    values outerEnv

private theorem extendEnvironmentFor_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    {pre : PreModel}
    (values : WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    {sig : Sig}
    (value : Var
      (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    extendEnvironmentFor diagram outerIds localIds values outerEnv sig
        (appendRightVar diagram localIds value) =
      outerEnv sig value := by
  induction localIds with
  | nil => cases values; rfl
  | cons _ _ induction =>
      cases values with
      | cons _ tailValues => exact induction tailValues

def valuesFromEnvironmentFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
    Env pre ((localIds ++ outerIds).map fun wire =>
      (diagram.wires wire).sig) →
    WireValues pre (localIds.map fun wire => (diagram.wires wire).sig)
  | [], _ => .nil
  | _ :: tail, env =>
      .cons (env _ .here)
        (valuesFromEnvironmentFor diagram outerIds tail
          (fun sig value => env sig (.there value)))

theorem extendEnvironmentFor_from
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (env : Env pre ((localIds ++ outerIds).map fun wire =>
      (diagram.wires wire).sig))
    (outerEnv : Env pre (outerIds.map fun wire => (diagram.wires wire).sig))
    (agrees : ∀ sig (value : Var
      (outerIds.map fun wire => (diagram.wires wire).sig) sig),
      env sig (appendRightVar diagram localIds value) = outerEnv sig value) :
    extendEnvironmentFor diagram outerIds localIds
        (valuesFromEnvironmentFor diagram outerIds localIds env) outerEnv =
      env := by
  induction localIds with
  | nil =>
      funext sig value
      exact (agrees sig value).symm
  | cons _ _ induction =>
      funext sig value
      cases value with
      | here => rfl
      | there value =>
          exact congrFun (congrFun
            (induction (fun sig value => env sig (.there value))
              (by
                intro sig outer
                exact agrees sig outer)) sig) value

theorem extendEnvironment_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId)
    {pre : PreModel}
    (values : WireValues pre
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig} (value : Var context.sigs sig) :
    extendEnvironment diagram context region values outerEnv sig
        (appendRightVar diagram (diagram.wiresAt region) value) =
      outerEnv sig value := by
  exact extendEnvironmentFor_appendRightVar diagram context.ids
    (diagram.wiresAt region) values outerEnv value

structure WireContextsCorrespond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftContext : WireContext left)
    (rightContext : WireContext right) : Prop where
  forward :
    ∀ wire, wire ∈ leftContext.ids →
      iso.wires wire ∈ rightContext.ids
  backward :
    ∀ wire, wire ∈ rightContext.ids →
      iso.wires.symm wire ∈ leftContext.ids

theorem WireContextsCorrespond.symm
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    {iso : ConcreteIso left right}
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext) :
    WireContextsCorrespond iso.symm rightContext leftContext := by
  constructor
  · intro wire member
    exact contexts.backward wire member
  · intro wire member
    simpa [ConcreteIso.symm] using contexts.forward wire member

theorem empty_contexts_correspond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) :
    WireContextsCorrespond iso
      (WireContext.empty left) (WireContext.empty right) := by
  constructor
  · intro wire member
    change wire ∈ [] at member
    simp at member
  · intro wire member
    change wire ∈ [] at member
    simp at member

theorem extend_contexts_correspond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (region : left.RegionId) :
    WireContextsCorrespond iso
      (leftContext.extend region)
      (rightContext.extend (iso.regions region)) := by
  constructor
  · intro wire member
    simp only [WireContext.extend, List.mem_append] at member ⊢
    rcases member with localMember | outer
    · exact Or.inl (iso.wiresAt_forward localMember)
    · exact Or.inr (contexts.forward wire outer)
  · intro wire member
    simp only [WireContext.extend, List.mem_append] at member ⊢
    rcases member with localMember | outer
    · have pulled := iso.wiresAt_backward localMember
      have localPulled :
          iso.wires.symm wire ∈ left.wiresAt region := by
        change iso.wires.symm wire ∈
          left.wiresAt (iso.regions.invFun (iso.regions region)) at pulled
        have regionEquality := iso.regions.left_inv region
        rw [regionEquality] at pulled
        exact pulled
      exact Or.inl localPulled
    · exact Or.inr (contexts.backward wire outer)

end ConcreteElaboration

end VisualProof
