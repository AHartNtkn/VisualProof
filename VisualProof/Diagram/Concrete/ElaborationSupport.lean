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
