import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedEnvironment

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Ordered conjunction of the compiled selected block for each occurrence. -/
def occurrenceFamilyItems
    (items : ι → ItemSeq  wireCount rels) :
    List ι → ItemSeq  wireCount rels
  | [] => .nil
  | index :: rest => (items index).append (occurrenceFamilyItems items rest)

/-- Ordered conjunction of the one fresh atom compiled for each occurrence. -/
def occurrenceFamilyAtomItems
    (items : ι → Item  wireCount rels) :
    List ι → ItemSeq  wireCount rels
  | [] => .nil
  | index :: rest => .cons (items index) (occurrenceFamilyAtomItems items rest)

theorem compileOccurrenceFamilyItems
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : Concrete.Elaboration.WireContext d) →
      Concrete.Elaboration.BinderContext d rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext d)
    (binders : Concrete.Elaboration.BinderContext d rels)
    (indices : List ι)
    (occurrences : ι → List (Concrete.Elaboration.LocalOccurrence
      d.regionCount d.nodeCount))
    (items : ι → ItemSeq  context.length rels)
    (compiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileOccurrencesWith?  d recurse
        context binders (occurrences index) = some (items index)) :
    Concrete.Elaboration.compileOccurrencesWith?  d recurse
        context binders (indices.flatMap occurrences) =
      some (occurrenceFamilyItems items indices) := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      exact Concrete.Elaboration.compileOccurrencesWith?_append recurse context
        binders (occurrences head) (tail.flatMap occurrences) (items head)
        (occurrenceFamilyItems items tail) (compiled head (by simp))
        (ih (by
          intro index member
          exact compiled index (by simp [member])))

theorem compileOccurrenceFamilyAtomItems
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : Concrete.Elaboration.WireContext d) →
      Concrete.Elaboration.BinderContext d rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext d)
    (binders : Concrete.Elaboration.BinderContext d rels)
    (indices : List ι)
    (occurrences : ι → Concrete.Elaboration.LocalOccurrence
      d.regionCount d.nodeCount)
    (items : ι → Item  context.length rels)
    (compiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileOccurrenceWith?  d recurse
        context binders (occurrences index) = some (items index)) :
    Concrete.Elaboration.compileOccurrencesWith?  d recurse
        context binders (indices.map occurrences) =
      some (occurrenceFamilyAtomItems items indices) := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, Concrete.Elaboration.compileOccurrencesWith?,
        occurrenceFamilyAtomItems]
      rw [compiled head (by simp), ih (by
        intro index member
        exact compiled index (by simp [member]))]
      rfl

theorem occurrenceFamilyItems_denote_iff
    (indices : List ι)
    (items : ι → ItemSeq  wireCount rels)
    (model : Model)
    (environment : Fin wireCount → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model  environment relations
        (occurrenceFamilyItems items indices) ↔
      ∀ index, index ∈ indices →
        denoteItemSeq model  environment relations (items index) := by
  induction indices with
  | nil => simp [occurrenceFamilyItems]
  | cons head tail ih =>
      simp only [occurrenceFamilyItems, denoteItemSeq_append]
      rw [ih]
      constructor
      · intro denotes index membership
        rcases denotes with ⟨headDenotes, tailDenotes⟩
        have cases : index = head ∨ index ∈ tail := by simpa using membership
        rcases cases with equal | member
        · subst index
          exact headDenotes
        · exact tailDenotes index member
      · intro all
        exact ⟨all head (by simp), fun index member =>
          all index (by simp [member])⟩

theorem occurrenceFamilyAtomItems_denote_iff
    (indices : List ι)
    (items : ι → Item  wireCount rels)
    (model : Model)
    (environment : Fin wireCount → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model  environment relations
        (occurrenceFamilyAtomItems items indices) ↔
      ∀ index, index ∈ indices →
        denoteItem model  environment relations (items index) := by
  induction indices with
  | nil => simp [occurrenceFamilyAtomItems]
  | cons head tail ih =>
      simp only [occurrenceFamilyAtomItems, denoteItemSeq]
      rw [ih]
      constructor
      · intro denotes index membership
        rcases denotes with ⟨headDenotes, tailDenotes⟩
        have cases : index = head ∨ index ∈ tail := by simpa using membership
        rcases cases with equal | member
        · subst index
          exact headDenotes
        · exact tailDenotes index member
      · intro all
        exact ⟨all head (by simp), fun index member =>
          all index (by simp [member])⟩

end AbstractionRawTrace

end VisualProof.Concrete
