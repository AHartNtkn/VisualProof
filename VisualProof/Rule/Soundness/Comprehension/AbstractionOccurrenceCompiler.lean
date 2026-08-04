import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Ordered conjunction of the compiled selected block for each occurrence. -/
def occurrenceFamilyItems
    (items : ι → ItemSeq signature wireCount rels) :
    List ι → ItemSeq signature wireCount rels
  | [] => .nil
  | index :: rest => (items index).append (occurrenceFamilyItems items rest)

/-- Ordered conjunction of the one fresh atom compiled for each occurrence. -/
def occurrenceFamilyAtomItems
    (items : ι → Item signature wireCount rels) :
    List ι → ItemSeq signature wireCount rels
  | [] => .nil
  | index :: rest => .cons (items index) (occurrenceFamilyAtomItems items rest)

theorem compileOccurrenceFamilyItems
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : ConcreteElaboration.WireContext d) →
      ConcreteElaboration.BinderContext d rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext d)
    (binders : ConcreteElaboration.BinderContext d rels)
    (indices : List ι)
    (occurrences : ι → List (ConcreteElaboration.LocalOccurrence
      d.regionCount d.nodeCount))
    (items : ι → ItemSeq signature context.length rels)
    (compiled : ∀ index, index ∈ indices →
      ConcreteElaboration.compileOccurrencesWith? signature d recurse
        context binders (occurrences index) = some (items index)) :
    ConcreteElaboration.compileOccurrencesWith? signature d recurse
        context binders (indices.flatMap occurrences) =
      some (occurrenceFamilyItems items indices) := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      exact ConcreteElaboration.compileOccurrencesWith?_append recurse context
        binders (occurrences head) (tail.flatMap occurrences) (items head)
        (occurrenceFamilyItems items tail) (compiled head (by simp))
        (ih (by
          intro index member
          exact compiled index (by simp [member])))

theorem compileOccurrenceFamilyAtomItems
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : ConcreteElaboration.WireContext d) →
      ConcreteElaboration.BinderContext d rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext d)
    (binders : ConcreteElaboration.BinderContext d rels)
    (indices : List ι)
    (occurrences : ι → ConcreteElaboration.LocalOccurrence
      d.regionCount d.nodeCount)
    (items : ι → Item signature context.length rels)
    (compiled : ∀ index, index ∈ indices →
      ConcreteElaboration.compileOccurrenceWith? signature d recurse
        context binders (occurrences index) = some (items index)) :
    ConcreteElaboration.compileOccurrencesWith? signature d recurse
        context binders (indices.map occurrences) =
      some (occurrenceFamilyAtomItems items indices) := by
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, ConcreteElaboration.compileOccurrencesWith?,
        occurrenceFamilyAtomItems]
      rw [compiled head (by simp), ih (by
        intro index member
        exact compiled index (by simp [member]))]
      rfl

theorem occurrenceFamilyItems_denote_iff
    (indices : List ι)
    (items : ι → ItemSeq signature wireCount rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin wireCount → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model named environment relations
        (occurrenceFamilyItems items indices) ↔
      ∀ index, index ∈ indices →
        denoteItemSeq model named environment relations (items index) := by
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
    (items : ι → Item signature wireCount rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin wireCount → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model named environment relations
        (occurrenceFamilyAtomItems items indices) ↔
      ∀ index, index ∈ indices →
        denoteItem model named environment relations (items index) := by
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

end VisualProof.Rule
