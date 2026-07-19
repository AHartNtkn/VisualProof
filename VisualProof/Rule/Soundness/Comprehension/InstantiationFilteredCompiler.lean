import VisualProof.Rule.Soundness.Comprehension.InstantiationDropCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Reinsert semantically certified occurrences into a compiled conjunction.
This is stated over the authoritative occurrence compiler: successful full and
filtered compilations fix the exact item sequences, while the caller supplies
only the denotation of items deliberately removed by the Boolean filter. -/
theorem compileOccurrencesWith_filter_denotes
    {signature : List Nat}
    (diagram : ConcreteDiagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : ConcreteElaboration.WireContext diagram) →
      ConcreteElaboration.BinderContext diagram rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    (keep : ConcreteElaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    (allItems keptItems : ItemSeq signature context.length rels)
    (allCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      diagram recurse context binders occurrences = some allItems)
    (keptCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      diagram recurse context binders (occurrences.filter keep) =
        some keptItems)
    (removedDenotes : ∀ occurrence,
      occurrence ∈ occurrences → keep occurrence = false →
      ∀ item,
        ConcreteElaboration.compileOccurrenceWith? signature diagram recurse
          context binders occurrence = some item →
        denoteItem model named environment relEnv item)
    (keptDenotes : denoteItemSeq model named environment relEnv keptItems) :
    denoteItemSeq model named environment relEnv allItems := by
  induction occurrences generalizing allItems keptItems with
  | nil =>
      simp only [ConcreteElaboration.compileOccurrencesWith?,
        List.filter_nil] at allCompiled keptCompiled
      cases allCompiled
      trivial
  | cons occurrence tail ih =>
      simp only [ConcreteElaboration.compileOccurrencesWith?] at allCompiled
      cases headResult : ConcreteElaboration.compileOccurrenceWith? signature
          diagram recurse context binders occurrence with
      | none => simp [headResult] at allCompiled
      | some headItem =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature diagram recurse context binders tail with
          | none => simp [headResult, tailResult] at allCompiled
          | some tailItems =>
              simp [headResult, tailResult] at allCompiled
              subst allItems
              cases kept : keep occurrence with
              | false =>
                  simp only [List.filter_cons, kept, Bool.false_eq_true,
                    ↓reduceIte] at keptCompiled
                  have headDenotes := removedDenotes occurrence (by simp)
                    kept headItem headResult
                  have tailRemoved : ∀ current,
                      current ∈ tail → keep current = false →
                      ∀ item,
                        ConcreteElaboration.compileOccurrenceWith? signature
                          diagram recurse context binders current = some item →
                        denoteItem model named environment relEnv item := by
                    intro current member
                    exact removedDenotes current (by simp [member])
                  exact ⟨headDenotes,
                    ih tailItems keptItems tailResult keptCompiled tailRemoved
                      keptDenotes⟩
              | true =>
                  simp only [List.filter_cons, kept, ↓reduceIte] at keptCompiled
                  simp only [ConcreteElaboration.compileOccurrencesWith?,
                    headResult] at keptCompiled
                  cases keptTailResult :
                      ConcreteElaboration.compileOccurrencesWith? signature
                        diagram recurse context binders
                          (tail.filter keep) with
                  | none => simp [keptTailResult] at keptCompiled
                  | some keptTail =>
                      simp [keptTailResult] at keptCompiled
                      subst keptItems
                      have tailRemoved : ∀ current,
                          current ∈ tail → keep current = false →
                          ∀ item,
                            ConcreteElaboration.compileOccurrenceWith?
                              signature diagram recurse context binders
                                current = some item →
                            denoteItem model named environment relEnv item := by
                        intro current member
                        exact removedDenotes current (by simp [member])
                      exact ⟨keptDenotes.1,
                        ih tailItems keptTail tailResult keptTailResult
                          tailRemoved keptDenotes.2⟩

end InstantiationSemantic

end VisualProof.Rule
