import VisualProof.Rule.Soundness.Comprehension.InstantiationDropCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Reinsert semantically certified occurrences into a compiled conjunction.
This is stated over the authoritative occurrence compiler: successful full and
filtered compilations fix the exact item sequences, while the caller supplies
only the denotation of items deliberately removed by the Boolean filter. -/
theorem compileOccurrencesWith_filter_denotes
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    (keep : Concrete.Elaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool)
    (model : Model)
    (environment : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    (allItems keptItems : ItemSeq  context.length rels)
    (allCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders occurrences = some allItems)
    (keptCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders (occurrences.filter keep) =
        some keptItems)
    (removedDenotes : ∀ occurrence,
      occurrence ∈ occurrences → keep occurrence = false →
      ∀ item,
        Concrete.Elaboration.compileOccurrenceWith?  diagram recurse
          context binders occurrence = some item →
        denoteItem model  environment relEnv item)
    (keptDenotes : denoteItemSeq model  environment relEnv keptItems) :
    denoteItemSeq model  environment relEnv allItems := by
  induction occurrences generalizing allItems keptItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        List.filter_nil] at allCompiled keptCompiled
      cases allCompiled
      trivial
  | cons occurrence tail ih =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at allCompiled
      cases headResult : Concrete.Elaboration.compileOccurrenceWith?
          diagram recurse context binders occurrence with
      | none => simp [headResult] at allCompiled
      | some headItem =>
          cases tailResult : Concrete.Elaboration.compileOccurrencesWith?
               diagram recurse context binders tail with
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
                        Concrete.Elaboration.compileOccurrenceWith?
                          diagram recurse context binders current = some item →
                        denoteItem model  environment relEnv item := by
                    intro current member
                    exact removedDenotes current (by simp [member])
                  exact ⟨headDenotes,
                    ih tailItems keptItems tailResult keptCompiled tailRemoved
                      keptDenotes⟩
              | true =>
                  simp only [List.filter_cons, kept, ↓reduceIte] at keptCompiled
                  simp only [Concrete.Elaboration.compileOccurrencesWith?,
                    headResult] at keptCompiled
                  cases keptTailResult :
                      Concrete.Elaboration.compileOccurrencesWith?
                        diagram recurse context binders
                          (tail.filter keep) with
                  | none => simp [keptTailResult] at keptCompiled
                  | some keptTail =>
                      simp [keptTailResult] at keptCompiled
                      subst keptItems
                      have tailRemoved : ∀ current,
                          current ∈ tail → keep current = false →
                          ∀ item,
                            Concrete.Elaboration.compileOccurrenceWith?
                               diagram recurse context binders
                                current = some item →
                            denoteItem model  environment relEnv item := by
                        intro current member
                        exact removedDenotes current (by simp [member])
                      exact ⟨keptDenotes.1,
                        ih tailItems keptTail tailResult keptTailResult
                          tailRemoved keptDenotes.2⟩

/-- Forget compiled occurrences rejected by a Boolean filter.  This is the
covariant companion to `compileOccurrencesWith_filter_denotes`; together the
two lemmas expose exactly the polarity split used when atom deletion crosses
cuts. -/
theorem compileOccurrencesWith_filter_denotes_of_all
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    (keep : Concrete.Elaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool)
    (model : Model)
    (environment : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    (allItems keptItems : ItemSeq  context.length rels)
    (allCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders occurrences = some allItems)
    (keptCompiled : Concrete.Elaboration.compileOccurrencesWith?
      diagram recurse context binders (occurrences.filter keep) =
        some keptItems)
    (allDenotes : denoteItemSeq model  environment relEnv allItems) :
    denoteItemSeq model  environment relEnv keptItems := by
  induction occurrences generalizing allItems keptItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        List.filter_nil] at allCompiled keptCompiled
      cases keptCompiled
      trivial
  | cons occurrence tail ih =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at allCompiled
      cases headResult : Concrete.Elaboration.compileOccurrenceWith?
          diagram recurse context binders occurrence with
      | none => simp [headResult] at allCompiled
      | some headItem =>
          cases tailResult : Concrete.Elaboration.compileOccurrencesWith?
               diagram recurse context binders tail with
          | none => simp [headResult, tailResult] at allCompiled
          | some tailItems =>
              simp [headResult, tailResult] at allCompiled
              subst allItems
              cases kept : keep occurrence with
              | false =>
                  simp only [List.filter_cons, kept, Bool.false_eq_true,
                    ↓reduceIte] at keptCompiled
                  exact ih tailItems keptItems tailResult keptCompiled
                    allDenotes.2
              | true =>
                  simp only [List.filter_cons, kept, ↓reduceIte] at keptCompiled
                  simp only [Concrete.Elaboration.compileOccurrencesWith?,
                    headResult] at keptCompiled
                  cases keptTailResult :
                      Concrete.Elaboration.compileOccurrencesWith?
                        diagram recurse context binders
                          (tail.filter keep) with
                  | none => simp [keptTailResult] at keptCompiled
                  | some keptTail =>
                      simp [keptTailResult] at keptCompiled
                      subst keptItems
                      exact ⟨allDenotes.1,
                        ih tailItems keptTail tailResult keptTailResult
                          allDenotes.2⟩

end InstantiationSemantic

end VisualProof.Rule
