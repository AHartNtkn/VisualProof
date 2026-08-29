import VisualProof.Diagram.ScopedRewrite
import VisualProof.Diagram.Semantics.Algebra

namespace VisualProof.Diagram

open VisualProof.Theory

theorem DiagramContext.denote_fill_iff
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (localIff : ∀ env : Values model holeWires,
      denoteRegion model env before ↔ denoteRegion model env after)
    (env : Values model outer) :
    denoteRegion model env (context.fill before) ↔
      denoteRegion model env (context.fill after) := by
  cases polarity : context.polarity with
  | positive =>
      constructor
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
  | negative =>
      constructor
      · have implication := context.denote_fill model after before
          (fun holeEnv => (localIff holeEnv).mpr) env
        rw [polarity] at implication
        exact implication
      · have implication := context.denote_fill model before after
          (fun holeEnv => (localIff holeEnv).mp) env
        rw [polarity] at implication
        exact implication

theorem CompletionPin.sound_iff
    {source target : Region outer}
    (description : CompletionPin.Description source target)
    (model : Model) (environment : Values model outer) :
    denoteRegion model environment source ↔
      denoteRegion model environment target := by
  have filled := description.context.denote_fill_iff
    (.mk description.locals description.items)
    (.mk description.locals
      (description.items.append (.cons
        (.identity description.signature 1 (fun _ => description.wire)) .nil)))
    (model := model) (fun siteEnv => by
      simp only [denoteRegion_mk]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        refine ⟨localEnv, (denoteItemSeq_append model
          (siteEnv.append localEnv) description.items _).mpr
            ⟨itemsDenote, ?_⟩⟩
        exact ⟨denoteItem_unary_identity model (siteEnv.append localEnv)
          description.wire, trivial⟩
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, (denoteItemSeq_append model
          (siteEnv.append localEnv) description.items _).mp itemsDenote |>.1⟩)
    environment
  simpa only [description.source_eq, description.target_eq] using filled

theorem CompletionPlan.sound_iff
    {source target : Region outer}
    (plan : CompletionPlan maximum source target)
    (model : Model) (environment : Values model outer) :
    denoteRegion model environment source ↔
      denoteRegion model environment target := by
  induction plan with
  | done => exact Iff.rfl
  | step pin _ _ rest induction =>
      exact (CompletionPin.sound_iff pin model environment).trans induction

end VisualProof.Diagram
