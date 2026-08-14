import VisualProof.Diagram.Context
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof

theorem denoteItemSeq_append
    (model : Model) (env : Values model wires)
    (first second : ItemSeq wires) :
    denoteItemSeq model env (first.append second) ↔
      denoteItemSeq model env first ∧ denoteItemSeq model env second := by
  let regionMotive : ∀ context : List Theory.Sig, Region context → Prop :=
    fun _ _ => True
  let itemMotive : ∀ context : List Theory.Sig, Item context → Prop :=
    fun _ _ => True
  let itemsMotive := fun (context : List Theory.Sig)
      (items : ItemSeq context) =>
    ∀ (env : Values model context) (second : ItemSeq context),
      denoteItemSeq model env (items.append second) ↔
        denoteItemSeq model env items ∧ denoteItemSeq model env second
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro env second; simp)
    (by
      intro _ head tail _ tailIH env second
      simp only [ItemSeq.append, denoteItemSeq_cons]
      rw [tailIH env second]
      constructor
      · rintro ⟨headDenotes, tailDenotes, secondDenotes⟩
        exact ⟨⟨headDenotes, tailDenotes⟩, secondDenotes⟩
      · rintro ⟨⟨headDenotes, tailDenotes⟩, secondDenotes⟩
        exact ⟨headDenotes, tailDenotes, secondDenotes⟩)
    first env second

theorem denoteItemSeq_frame
    (model : Model) (env : Values model wires)
    (before after : ItemSeq wires) (item : Item wires) :
    denoteItemSeq model env (before.append (.cons item after)) ↔
      denoteItemSeq model env before ∧
        denoteItem model env item ∧ denoteItemSeq model env after := by
  rw [denoteItemSeq_append]
  simp only [denoteItemSeq_cons]

private theorem succ_even_implies_odd {n : Nat} (h : (n + 1) % 2 = 0) :
    n % 2 = 1 := by omega

private theorem succ_odd_implies_even {n : Nat} (h : (n + 1) % 2 = 1) :
    n % 2 = 0 := by omega

private theorem context_polarity
    (context : DiagramContext outer hole)
    (model : Model) (before after : Region hole)
    (localImplication : ∀ holeEnv : Values model hole,
      denoteRegion model holeEnv before →
        denoteRegion model holeEnv after) :
    (∀ (outerEnv : Values model outer), context.cutDepth % 2 = 0 →
      denoteRegion model outerEnv (context.fill before) →
        denoteRegion model outerEnv (context.fill after)) ∧
    (∀ (outerEnv : Values model outer), context.cutDepth % 2 = 1 →
      denoteRegion model outerEnv (context.fill after) →
        denoteRegion model outerEnv (context.fill before)) := by
  induction context with
  | hole =>
      constructor
      · intro env _ denotes
        exact localImplication env denotes
      · intro _ odd _
        simp [DiagramContext.cutDepth] at odd
  | cut locals beforeItems afterItems child induction =>
      constructor
      · intro env even sourceDenotes
        rcases sourceDenotes with ⟨localEnv, itemsDenote⟩
        rcases (denoteItemSeq_frame model (env.append localEnv)
          beforeItems afterItems (.cut (child.fill before))).mp itemsDenote with
          ⟨beforeDenotes, childDenotes, afterDenotes⟩
        refine ⟨localEnv, (denoteItemSeq_frame model (env.append localEnv)
          beforeItems afterItems (.cut (child.fill after))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro afterChild
        apply childDenotes
        exact (induction before after localImplication).2
          (env.append localEnv) (succ_even_implies_odd even) afterChild
      · intro env odd targetDenotes
        rcases targetDenotes with ⟨localEnv, itemsDenote⟩
        rcases (denoteItemSeq_frame model (env.append localEnv)
          beforeItems afterItems (.cut (child.fill after))).mp itemsDenote with
          ⟨beforeDenotes, childDenotes, afterDenotes⟩
        refine ⟨localEnv, (denoteItemSeq_frame model (env.append localEnv)
          beforeItems afterItems (.cut (child.fill before))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro beforeChild
        apply childDenotes
        exact (induction before after localImplication).1
          (env.append localEnv) (succ_odd_implies_even odd) beforeChild

theorem DiagramContext.denote_fill
    (context : DiagramContext outer holeWires)
    (model : Model) (before after : Region holeWires)
    (localImplication : ∀ holeEnv : Values model holeWires,
      denoteRegion model holeEnv before →
        denoteRegion model holeEnv after)
    (outerEnv : Values model outer) :
    match context.polarity with
    | .positive =>
        denoteRegion model outerEnv (context.fill before) →
          denoteRegion model outerEnv (context.fill after)
    | .negative =>
        denoteRegion model outerEnv (context.fill after) →
          denoteRegion model outerEnv (context.fill before) := by
  by_cases even : context.cutDepth % 2 = 0
  · simp only [DiagramContext.polarity, even, if_true]
    exact (context_polarity context model before after localImplication).1
      outerEnv even
  · have bound : context.cutDepth % 2 < 2 := Nat.mod_lt _ (by omega)
    have odd : context.cutDepth % 2 = 1 := by omega
    simp only [DiagramContext.polarity, even, if_false]
    exact (context_polarity context model before after localImplication).2
      outerEnv odd

end VisualProof.Diagram
