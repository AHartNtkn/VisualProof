import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

open VisualProof
open VisualProof.Theory

namespace DiagramContext

/-- Canonical embedding of the relations visible outside a context into the
relation environment visible at its hole. -/
def outerRelation :
    DiagramContext signature outerWires holeWires outerRels holeRels →
      RelationRenaming outerRels holeRels
  | .hole => fun relation => relation
  | .cut _ _ _ child => child.outerRelation
  | .bubble _ _ _ _ child => fun relation =>
      child.outerRelation ⟨relation.index.succ, relation.hasArity⟩

/-- Environments that can actually reach a context hole while evaluating its
surrounding region.  Unlike an unconstrained hole valuation, inherited wire
and relation values are tied to the outer valuation. -/
def Reachable
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (outerEnv : Fin outerWires → D) (outerRelEnv : RelEnv D outerRels)
    (holeEnv : Fin holeWires → D) (holeRelEnv : RelEnv D holeRels) : Prop :=
  match ctx with
  | .hole => outerEnv = holeEnv ∧ outerRelEnv = holeRelEnv
  | .cut localWires _ _ child =>
      ∃ localEnv : Fin localWires → D,
        child.Reachable (extendWireEnv outerEnv localEnv) outerRelEnv
          holeEnv holeRelEnv
  | .bubble localWires _ _ arity child =>
      ∃ (localEnv : Fin localWires → D) (relation : Relation D arity),
        child.Reachable (extendWireEnv outerEnv localEnv)
          (relation, outerRelEnv) holeEnv holeRelEnv

/-- Every reachable hole valuation retains all outer wire values. -/
theorem Reachable.outerWire
    {ctx : DiagramContext signature outerWires holeWires outerRels holeRels}
    {outerEnv : Fin outerWires → D} {outerRelEnv : RelEnv D outerRels}
    {holeEnv : Fin holeWires → D} {holeRelEnv : RelEnv D holeRels}
    (reachable : ctx.Reachable outerEnv outerRelEnv holeEnv holeRelEnv) :
    holeEnv ∘ ctx.outerWire = outerEnv := by
  induction ctx with
  | hole =>
      obtain ⟨rfl, _⟩ := reachable
      rfl
  | cut localWires before after child induction =>
      obtain ⟨localEnv, childReachable⟩ := reachable
      have childOuter := induction childReachable
      funext index
      change holeEnv (child.outerWire (Fin.castAdd localWires index)) =
        outerEnv index
      rw [show holeEnv (child.outerWire (Fin.castAdd localWires index)) =
          extendWireEnv outerEnv localEnv (Fin.castAdd localWires index) from
        congrFun childOuter (Fin.castAdd localWires index)]
      simp [extendWireEnv]
  | bubble localWires before after arity child induction =>
      obtain ⟨localEnv, relation, childReachable⟩ := reachable
      have childOuter := induction childReachable
      funext index
      change holeEnv (child.outerWire (Fin.castAdd localWires index)) =
        outerEnv index
      rw [show holeEnv (child.outerWire (Fin.castAdd localWires index)) =
          extendWireEnv outerEnv localEnv (Fin.castAdd localWires index) from
        congrFun childOuter (Fin.castAdd localWires index)]
      simp [extendWireEnv]

/-- Every reachable hole relation valuation retains all outer relations. -/
theorem Reachable.outerRelation
    {ctx : DiagramContext signature outerWires holeWires outerRels holeRels}
    {outerEnv : Fin outerWires → D} {outerRelEnv : RelEnv D outerRels}
    {holeEnv : Fin holeWires → D} {holeRelEnv : RelEnv D holeRels}
    (reachable : ctx.Reachable outerEnv outerRelEnv holeEnv holeRelEnv) :
    RelEnv.Agrees ctx.outerRelation outerRelEnv holeRelEnv := by
  induction ctx with
  | hole =>
      obtain ⟨_, rfl⟩ := reachable
      intro arity relation
      rfl
  | cut localWires before after child induction =>
      obtain ⟨localEnv, childReachable⟩ := reachable
      exact induction childReachable
  | bubble localWires before after arity child induction =>
      obtain ⟨localEnv, relationValue, childReachable⟩ := reachable
      have childAgrees := induction childReachable
      intro relationArity relation
      exact childAgrees relationArity
        ⟨relation.index.succ, relation.hasArity⟩

/-- A local equivalence need only hold at valuations that can actually reach
the hole; it then lifts through the surrounding context. -/
theorem fill_equiv_of_reachable
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin outerWires → model.Carrier)
    (outerRelEnv : RelEnv model.Carrier outerRels)
    (holeEquiv : ∀ holeEnv holeRelEnv,
      ctx.Reachable outerEnv outerRelEnv holeEnv holeRelEnv →
        (denoteRegion model named holeEnv holeRelEnv first ↔
          denoteRegion model named holeEnv holeRelEnv second)) :
    denoteRegion model named outerEnv outerRelEnv (ctx.fill first) ↔
      denoteRegion model named outerEnv outerRelEnv (ctx.fill second) := by
  induction ctx with
  | hole =>
      exact holeEquiv outerEnv outerRelEnv ⟨rfl, rfl⟩
  | cut localWires before after child induction =>
      constructor
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, childNot, afterDenotes⟩ :=
          (denoteItemSeq_frame model named
            (extendWireEnv outerEnv localEnv) outerRelEnv before after
            (.cut (child.fill first))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv outerEnv localEnv) outerRelEnv before after
          (.cut (child.fill second))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro secondDenotes
        apply childNot
        exact (induction first second
          (extendWireEnv outerEnv localEnv) outerRelEnv
          (fun holeEnv holeRelEnv childReachable =>
            holeEquiv holeEnv holeRelEnv ⟨localEnv, childReachable⟩)).mpr
          secondDenotes
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, childNot, afterDenotes⟩ :=
          (denoteItemSeq_frame model named
            (extendWireEnv outerEnv localEnv) outerRelEnv before after
            (.cut (child.fill second))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv outerEnv localEnv) outerRelEnv before after
          (.cut (child.fill first))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro firstDenotes
        apply childNot
        exact (induction first second
          (extendWireEnv outerEnv localEnv) outerRelEnv
          (fun holeEnv holeRelEnv childReachable =>
            holeEquiv holeEnv holeRelEnv ⟨localEnv, childReachable⟩)).mp
          firstDenotes
  | bubble localWires before after arity child induction =>
      constructor
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, ⟨relationValue, childDenotes⟩,
            afterDenotes⟩ :=
          (denoteItemSeq_frame model named
            (extendWireEnv outerEnv localEnv) outerRelEnv before after
            (.bubble arity (child.fill first))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv outerEnv localEnv) outerRelEnv before after
          (.bubble arity (child.fill second))).mpr
            ⟨beforeDenotes, ⟨relationValue, ?_⟩, afterDenotes⟩⟩
        exact (induction first second
          (extendWireEnv outerEnv localEnv)
          (relationValue, outerRelEnv)
          (fun holeEnv holeRelEnv childReachable =>
            holeEquiv holeEnv holeRelEnv
              ⟨localEnv, relationValue, childReachable⟩)).mp childDenotes
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, ⟨relationValue, childDenotes⟩,
            afterDenotes⟩ :=
          (denoteItemSeq_frame model named
            (extendWireEnv outerEnv localEnv) outerRelEnv before after
            (.bubble arity (child.fill second))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model named
          (extendWireEnv outerEnv localEnv) outerRelEnv before after
          (.bubble arity (child.fill first))).mpr
            ⟨beforeDenotes, ⟨relationValue, ?_⟩, afterDenotes⟩⟩
        exact (induction first second
          (extendWireEnv outerEnv localEnv)
          (relationValue, outerRelEnv)
          (fun holeEnv holeRelEnv childReachable =>
            holeEquiv holeEnv holeRelEnv
              ⟨localEnv, relationValue, childReachable⟩)).mpr childDenotes

end DiagramContext

end VisualProof.Diagram
