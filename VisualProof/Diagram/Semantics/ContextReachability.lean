import VisualProof.Diagram.Semantics.Algebra

namespace VisualProof.Diagram

open VisualProof
open VisualProof.Theory

namespace DiagramContext

/-- Environments that arise at a recursive context hole from one enclosing
environment. This is the semantic content of the context's inherited-wire
renaming. -/
def Reachable (context : DiagramContext outer holeWires)
    (outerEnv : Values model outer) (holeEnv : Values model holeWires) : Prop :=
  match context with
  | .hole => outerEnv = holeEnv
  | .cut locals _ _ child =>
      ∃ localEnv : Values model locals,
        child.Reachable (outerEnv.append localEnv) holeEnv

/-- A reachable hole environment agrees with the enclosing environment on
every inherited wire. -/
theorem Reachable.outerWire
    {context : DiagramContext outer holeWires}
    {outerEnv : Values model outer} {holeEnv : Values model holeWires}
    (reachable : context.Reachable outerEnv holeEnv) :
    Values.rename context.outerWire holeEnv = outerEnv := by
  induction context with
  | hole =>
      rw [reachable]
      apply Values.ext
      intro signature wire
      simp [DiagramContext.outerWire, WireRenaming.id]
  | cut locals before after child induction =>
      obtain ⟨localEnv, childReachable⟩ := reachable
      have childOuter := induction childReachable
      apply Values.ext
      intro signature wire
      simp only [DiagramContext.outerWire, Values.lookup_rename,
        WireRenaming.comp]
      rw [show holeEnv.lookup
          (child.outerWire (wire.appendLeft locals)) =
            (outerEnv.append localEnv).lookup (wire.appendLeft locals) by
        simpa only [Values.lookup_rename] using
          congrArg (fun values => values.lookup (wire.appendLeft locals))
            childOuter]
      exact Values.lookup_append_left outerEnv localEnv wire

/-- A semantic equivalence that holds for every environment reachable at a
context hole lifts through that context. -/
theorem fill_equiv_of_reachable
    (context : DiagramContext outer holeWires)
    (first second : Region holeWires)
    (model : Model) (outerEnv : Values model outer)
    (holeEquiv : ∀ holeEnv : Values model holeWires,
      context.Reachable outerEnv holeEnv →
        (denoteRegion model holeEnv first ↔
          denoteRegion model holeEnv second)) :
    denoteRegion model outerEnv (context.fill first) ↔
      denoteRegion model outerEnv (context.fill second) := by
  induction context with
  | hole => exact holeEquiv outerEnv rfl
  | cut locals before after child induction =>
      constructor
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, childNot, afterDenotes⟩ :=
          (denoteItemSeq_frame model (outerEnv.append localEnv)
            before after (.cut (child.fill first))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model
          (outerEnv.append localEnv) before after
          (.cut (child.fill second))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro secondDenotes
        apply childNot
        exact (induction first second (outerEnv.append localEnv)
          (fun holeEnv childReachable =>
            holeEquiv holeEnv ⟨localEnv, childReachable⟩)).mpr
          secondDenotes
      · rintro ⟨localEnv, items⟩
        obtain ⟨beforeDenotes, childNot, afterDenotes⟩ :=
          (denoteItemSeq_frame model (outerEnv.append localEnv)
            before after (.cut (child.fill second))).mp items
        refine ⟨localEnv, (denoteItemSeq_frame model
          (outerEnv.append localEnv) before after
          (.cut (child.fill first))).mpr
            ⟨beforeDenotes, ?_, afterDenotes⟩⟩
        intro firstDenotes
        apply childNot
        exact (induction first second (outerEnv.append localEnv)
          (fun holeEnv childReachable =>
            holeEquiv holeEnv ⟨localEnv, childReachable⟩)).mp
          firstDenotes

end DiagramContext

end VisualProof.Diagram
