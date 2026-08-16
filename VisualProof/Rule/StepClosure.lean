import VisualProof.Rule.Step

namespace VisualProof.Rule

open Diagram

namespace StepClosure

noncomputable section

theorem isoSource
    (sourceIso : OpenDiagramIso source source')
    (steps : Relation.TransGen Step source target) :
    Relation.TransGen Step source' target := by
  induction steps with
  | single step =>
      exact .single (Step.iso sourceIso step (OpenDiagramIso.refl _))
  | tail _ step induction =>
      exact .tail induction step

theorem isoTarget
    (steps : Relation.TransGen Step source target)
    (targetIso : OpenDiagramIso target target') :
    Relation.TransGen Step source target' := by
  induction steps with
  | single step =>
      exact .single (Step.iso (OpenDiagramIso.refl _) step targetIso)
  | tail previous step _ =>
      exact .tail previous
        (Step.iso (OpenDiagramIso.refl _) step targetIso)

theorem iso
    (sourceIso : OpenDiagramIso source source')
    (steps : Relation.TransGen Step source target)
    (targetIso : OpenDiagramIso target target') :
    Relation.TransGen Step source' target' :=
  isoTarget (isoSource sourceIso steps) targetIso

theorem prepend
    (step : Step source middle)
    (steps : Relation.TransGen Step middle target) :
    Relation.TransGen Step source target :=
  (Relation.TransGen.single step).trans steps

theorem append
    (steps : Relation.TransGen Step source middle)
    (step : Step middle target) :
    Relation.TransGen Step source target :=
  steps.tail step

end

end StepClosure

end VisualProof.Rule
