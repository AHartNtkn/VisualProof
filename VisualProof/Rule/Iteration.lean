import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Iteration

structure WireFreshening
    (sourceWires targetWires freshWires : Nat)
    (inherited : Fin sourceWires → Fin targetWires) where
  sourceOfFresh : Fin freshWires → Fin sourceWires
  sourceOfFresh_injective : Function.Injective sourceOfFresh
  wire : Fin sourceWires → Fin (targetWires + freshWires)
  wire_fresh : ∀ fresh,
    wire (sourceOfFresh fresh) = Fin.natAdd targetWires fresh
  wire_inherited : ∀ source,
    (∀ fresh, sourceOfFresh fresh ≠ source) →
      wire source = Fin.castAdd freshWires (inherited source)

theorem WireFreshening.env_eq
    (freshening : WireFreshening sourceWires targetWires freshWires inherited)
    (sourceEnv : Fin sourceWires → D)
    (targetEnv : Fin targetWires → D)
    (inheritedEq : targetEnv ∘ inherited = sourceEnv) :
    ∃ freshEnv : Fin freshWires → D,
      extendWireEnv targetEnv freshEnv ∘ freshening.wire = sourceEnv := by
  refine ⟨fun fresh => sourceEnv (freshening.sourceOfFresh fresh), ?_⟩
  funext source
  by_cases sourceFresh : ∃ fresh, freshening.sourceOfFresh fresh = source
  · rcases sourceFresh with ⟨fresh, sourceEq⟩
    subst source
    simp [extendWireEnv, freshening.wire_fresh]
  · change extendWireEnv targetEnv
      (fun fresh => sourceEnv (freshening.sourceOfFresh fresh))
      (freshening.wire source) = sourceEnv source
    rw [freshening.wire_inherited source (by
      intro fresh sourceEq
      exact sourceFresh ⟨fresh, sourceEq⟩)]
    simpa [extendWireEnv] using congrFun inheritedEq source

structure Base
    (source target : OpenDiagram arity) where
  interface : OpenDiagram arity
  ancestorWires : Nat
  anchorLocal : Nat
  descendantWires : Nat
  ancestorRels : RelCtx
  descendantRels : RelCtx
  outer :
    DiagramContext interface.externalClasses ancestorWires
      [] ancestorRels
  descendant :
    DiagramContext (ancestorWires + anchorLocal) descendantWires
      ancestorRels descendantRels
  selected :
    Region (ancestorWires + anchorLocal) ancestorRels
  remainder :
    Region descendantWires descendantRels
  copyLocal : Nat
  copyWires : WireFreshening
    (ancestorWires + anchorLocal) descendantWires copyLocal
    descendant.outerWire
  source_iso :
    OpenDiagramIso source
      (interface.withBody
        (outer.fill
          (Region.adjoinAt anchorLocal .nil
            (selected.conjoin
              (descendant.fill remainder)))))
  target_iso :
    OpenDiagramIso target
      (interface.withBody
        (outer.fill
          (Region.adjoinAt anchorLocal .nil
            (selected.conjoin
              (descendant.fill
                ((Region.adjoinAt copyLocal .nil
                    ((selected.renameWires copyWires.wire).renameRelations
                      descendant.outerRelation)).conjoin
                  remainder))))))

def Base.copy (step : Base source target) :
    Region step.descendantWires step.descendantRels :=
  Region.adjoinAt step.copyLocal .nil
    ((step.selected.renameWires step.copyWires.wire).renameRelations
      step.descendant.outerRelation)

noncomputable def Base.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Base source target)
    (targetIso : OpenDiagramIso target target') :
    Base source' target' where
  interface := step.interface
  ancestorWires := step.ancestorWires
  anchorLocal := step.anchorLocal
  descendantWires := step.descendantWires
  ancestorRels := step.ancestorRels
  descendantRels := step.descendantRels
  outer := step.outer
  descendant := step.descendant
  selected := step.selected
  remainder := step.remainder
  copyLocal := step.copyLocal
  copyWires := step.copyWires
  source_iso := sourceIso.symm.trans step.source_iso
  target_iso := targetIso.symm.trans step.target_iso

end Iteration

def Iteration : Rule :=
  symmetric fun source target =>
    Nonempty (Iteration.Base source target)

theorem Iteration.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : Iteration source target)
    (targetIso : OpenDiagramIso target target') :
    Iteration source' target' := by
  cases step with
  | inl forward =>
      rcases forward with ⟨forward⟩
      exact Or.inl ⟨Iteration.Base.iso sourceIso forward targetIso⟩
  | inr backward =>
      rcases backward with ⟨backward⟩
      exact Or.inr ⟨Iteration.Base.iso targetIso backward sourceIso⟩

theorem Iteration.symm
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Iteration source target) :
    Iteration target source := by
  exact step.elim Or.inr Or.inl

end VisualProof.Rule
