import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Iteration

/-- A local copy may keep inherited wires or allocate one fresh descendant
wire for a selected source wire. -/
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

/-- The local iteration law.  All source/target endpoint and context ownership
lives in `NestedContextReplacement`; this record owns only the copied region
and its source-derived wire freshening. -/
structure Local
    {ancestorWires anchorLocal descendantWires : Nat}
    {ancestorRels descendantRels : RelCtx}
    (descendant : DiagramContext (ancestorWires + anchorLocal)
      descendantWires ancestorRels descendantRels)
    (selected : Region (ancestorWires + anchorLocal) ancestorRels)
    (before after : Region descendantWires descendantRels) where
  copyLocal : Nat
  copyWires : WireFreshening
    (ancestorWires + anchorLocal) descendantWires copyLocal
    descendant.outerWire
  after_eq : after =
    ((Region.adjoinAt copyLocal .nil
      ((selected.renameWires copyWires.wire).renameRelations
        descendant.outerRelation)).conjoin before)

def Local.copy
    (descendant : DiagramContext (ancestorWires + anchorLocal)
      descendantWires ancestorRels descendantRels)
    (selected : Region (ancestorWires + anchorLocal) ancestorRels)
    (remainder : Region descendantWires descendantRels)
    (copyLocal : Nat)
    (copyWires : WireFreshening
      (ancestorWires + anchorLocal) descendantWires copyLocal
      descendant.outerWire) :
    Local descendant selected remainder
      ((Region.adjoinAt copyLocal .nil
        ((selected.renameWires copyWires.wire).renameRelations
          descendant.outerRelation)).conjoin remainder) where
  copyLocal := copyLocal
  copyWires := copyWires
  after_eq := rfl

end Iteration

def Iteration : Rule :=
  symmetric (NestedContextual Iteration.Local)

theorem Iteration.iso
    {arity : Nat}
    {source source' target target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : Iteration source target)
    (targetIso : OpenDiagramIso target target') :
    Iteration source' target' := by
  cases step with
  | inl forward =>
      rcases forward with ⟨replacement, ⟨localEvidence⟩⟩
      exact Or.inl ⟨replacement.iso sourceIso.symm targetIso,
        ⟨localEvidence⟩⟩
  | inr backward =>
      rcases backward with ⟨replacement, ⟨localEvidence⟩⟩
      exact Or.inr ⟨replacement.iso targetIso.symm sourceIso,
        ⟨localEvidence⟩⟩

theorem Iteration.symm
    {arity : Nat}
    {source target : OpenDiagram arity}
    (step : Iteration source target) :
    Iteration target source := by
  exact step.elim Or.inr Or.inl

end VisualProof.Rule
