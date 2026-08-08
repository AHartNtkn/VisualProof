import VisualProof.Concrete.Step
import VisualProof.Refinement.Implementation.DoubleCutElimContext

namespace VisualProof.Refinement.Implementation.DoubleCutElim

open VisualProof
open VisualProof.Diagram
open VisualProof.Refinement.Implementation.DoubleCutElimTransport

private def concreteIsoOfEq
    {source target : Concrete.Diagram}
    (equality : source = target) : Concrete.Iso source target := by
  subst target
  exact Concrete.Iso.refl source

@[simp] private theorem concreteIsoOfEq_wires_val
    {source target : Concrete.Diagram}
    (equality : source = target) (wire : Fin source.wireCount) :
    ((concreteIsoOfEq equality).wires wire).val = wire.val := by
  subst target
  rfl

/-- The canonical promoted open target retains the source boundary in its
original order. -/
def targetOpen
    {arity : Nat}
    (source : Concrete.State arity)
    {outer : Fin source.checked.val.diagram.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.checked.val.diagram outer raw) :
    Concrete.OpenDiagram where
  diagram := Target trace
  boundary := source.checked.val.boundary

def targetOpenWellFormed
    {arity : Nat}
    (source : Concrete.State arity)
    {outer : Fin source.checked.val.diagram.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.checked.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed) :
    (targetOpen source trace).WellFormed := by
  by_cases root : trace.target = source.checked.val.diagram.root
  · simpa [targetOpen,
      DoubleCutElimRoot.targetOpen] using
      DoubleCutElimRoot.targetOpenWellFormed source.checked trace root
        targetWellFormed
  · have rootNe : trace.target ≠ source.checked.val.diagram.root := root
    simpa [targetOpen,
      DoubleCutElimContext.targetOpen] using
      DoubleCutElimContext.targetOpenWellFormed source.checked trace
        targetWellFormed

def checkedTarget
    {arity : Nat}
    (source : Concrete.State arity)
    {outer : Fin source.checked.val.diagram.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.checked.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed) : Concrete.CheckedOpen :=
  ⟨targetOpen source trace,
    targetOpenWellFormed source trace targetWellFormed⟩

/-- Exact ordered-interface identification of the canonical promoted target
with the actual packed receipt target. -/
noncomputable def targetOpen_result_iso
    {arity : Nat}
    (source : Concrete.State arity)
    (outer : Fin source.checked.val.diagram.regionCount)
    {raw : Concrete.Diagram}
    (rawSuccess : Concrete.doubleCutElimRaw?
      source.checked.val.diagram outer = some raw)
    {result : Concrete.OperationReceipt source.diagram}
    {receipt : Concrete.Receipt source}
    (realizes : result.Realizes raw
      (Concrete.doubleCutElimWireProvenance rawSuccess)
      (Concrete.doubleCutElimWireTransport rawSuccess))
    (packed : result.toReceipt source = some receipt) :
    Concrete.OpenIso
      (targetOpen source (Concrete.doubleCutElimTrace rawSuccess))
      receipt.target.checked.val := by
  let trace := Concrete.doubleCutElimTrace rawSuccess
  unfold Concrete.OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i mapped transport
  cases packed
  have expected := realizes.transportBoundary_expected transport
  have rawEq : raw = Target trace := trace.promotion.raw_eq_diagram
  let diagramIso : Concrete.Iso (Target trace) raw :=
    concreteIsoOfEq rawEq.symm
  have boundaryEq :
      source.checked.val.boundary.map diagramIso.wires =
        realizes.targetBoundary mapped := by
    have targetWellFormed : (Target trace).WellFormed := by
      rw [← rawEq]
      exact realizes.result_eq ▸ result.result.property
    have exactTransport :
        (Concrete.doubleCutElimWireTransport rawSuccess).transportBoundary
            source.checked.val.boundary =
          some (source.checked.val.boundary.map diagramIso.wires) := by
      apply Concrete.WireTransport.transportBoundary_eq_map
      intro wire member
      have canonicalRootScoped :
          ((Target trace).wires wire).scope = (Target trace).root :=
        (targetOpenWellFormed source trace targetWellFormed
          ).boundary_is_root_scoped wire member
      have rawRootScoped :
          (raw.wires (diagramIso.wires wire)).scope = raw.root := by
        calc
          (raw.wires (diagramIso.wires wire)).scope =
              diagramIso.regions ((Target trace).wires wire).scope :=
            (diagramIso.wire_scope_eq wire).symm
          _ = diagramIso.regions (Target trace).root :=
            congrArg diagramIso.regions canonicalRootScoped
          _ = raw.root := diagramIso.root_eq
      have mappedEq : Fin.cast
          (Concrete.doubleCutElimRaw?_wireCount rawSuccess).symm wire =
          diagramIso.wires wire := by
        apply Fin.ext
        simpa [diagramIso] using
          (concreteIsoOfEq_wires_val rawEq.symm wire).symm
      simpa [Concrete.doubleCutElimWireTransport,
        Concrete.WireTransport.byWireCount,
        Concrete.WireTransport.rootFiltered, diagramIso,
        concreteIsoOfEq, mappedEq] using rawRootScoped
    exact Option.some.inj (exactTransport.symm.trans expected)
  have canonicalToRaw : Concrete.OpenIso
      (targetOpen source trace) (realizes.rawResultOpen mapped) := {
    diagram := diagramIso
    boundary := boundaryEq
  }
  exact canonicalToRaw.trans (realizes.rawResultOpenIso mapped)

private theorem castArity_trans
    (diagram : OpenDiagram sourceArity)
    (first : sourceArity = middleArity)
    (second : middleArity = targetArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst middleArity
  subst targetArity
  rfl

private theorem rule_castArity
    (arityEq : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (step : Rule.DoubleCut source target) :
    Rule.DoubleCut (source.castArity arityEq)
      (target.castArity arityEq) := by
  subst targetArity
  exact step

/-- A successful concrete double-cut elimination realizes the structural
double-cut relation between the canonical checked elaborations. -/
theorem elim
    {arity : Nat}
    (source : Concrete.State arity)
    (outer : Fin source.checked.val.diagram.regionCount)
    {raw : Concrete.Diagram}
    (rawSuccess : Concrete.doubleCutElimRaw?
      source.checked.val.diagram outer = some raw)
    {result : Concrete.OperationReceipt source.diagram}
    {receipt : Concrete.Receipt source}
    (packed : result.toReceipt source = some receipt)
    (realizes : result.Realizes raw
      (Concrete.doubleCutElimWireProvenance rawSuccess)
      (Concrete.doubleCutElimWireTransport rawSuccess)) :
    Rule.DoubleCut
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) := by
  let trace := Concrete.doubleCutElimTrace rawSuccess
  have rawWellFormed : raw.WellFormed :=
    realizes.result_eq ▸ result.result.property
  have targetWellFormed : (Target trace).WellFormed := by
    change trace.promotion.diagram.WellFormed
    rw [← trace.promotion.raw_eq_diagram]
    exact rawWellFormed
  let target := checkedTarget source trace targetWellFormed
  have rawStep : Rule.DoubleCut source.checked.elaborate
      target.elaborate := by
    by_cases root : trace.target = source.checked.val.diagram.root
    · have step := DoubleCutElimRoot.root_rule source.checked trace root
          targetWellFormed
      simpa [target, checkedTarget, targetOpen,
        DoubleCutElimRoot.checkedTarget,
        DoubleCutElimRoot.targetOpen] using step
    · have step := DoubleCutElimContext.nested_rule source.checked trace
          root targetWellFormed
      simpa [target, checkedTarget, targetOpen,
        DoubleCutElimContext.checkedTarget,
        DoubleCutElimContext.targetOpen] using step
  have concreteIso := targetOpen_result_iso source outer rawSuccess realizes
    packed
  have targetIso : OpenDiagramIso target.elaborate
      (receipt.target.checked.elaborate.castArity
        concreteIso.boundary_length_eq.symm) := by
    simpa [target, checkedTarget] using concreteIso.elaborate_isomorphic
      (targetOpenWellFormed source trace targetWellFormed)
      receipt.target.checked.property
  have boundaryStep := Rule.DoubleCut.iso
    (OpenDiagramIso.refl source.checked.elaborate) rawStep targetIso
  have castStep := rule_castArity source.boundary_length boundaryStep
  have arityProof : concreteIso.boundary_length_eq.symm.trans
        source.boundary_length = receipt.target.boundary_length :=
    Subsingleton.elim _ _
  have targetEq :
      ((receipt.target.checked.elaborate.castArity
        concreteIso.boundary_length_eq.symm).castArity
          source.boundary_length) =
        receipt.target.checked.elaborate.castArity
          receipt.target.boundary_length := by
    rw [castArity_trans, arityProof]
  have targetCastIso : OpenDiagramIso
      ((receipt.target.checked.elaborate.castArity
        concreteIso.boundary_length_eq.symm).castArity
          source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) := by
    rw [targetEq]
    exact OpenDiagramIso.refl _
  exact Rule.DoubleCut.iso
    (OpenDiagramIso.refl
      (source.checked.elaborate.castArity source.boundary_length))
    castStep targetCastIso

end VisualProof.Refinement.Implementation.DoubleCutElim
