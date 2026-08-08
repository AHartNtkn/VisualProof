import VisualProof.Concrete.Step
import VisualProof.Rule.DoubleCut
import VisualProof.Refinement.Implementation.DoubleCutIntroCompile
import VisualProof.Refinement.Implementation.DoubleCutIntroContext

namespace VisualProof.Refinement.Implementation.DoubleCutIntro

open VisualProof.Diagram
open VisualProof.Refinement.Implementation.DoubleCutTransport

theorem boundary_transport
    (input : Concrete.Diagram)
    (selection : Concrete.CheckedSelection input)
    (boundary : List (Fin input.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    (Concrete.doubleCutIntroWireTransport input selection).transportBoundary
      boundary = some boundary := by
  induction boundary with
  | nil => rfl
  | cons wire rest induction =>
      have wireRoot := rootScoped wire (by simp)
      have restRoot : ∀ tail, tail ∈ rest →
          (input.wires tail).scope = input.root := by
        intro tail member
        exact rootScoped tail (by simp [member])
      have image :
          (Concrete.doubleCutIntroWireTransport input selection).image? wire =
            some wire := by
        simp [Concrete.doubleCutIntroWireTransport,
          Concrete.WireTransport.byWireCount,
          Concrete.WireTransport.rootFiltered, DoubleCutTransport.wire,
          DoubleCutTransport.root]
        exact congrArg (Fin.castAdd 2) wireRoot
      rw [Concrete.WireTransport.transportBoundary, image,
        induction restRoot]
      rfl

def targetOpen_result_iso
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {result : Concrete.OperationReceipt source.diagram}
    {receipt : Concrete.Receipt source}
    (realizes : result.Realizes
      (Concrete.doubleCutIntroRaw source.checked.val.diagram selection)
      (Concrete.doubleCutIntroWireProvenance
        source.checked.val.diagram selection)
      (Concrete.doubleCutIntroWireTransport
        source.checked.val.diagram selection))
    (packed : result.toReceipt source = some receipt) :
    Concrete.OpenIso
      (targetOpen source.checked.val selection)
      receipt.target.checked.val := by
  unfold Concrete.OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i mapped transport
  cases packed
  have expected := realizes.transportBoundary_expected transport
  have identity := boundary_transport source.checked.val.diagram selection
    source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped
  have boundaryEq : source.checked.val.boundary =
      realizes.targetBoundary mapped := by
    exact Option.some.inj (identity.symm.trans expected)
  have canonicalToRaw : Concrete.OpenIso
      (targetOpen source.checked.val selection)
      (realizes.rawResultOpen mapped) := {
    diagram := Concrete.Iso.refl
      (Concrete.doubleCutIntroRaw source.checked.val.diagram selection)
    boundary := by
      change source.checked.val.boundary.map
          (FiniteEquiv.refl
            (Fin source.checked.val.diagram.wireCount)) =
        realizes.targetBoundary mapped
      have reflMap : (FiniteEquiv.refl
          (Fin source.checked.val.diagram.wireCount)).toFun = id := rfl
      rw [reflMap, List.map_id, boundaryEq]
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

/-- A successful concrete double-cut introduction realizes the structural
double-cut relation between the canonical checked elaborations. -/
theorem intro {arity : Nat} (source : Concrete.State arity)
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {result : Concrete.OperationReceipt source.diagram}
    {receipt : Concrete.Receipt source}
    (packed : result.toReceipt source = some receipt)
    (realizes : result.Realizes
      (Concrete.doubleCutIntroRaw source.checked.val.diagram selection)
      (Concrete.doubleCutIntroWireProvenance
        source.checked.val.diagram selection)
      (Concrete.doubleCutIntroWireTransport
        source.checked.val.diagram selection)) :
    Rule.DoubleCut
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) := by
  have rawWellFormed :
      (Concrete.doubleCutIntroRaw source.checked.val.diagram selection).WellFormed :=
    realizes.result_eq ▸ result.result.property
  let checkedTarget : Concrete.CheckedOpen :=
    ⟨targetOpen source.checked.val selection,
      targetOpen_wellFormed source.checked selection rawWellFormed⟩
  have rawStep : Rule.DoubleCut source.checked.elaborate
      checkedTarget.elaborate := by
    by_cases anchorRoot : selection.val.anchor =
        source.checked.val.diagram.root
    · simpa [checkedTarget] using
        DoubleCutIntroCompile.root_rule source.checked selection anchorRoot
          rawWellFormed
    · have rootNe : source.checked.val.diagram.root ≠
          selection.val.anchor := by
        intro equality
        exact anchorRoot equality.symm
      simpa [checkedTarget] using
        DoubleCutIntroContext.nested_rule source.checked selection rootNe
          rawWellFormed
  have concreteIso := targetOpen_result_iso source selection realizes packed
  have targetIso := concreteIso.elaborate_isomorphic
    (targetOpen_wellFormed source.checked selection rawWellFormed)
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

end VisualProof.Refinement.Implementation.DoubleCutIntro
