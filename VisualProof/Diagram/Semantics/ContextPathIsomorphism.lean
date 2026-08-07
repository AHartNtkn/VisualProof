import VisualProof.Diagram.ContextPathIsomorphism
import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

/-- Semantic form of `fill_eq_mk_filledRootItems`. -/
theorem Region.ContextPath.denote_fill_iff_filledRootItems
    {items : ItemSeq  wires rels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (proper : path ≠ [])
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels)
    (model : Model)
    (environment : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model  environment relEnv
        (witness.toFocus.context.fill replacement) ↔
      denoteItemSeq model  environment relEnv
        (witness.filledRootItems proper replacement) := by
  rw [witness.fill_eq_mk_filledRootItems proper replacement]
  simp only [denoteRegion_mk, extendWireEnv_zero]
  constructor
  · rintro ⟨_, denotation⟩
    exact denotation
  · intro denotation
    exact ⟨Fin.elim0, denotation⟩

/-- Appending root siblings on the right represents conjunction with those
siblings.  This semantic form is insensitive to the compiler's chosen sibling
order and retains all local witnesses of the focused replacement. -/
theorem Region.ContextPath.appendRootItemsRight_fill_equiv
    {items suffix : ItemSeq  wires rels}
    {index : Nat} {rest : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest))
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels)
    (model : Model)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model  env relEnv
        ((Region.mk 0 suffix).conjoin
          (witness.toFocus.context.fill replacement)) ↔
      denoteRegion model  env relEnv
        ((witness.appendRootItemsRight suffix).toFocus.context.fill
          (witness.appendRootItemsRightReplacement replacement)) := by
  cases witness with
  | cut focus atIndex isCut nested =>
      have leftEnv : env ∘ Region.conjoinLeftWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinLeftWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinLeftWire, Fin.addCases_left]
      have rightEnv : env ∘ Region.conjoinRightWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinRightWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinRightWire, Fin.addCases_left]
      simp [Region.ContextPath.toFocus,
        Region.ContextPath.appendRootItemsRight, DiagramContext.fill,
        Region.ContextPath.appendRootItemsRightReplacement,
        denoteRegion_mk, extendWireEnv_zero, ItemSeq.Focus.appendAfter,
        denoteItemSeq_append, denoteItemSeq_renameWires, leftEnv, rightEnv,
        and_assoc, and_left_comm, and_comm]
  | bubble focus atIndex isBubble nested =>
      have leftEnv : env ∘ Region.conjoinLeftWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinLeftWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinLeftWire, Fin.addCases_left]
      have rightEnv : env ∘ Region.conjoinRightWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinRightWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinRightWire, Fin.addCases_left]
      simp [Region.ContextPath.toFocus,
        Region.ContextPath.appendRootItemsRight, DiagramContext.fill,
        Region.ContextPath.appendRootItemsRightReplacement,
        denoteRegion_mk, extendWireEnv_zero, ItemSeq.Focus.appendAfter,
        denoteItemSeq_append, denoteItemSeq_renameWires, leftEnv, rightEnv,
        and_assoc, and_left_comm, and_comm]

/-- Transport a semantic equivalence between two source presentations across
isomorphisms of both endpoints. -/
theorem RegionIso.transport_equivalence
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBefore sourceAfter : Region  sourceWires rels}
    {targetBefore targetAfter : Region  targetWires rels}
    (beforeIso : RegionIso  wire rels sourceBefore targetBefore)
    (afterIso : RegionIso  wire rels sourceAfter targetAfter)
    (sourceEquivalent :
      ∀ (model : Model)
        (env : Fin sourceWires → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteRegion model  env relEnv sourceBefore ↔
          denoteRegion model  env relEnv sourceAfter)
    (model : Model)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model  targetEnv relEnv targetBefore ↔
      denoteRegion model  targetEnv relEnv targetAfter := by
  let sourceEnv : Fin sourceWires → model.Carrier :=
    fun index => targetEnv (wire index)
  have environments : EnvironmentsAgree wire sourceEnv targetEnv := by
    intro index
    rfl
  exact (beforeIso.denotation model  sourceEnv targetEnv relEnv
    environments).symm.trans
      ((sourceEquivalent model  sourceEnv relEnv).trans
        (afterIso.denotation model  sourceEnv targetEnv relEnv
          environments))

end VisualProof.Diagram
