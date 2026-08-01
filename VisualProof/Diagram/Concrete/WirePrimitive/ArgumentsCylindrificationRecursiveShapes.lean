import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveHoles

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

/-- Ordinary projection of a uniform region. -/
def recursiveOrdinary :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicItemSeq definitions arguments context
  | .mk ordinary _ => ordinary

/-- Regard a compiled item sequence as a uniform sequence containing only
ordinary leaves. -/
def recursiveLeafItems :
    ItemSeq definitions context →
      UniformIntrinsicItemSeq definitions arguments context
  | .nil => .nil
  | .cons head tail => .cons (.leaf head) (recursiveLeafItems tail)

/-- The ordinary item sequence obtained by removing every direct matching
application from one compiled sequence. -/
def recursiveAbstractOrdinaryItems
    (head : Var context (.rel arguments)) :
    ItemSeq definitions context →
      UniformIntrinsicItemSeq definitions arguments context
  | .nil => .nil
  | .cons item tail =>
      let rest := recursiveAbstractOrdinaryItems head tail
      match item with
      | .atom atomHead values =>
          match UniformIntrinsicRegion.matchedHeadArguments? head atomHead values with
          | some _ => rest
          | none => .cons (.leaf (.atom atomHead values)) rest
      | .named definition values =>
          .cons (.leaf (.named definition values)) rest
      | .identity signature ports atLeastTwo =>
          .cons (.leaf (.identity signature ports atLeastTwo)) rest
      | .cut body =>
          .cons (.cut (UniformIntrinsicRegion.abstractApplied head body)) rest
      | .bind signature body =>
          .cons (.bind signature
            (UniformIntrinsicRegion.abstractApplied head.there body)) rest

/-- The explicit ordinary-item recursion is definitionally faithful to the
authoritative uniform abstraction. -/
theorem recursiveOrdinary_abstractAppliedItems
    (head : Var context (.rel arguments)) :
    ∀ items : ItemSeq definitions context,
      recursiveOrdinary
          (UniformIntrinsicRegion.abstractAppliedItems head items) =
        recursiveAbstractOrdinaryItems head items
  | .nil => rfl
  | .cons item tail => by
      have induction := recursiveOrdinary_abstractAppliedItems head tail
      cases abstracted :
          UniformIntrinsicRegion.abstractAppliedItems head tail with
      | mk ordinary holes =>
          rw [abstracted] at induction
          change ordinary = _ at induction
          cases item with
          | atom atomHead values =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              cases matched : UniformIntrinsicRegion.matchedHeadArguments?
                  head atomHead values with
              | none =>
                simp only [matched, recursiveAbstractOrdinaryItems]
                exact congrArg
                  (UniformIntrinsicItemSeq.cons (.leaf (.atom atomHead values)))
                  induction
              | some matchedValues =>
                simp only [matched, recursiveAbstractOrdinaryItems]
                exact induction
          | named definition values =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.leaf (.named definition values)) ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.leaf (.named definition values))) induction
          | identity signature ports atLeastTwo =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.leaf (.identity signature ports atLeastTwo)) ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.leaf (.identity signature ports atLeastTwo))) induction
          | cut body =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.cut (UniformIntrinsicRegion.abstractApplied head body))
                ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.cut (UniformIntrinsicRegion.abstractApplied head body)))
                  induction
          | bind signature body =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.bind signature
                  (UniformIntrinsicRegion.abstractApplied head.there body))
                ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.bind signature
                  (UniformIntrinsicRegion.abstractApplied head.there body)))
                induction

/-- Canonical cylindrical receipt for an ordinary compiled leaf sequence and
its exact renaming. -/
def recursiveLeafReceipt
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    (items : ItemSeq definitions smallerContext) →
      CylindricalShapeItemSeq definitions insertion smallerContext largerContext
  | .nil => .nil embedding
  | .cons head tail =>
      .cons (.leaf embedding head (head.renameWires embedding) rfl)
        (recursiveLeafReceipt insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_smaller
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ items : ItemSeq definitions smallerContext,
      (recursiveLeafReceipt insertion embedding items).smaller =
        recursiveLeafItems items
  | .nil => rfl
  | .cons head tail => by
      simp only [recursiveLeafReceipt, CylindricalShapeItemSeq.smaller,
        CylindricalShapeItem.smaller, recursiveLeafItems]
      exact congrArg (UniformIntrinsicItemSeq.cons (.leaf head))
        (recursiveLeafReceipt_smaller insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_larger
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ items : ItemSeq definitions smallerContext,
      (recursiveLeafReceipt insertion embedding items).larger =
        recursiveLeafItems (items.renameWires embedding)
  | .nil => rfl
  | .cons head tail => by
      simp only [recursiveLeafReceipt, CylindricalShapeItemSeq.larger,
        CylindricalShapeItem.larger, recursiveLeafItems, ItemSeq.renameWires]
      exact congrArg
        (UniformIntrinsicItemSeq.cons (.leaf (head.renameWires embedding)))
        (recursiveLeafReceipt_larger insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_embedding
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ (items : ItemSeq definitions smallerContext) {signature : Sig}
      (value : Var smallerContext signature),
      (recursiveLeafReceipt insertion embedding items).embedding value =
        embedding value
  | .nil, _, _ => rfl
  | .cons head tail, _, _ => rfl

/-- Concatenate two cylindrical item-sequence receipts without changing their
shared context action. -/
def recursiveReceiptAppend
    (left right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    CylindricalShapeItemSeq definitions insertion smallerContext largerContext :=
  match left with
  | .nil _ => right
  | .cons head tail => .cons head (recursiveReceiptAppend tail right)

@[simp] theorem recursiveReceiptAppend_smaller
    (right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    ∀ left : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext,
    (recursiveReceiptAppend left right).smaller =
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
        left.smaller right.smaller
  | .nil _ => rfl
  | .cons head tail => by
      simp only [recursiveReceiptAppend, CylindricalShapeItemSeq.smaller,
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.append]
      exact congrArg (UniformIntrinsicItemSeq.cons head.smaller)
        (recursiveReceiptAppend_smaller right tail)

@[simp] theorem recursiveReceiptAppend_larger
    (right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    ∀ left : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext,
    (recursiveReceiptAppend left right).larger =
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
        left.larger right.larger
  | .nil _ => rfl
  | .cons head tail => by
      simp only [recursiveReceiptAppend, CylindricalShapeItemSeq.larger,
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.append]
      exact congrArg (UniformIntrinsicItemSeq.cons head.larger)
        (recursiveReceiptAppend_larger right tail)

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
