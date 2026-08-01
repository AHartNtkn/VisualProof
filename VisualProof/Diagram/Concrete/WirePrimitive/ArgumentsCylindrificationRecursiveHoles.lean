import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

/-- Assemble a cylindrical-hole receipt from exact ordered lengths, the two
finite order equivalences, and one pointwise split equation.  Root and
descendant arity blocks differ only in how they prove that equation. -/
noncomputable def cylindricalHolesOfSplit
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (sourceOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (freshOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (splitExact : ∀ index : Fin freshCount,
      insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index)) =
        ⟨bounds.freshVar outer (freshOrder index),
          Vars.rename (bounds.embed outer)
            (smaller.get
              (Fin.cast smallerLength.symm (sourceOrder index)))⟩) :
    CylindricalHoles insertion bounds outer smaller larger :=
  { smaller_length := smallerLength
    larger_length := largerLength
    sourceIndex := sourceOrder
    sourceIndex_injective := sourceOrder.injective
    sourceIndex_surjective := fun target =>
      ⟨sourceOrder.invFun target, sourceOrder.right_inv target⟩
    freshIndex := freshOrder
    freshIndex_injective := freshOrder.injective
    freshIndex_surjective := fun target =>
      ⟨freshOrder.invFun target, freshOrder.right_inv target⟩
    inserted_exact := fun index => congrArg Prod.fst (splitExact index)
    retained_exact := fun index => congrArg Prod.snd (splitExact index) }

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
