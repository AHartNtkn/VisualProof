import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalContext

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

/-- Regions that may occur in a binder stack while traversing the certified
final-to-original simulation: preserved frame regions and the single promoted
focus. -/
def FinalAdmissible
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (region : Fin elimTrace.sourceDiagram.regionCount) : Prop :=
  copyTrace.FinalRegularPreimage elimTrace finalWellFormed region ∨
    region = elimTrace.targetIndex finalWellFormed

theorem reverseRegionMap_injective_of_admissible
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    {first second : Fin elimTrace.sourceDiagram.regionCount}
    (firstAdmissible : copyTrace.FinalAdmissible elimTrace finalWellFormed
      first)
    (secondAdmissible : copyTrace.FinalAdmissible elimTrace finalWellFormed
      second)
    (mapped : copyTrace.reverseRegionMap elimTrace finalWellFormed first =
      copyTrace.reverseRegionMap elimTrace finalWellFormed second) :
    first = second := by
  rcases firstAdmissible with firstRegular | firstFocus
  · rcases secondAdmissible with secondRegular | secondFocus
    · have firstForward := copyTrace.finalRegionMap_reverseRegionMap elimTrace
        finalWellFormed first firstRegular
      have secondForward := copyTrace.finalRegionMap_reverseRegionMap elimTrace
        finalWellFormed second secondRegular
      rw [← firstForward, ← secondForward, mapped]
    · subst second
      have firstSpec := copyTrace.reverseRegionMap_spec elimTrace
        finalWellFormed first firstRegular
      have firstParent : copyTrace.reverseRegionMap elimTrace finalWellFormed
          first = payload.parent := by
        rw [mapped]
        exact copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed
      exact False.elim (firstSpec.1.2 firstParent)
  · subst first
    rcases secondAdmissible with secondRegular | secondFocus
    · have secondSpec := copyTrace.reverseRegionMap_spec elimTrace
        finalWellFormed second secondRegular
      have secondParent : copyTrace.reverseRegionMap elimTrace finalWellFormed
          second = payload.parent := by
        rw [← mapped]
        exact copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed
      exact False.elim (secondSpec.1.2 secondParent)
    · exact secondFocus.symm

theorem child_admissible_of_regular_parent
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (parent child : Fin elimTrace.sourceDiagram.regionCount)
    (parentRegular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      parent)
    (childParent : (elimTrace.sourceDiagram.regions child).parent? =
      some parent) :
    copyTrace.FinalAdmissible elimTrace finalWellFormed child := by
  obtain ⟨originalChild, originalChildParent, mappedChild, _reverseChild⟩ :=
    copyTrace.finalChild_preimage_of_regular_parent elimTrace finalWellFormed
      parent parentRegular child childParent
  let originalParent := copyTrace.reverseRegionMap elimTrace finalWellFormed
    parent
  let originalParentRegular := (copyTrace.reverseRegionMap_spec elimTrace
    finalWellFormed parent parentRegular).1
  by_cases childFocus : originalChild = payload.parent
  · right
    exact mappedChild.symm.trans ((congrArg
      (copyTrace.finalRegionMap elimTrace finalWellFormed) childFocus).trans
      (copyTrace.finalRegionMap_parent elimTrace finalWellFormed))
  · left
    refine ⟨originalChild, ?_, mappedChild⟩
    constructor
    · intro enclosed
      rcases ConcreteElaboration.encloses_direct_child originalChildParent
          enclosed with childBubble | parentEnclosed
      · have childIsBubble : originalChild = bubble := childBubble.symm
        have direct := originalChildParent
        rw [childIsBubble, payload.bubble_eq] at direct
        have parentEq : payload.parent = originalParent :=
          Option.some.inj (by simpa [CRegion.parent?] using direct)
        exact originalParentRegular.2 parentEq.symm
      · exact originalParentRegular.1 parentEnclosed
    · exact childFocus

section BinderWitness

variable
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    {raw : ConcreteDiagram}

def FinalBindersMapped
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input.val targetRels)
    (relationMap : RelationRenaming sourceRels targetRels) : Prop :=
  ∀ region binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    targetBinders (copyTrace.reverseRegionMap elimTrace finalWellFormed region) =
      some ⟨binderArity, relationMap sourceRelation⟩

structure FinalBinderWitness
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input.val targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  bindersMapped : FinalBindersMapped copyTrace elimTrace finalWellFormed
    sourceBinders targetBinders relationMap
  admissible : ∀ region binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    copyTrace.FinalAdmissible elimTrace finalWellFormed region

namespace FinalBinderWitness

def empty
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    FinalBinderWitness copyTrace elimTrace finalWellFormed
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty where
  relationMap := ConcreteElaboration.identityRelationRenaming []
  bindersMapped := by simp [FinalBindersMapped,
    ConcreteElaboration.BinderContext.empty]
  admissible := by simp [ConcreteElaboration.BinderContext.empty]

def push
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    {finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input.val targetRels}
    (witness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders)
    (child parent : Fin elimTrace.sourceDiagram.regionCount)
    (arity : Nat)
    (childShape : elimTrace.sourceDiagram.regions child =
      .bubble parent arity)
    (parentRegular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      parent) :
    FinalBinderWitness copyTrace elimTrace finalWellFormed
      (sourceBinders.push child arity)
      (targetBinders.push
        (copyTrace.reverseRegionMap elimTrace finalWellFormed child) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    have childParent : (elimTrace.sourceDiagram.regions child).parent? =
        some parent := by simp [childShape, CRegion.parent?]
    have childAdmissible := copyTrace.child_admissible_of_regular_parent
      elimTrace finalWellFormed parent child parentRegular childParent
    by_cases equality : region = child
    · subst region
      simp only [ConcreteElaboration.BinderContext.push_self] at sourceLookup ⊢
      cases Option.some.inj sourceLookup
      rfl
    · rw [ConcreteElaboration.BinderContext.push_other _ arity equality]
        at sourceLookup
      cases sourceEq : sourceBinders region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          have regionAdmissible := witness.admissible region actualArity
            actualRelation sourceEq
          have reverseNe : copyTrace.reverseRegionMap elimTrace finalWellFormed
              region ≠
              copyTrace.reverseRegionMap elimTrace finalWellFormed child :=
            fun reverseEq => equality
              (copyTrace.reverseRegionMap_injective_of_admissible elimTrace
                finalWellFormed regionAdmissible childAdmissible reverseEq)
          rw [ConcreteElaboration.BinderContext.push_other _ arity reverseNe]
          simp [sourceEq] at sourceLookup
          rcases sourceLookup with ⟨arityEq, relationEq⟩
          subst binderArity
          have relationEq' := eq_of_heq relationEq
          subst sourceRelation
          rw [witness.bindersMapped region actualArity actualRelation sourceEq]
          rfl
  admissible := by
    intro region binderArity sourceRelation sourceLookup
    have childParent : (elimTrace.sourceDiagram.regions child).parent? =
        some parent := by simp [childShape, CRegion.parent?]
    by_cases equality : region = child
    · subst region
      exact copyTrace.child_admissible_of_regular_parent elimTrace
        finalWellFormed parent child parentRegular childParent
    · rw [ConcreteElaboration.BinderContext.push_other _ arity equality]
        at sourceLookup
      cases sourceEq : sourceBinders region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          exact witness.admissible region actualArity actualRelation sourceEq

theorem relationMap_push
    (witness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (child parent : Fin elimTrace.sourceDiagram.regionCount)
    (arity : Nat)
    (childShape : elimTrace.sourceDiagram.regions child =
      .bubble parent arity)
    (parentRegular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      parent) :
    ((push witness child parent arity childShape parentRegular).relationMap :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

end FinalBinderWitness

end BinderWitness

end InstantiationTrace

end VisualProof.Rule
