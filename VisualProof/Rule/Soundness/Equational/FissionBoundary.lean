import VisualProof.Rule.Soundness.Equational.FissionRootContext

namespace VisualProof.Rule

open VisualProof
open Diagram

namespace FissionSoundness

theorem boundaryWitness
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin boundary.length → model.Carrier) :
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction (sourceCheckedOpen input boundary sourceRoot).elaborate
      (targetCheckedOpen input selected site producer residual boundary
        sourceRoot targetWellFormed).elaborate
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedIndex (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)))
      model named sourceArgs
      (sourceArgs ∘ Fin.cast
        (boundaryLengthEq (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual)
          (boundary := boundary))) := by
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment
          (targetCheckedOpen input selected site producer residual boundary
            sourceRoot targetWellFormed).elaborate model.Carrier := {
        args := sourceArgs ∘ Fin.cast
          (boundaryLengthEq (input := input) (selected := selected)
            (site := site) (producer := producer) (residual := residual)
            (boundary := boundary))
        classes := sourceAssignment.classes ∘ sourceExposedIndex
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast
            (boundaryLengthEq (input := input) (selected := selected)
              (site := site) (producer := producer) (residual := residual)
              (boundary := boundary)) targetPosition
          have classEq := boundaryClass
            (input := input) (selected := selected) (site := site)
            (producer := producer) (residual := residual)
            (boundary := boundary) sourcePosition
          have positionEq : Fin.cast
              (boundaryLengthEq (input := input) (selected := selected)
                (site := site) (producer := producer) (residual := residual)
                (boundary := boundary)).symm sourcePosition =
                targetPosition := by
            apply Fin.ext
            rfl
          rw [positionEq] at classEq
          change sourceAssignment.classes
              (sourceExposedIndex
                ((targetOpen input selected site producer residual boundary
                  ).boundaryClass targetPosition)) = sourceArgs sourcePosition
          rw [← classEq, sourceExposedIndex_exposedIndex]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          change sourceAssignment.classes
              ((sourceOpen input boundary).boundaryClass sourcePosition) =
            sourceAssignment.args sourcePosition at sourceAgrees
          rw [sourceArgsEq] at sourceAgrees
          exact sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      funext sourceClass
      simp only [targetAssignment, Function.comp_apply]
      rw [sourceExposedIndex_exposedIndex]
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment
          (sourceCheckedOpen input boundary sourceRoot).elaborate
          model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘
          exposedIndex (input := input) (selected := selected) (site := site)
            (producer := producer) (residual := residual) (boundary := boundary)
        agrees := by
          intro sourcePosition
          change targetAssignment.classes
              (exposedIndex
                ((sourceOpen input boundary).boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          rw [boundaryClass]
          have targetAgrees := targetAssignment.agrees
            (Fin.cast
              (boundaryLengthEq (input := input) (selected := selected)
                (site := site) (producer := producer) (residual := residual)
                (boundary := boundary)).symm sourcePosition)
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      rfl

end FissionSoundness

end VisualProof.Rule
