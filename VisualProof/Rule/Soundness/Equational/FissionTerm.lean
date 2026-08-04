import VisualProof.Rule.Equational

namespace VisualProof.Rule

open VisualProof
open Diagram

namespace FissionSoundness

def liftClosedTo (bound : Nat) (term : Lambda.Term 0 α) :
    Lambda.Term bound α :=
  term.renameBound Fin.elim0

theorem liftClosedTo_zero (term : Lambda.Term 0 α) :
    liftClosedTo 0 term = term := by
  unfold liftClosedTo
  rw [show (Fin.elim0 : Fin 0 → Fin 0) = id by funext index; exact Fin.elim0 index]
  exact term.renameBound_id

theorem liftClosedTo_succ (bound : Nat) (term : Lambda.Term 0 α) :
    (liftClosedTo bound term).lift = liftClosedTo (bound + 1) term := by
  unfold liftClosedTo Lambda.Term.lift
  rw [Lambda.Term.renameBound_comp]
  apply congrArg (fun rename ↦ term.renameBound rename)
  funext index
  exact Fin.elim0 index

def fillFresh (bound : Nat) (producer : Lambda.Term 0 α) :
    Option α → Lambda.Term bound α
  | none => liftClosedTo bound producer
  | some wire => .port wire

theorem fillFresh_succ (bound : Nat) (producer : Lambda.Term 0 α) :
    (fun value ↦ (fillFresh bound producer value).lift) =
      fillFresh (bound + 1) producer := by
  funext value
  cases value with
  | none => exact liftClosedTo_succ bound producer
  | some wire => rfl

theorem mapSome_fillFresh (term : Lambda.Term bound α)
    (producer : Lambda.Term 0 α) :
    (term.mapFree some).bindFree (fillFresh bound producer) = term := by
  rw [Lambda.Term.mapFree_eq_bindFree_ports,
    Lambda.Term.bindFree_assoc]
  simpa [fillFresh] using term.bindFree_id

theorem lowerToZero_sound
    (bound : Nat) (selected : Lambda.Term bound α)
    (producer : Lambda.Term 0 α)
    (lowered : lowerToZero bound selected = some producer) :
    selected = liftClosedTo bound producer := by
  cases bound with
  | zero =>
      simp only [lowerToZero] at lowered
      have equality : selected = producer := Option.some.inj lowered
      exact equality.trans (liftClosedTo_zero producer).symm
  | succ bound =>
      simp only [lowerToZero] at lowered
      cases unliftResult : selected.unlift with
      | none => simp [unliftResult] at lowered
      | some previous =>
          have recursive : lowerToZero bound previous = some producer := by
            simpa [unliftResult] using lowered
          calc
            selected = previous.lift := Lambda.Term.unlift_sound unliftResult
            _ = (liftClosedTo bound producer).lift :=
              congrArg Lambda.Term.lift
                (lowerToZero_sound bound previous producer recursive)
            _ = liftClosedTo (bound + 1) producer :=
              liftClosedTo_succ bound producer
termination_by bound

theorem replaceSelected_reconstruct
    (term : Lambda.Term bound α)
    (path : List Lambda.PathSegment)
    (depth : Nat) (selected : Lambda.Term depth α)
    (residual : Lambda.Term bound (Option α))
    (producer : Lambda.Term 0 α)
    (selectedResult : subtermAt? term path = some ⟨depth, selected⟩)
    (residualResult : replaceAtPort? (term.mapFree some) path none =
      some residual)
    (producerResult : lowerToZero depth selected = some producer) :
    residual.bindFree (fillFresh bound producer) = term := by
  induction path generalizing bound term residual with
  | nil =>
      simp only [subtermAt?] at selectedResult
      cases selectedResult
      simp only [replaceAtPort?] at residualResult
      cases residualResult
      simpa only [Lambda.Term.bindFree, fillFresh] using
        (lowerToZero_sound _ _ producer producerResult).symm
  | cons segment rest ih =>
      cases segment with
      | fn =>
          cases term with
          | bvar index => contradiction
          | port wire => contradiction
          | lam body => contradiction
          | app fn argument =>
              simp only [subtermAt?] at selectedResult
              simp only [replaceAtPort?, Lambda.Term.mapFree] at residualResult
              obtain ⟨replaced, replacedResult, rfl⟩ :=
                Option.map_eq_some_iff.mp residualResult
              simp only [Lambda.Term.bindFree]
              rw [ih fn replaced selectedResult replacedResult,
                mapSome_fillFresh argument producer]
      | arg =>
          cases term with
          | bvar index => contradiction
          | port wire => contradiction
          | lam body => contradiction
          | app fn argument =>
              simp only [subtermAt?] at selectedResult
              simp only [replaceAtPort?, Lambda.Term.mapFree] at residualResult
              obtain ⟨replaced, replacedResult, rfl⟩ :=
                Option.map_eq_some_iff.mp residualResult
              simp only [Lambda.Term.bindFree]
              rw [mapSome_fillFresh fn producer,
                ih argument replaced selectedResult replacedResult]
      | body =>
          cases term with
          | bvar index => contradiction
          | port wire => contradiction
          | app fn argument => contradiction
          | lam body =>
              simp only [subtermAt?] at selectedResult
              simp only [replaceAtPort?, Lambda.Term.mapFree] at residualResult
              obtain ⟨replaced, replacedResult, rfl⟩ :=
                Option.map_eq_some_iff.mp residualResult
              simp only [Lambda.Term.bindFree]
              apply congrArg Lambda.Term.lam
              rw [fillFresh_succ]
              exact ih body replaced selectedResult replacedResult

theorem executor_reconstructs_global
    (term : Lambda.Term 0 α)
    (path : List Lambda.PathSegment)
    (depth : Nat) (selected : Lambda.Term depth α)
    (residual : Lambda.Term 0 (Option α))
    (producer : Lambda.Term 0 α)
    (selectedResult : subtermAt? term path = some ⟨depth, selected⟩)
    (residualResult : replaceAtPort? (term.mapFree some) path none =
      some residual)
    (producerResult : lowerToZero depth selected = some producer) :
    residual.bindFree (fun
      | none => producer
      | some wire => .port wire) = term := by
  have fillEq : fillFresh 0 producer = (fun
      | none => producer
      | some wire => Lambda.Term.port wire) := by
    funext value
    cases value with
    | none => exact liftClosedTo_zero producer
    | some wire => rfl
  rw [← fillEq]
  exact replaceSelected_reconstruct term path depth selected residual producer
    selectedResult residualResult producerResult

end FissionSoundness

end VisualProof.Rule
