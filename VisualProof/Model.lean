import VisualProof.Lambda.Quotient

namespace VisualProof

/-- A semantic universe for the diagram calculus, backed by a lawful Lambda
model, an inhabited carrier, and exactly the rigid-head separation principle
used by Lambda head stripping. -/
structure Model extends Lambda.LambdaModel where
  nonempty : Nonempty Carrier
  rigidHead_args_reflect :
    ∀ {ports : Nat}
      {left right : Lambda.Term 0 (Fin ports)}
      {leftSpine rightSpine : Lambda.HeadSpine 0 (Fin ports)},
      Lambda.headSpine left = some leftSpine →
      Lambda.headSpine right = some rightSpine →
      (sameBinders : leftSpine.binders = rightSpine.binders) →
      (headIndex : Fin leftSpine.binders) →
      leftSpine.head = .bound headIndex →
      rightSpine.head = .bound (Fin.cast sameBinders headIndex) →
      (sameLength : leftSpine.args.length = rightSpine.args.length) →
      (environment : Fin ports → Carrier) →
      eval left environment = eval right environment →
      ∀ index (valid : index < leftSpine.args.length),
        eval
            (Lambda.prefixClose leftSpine.binders
              (leftSpine.args.get ⟨index, valid⟩)) environment =
          eval
            (Lambda.prefixClose rightSpine.binders
              (rightSpine.args.get ⟨index, sameLength ▸ valid⟩)) environment

namespace Lambda

/-- The canonical beta-eta quotient model reflects aligned bound-rigid-head
equality to equality of every prefix-closed argument. -/
theorem canonicalModel_rigidHead_args_reflect
    {ports : Nat} {left right : Term 0 (Fin ports)}
    {leftSpine rightSpine : HeadSpine 0 (Fin ports)}
    (leftShape : headSpine left = some leftSpine)
    (rightShape : headSpine right = some rightSpine)
    (sameBinders : leftSpine.binders = rightSpine.binders)
    (headIndex : Fin leftSpine.binders)
    (leftHead : leftSpine.head = .bound headIndex)
    (rightHead : rightSpine.head = .bound (Fin.cast sameBinders headIndex))
    (sameLength : leftSpine.args.length = rightSpine.args.length)
    (environment : Fin ports → Individual)
    (evaluationsEqual : canonicalModel.eval left environment =
      canonicalModel.eval right environment) :
    ∀ index (valid : index < leftSpine.args.length),
      canonicalModel.eval
          (prefixClose leftSpine.binders
            (leftSpine.args.get ⟨index, valid⟩)) environment =
      canonicalModel.eval
          (prefixClose rightSpine.binders
            (rightSpine.args.get ⟨index, sameLength ▸ valid⟩)) environment := by
  classical
  let representatives : Fin ports → ClosedTerm := fun port =>
    Classical.choose (Quotient.exists_rep (environment port))
  have representatives_quote : ∀ port,
      quote (representatives port) = environment port := by
    intro port
    exact Classical.choose_spec (Quotient.exists_rep (environment port))
  have leftEvaluation := canonicalModel_eval_eq_quote left environment
    representatives representatives_quote
  have rightEvaluation := canonicalModel_eval_eq_quote right environment
    representatives representatives_quote
  have equivalent : BetaEta (left.bindFree representatives)
      (right.bindFree representatives) := by
    apply quote_eq_iff.mp
    exact leftEvaluation.symm.trans
      (evaluationsEqual.trans rightEvaluation)
  have arguments := rigidHead_args_bindFree_bound leftShape rightShape
    sameBinders headIndex leftHead rightHead sameLength representatives
    equivalent
  intro index valid
  let leftArgument := prefixClose leftSpine.binders
    (leftSpine.args.get ⟨index, valid⟩)
  let rightArgument := prefixClose rightSpine.binders
    (rightSpine.args.get ⟨index, sameLength ▸ valid⟩)
  have argumentEquivalent :
      BetaEta (leftArgument.bindFree representatives)
        (rightArgument.bindFree representatives) :=
    arguments index valid
  have leftQuoted : canonicalModel.eval leftArgument environment =
      quote (leftArgument.bindFree representatives) :=
    canonicalModel_eval_eq_quote leftArgument environment representatives
      representatives_quote
  have quotedEquivalent : quote (leftArgument.bindFree representatives) =
      quote (rightArgument.bindFree representatives) :=
    Quotient.sound argumentEquivalent
  have rightQuoted : canonicalModel.eval rightArgument environment =
      quote (rightArgument.bindFree representatives) :=
    canonicalModel_eval_eq_quote rightArgument environment representatives
      representatives_quote
  exact leftQuoted.trans (quotedEquivalent.trans rightQuoted.symm)

end Lambda

/-- The canonical beta-eta quotient semantics as a diagram model. -/
noncomputable def Model.canonical : Model where
  toLambdaModel := Lambda.canonicalModel
  nonempty := ⟨Lambda.quote (.lam (.bvar 0))⟩
  rigidHead_args_reflect := Lambda.canonicalModel_rigidHead_args_reflect

end VisualProof
