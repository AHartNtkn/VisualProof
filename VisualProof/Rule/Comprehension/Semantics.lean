import VisualProof.Rule.Comprehension

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

/-- A checked open comprehension with `arity` relation arguments followed by
fixed parameter positions denotes an actual relation in every lambda model. -/
def interpretedComprehension
    {signature : List Nat}
    (comprehension : CheckedOpenDiagram signature)
    (arity parameterCount : Nat)
    (boundarySplit :
      comprehension.val.boundary.length = arity + parameterCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameters : Fin parameterCount → model.Carrier) :
    Relation model.Carrier arity :=
  fun arguments =>
    comprehension.denote model named
      (Fin.addCases arguments parameters ∘ Fin.cast boundarySplit)

theorem interpretedComprehension_apply
    {signature : List Nat}
    (comprehension : CheckedOpenDiagram signature)
    (arity parameterCount : Nat)
    (boundarySplit :
      comprehension.val.boundary.length = arity + parameterCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameters : Fin parameterCount → model.Carrier)
    (arguments : Fin arity → model.Carrier) :
    interpretedComprehension comprehension arity parameterCount boundarySplit
        model named parameters arguments ↔
      comprehension.denote model named
        (Fin.addCases arguments parameters ∘ Fin.cast boundarySplit) :=
  Iff.rfl

/-- The instantiation payload's ordered split is exactly the relation witness
used to eliminate its quantified relation. -/
def ComprehensionInstantiatePayload.interpretedRelation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders :
      List (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameters : Fin attachments.length → model.Carrier) :
    Relation model.Carrier payload.arity :=
  interpretedComprehension (signature := signature) comprehension payload.arity
    attachments.length
    payload.boundarySplit model named parameters

theorem ComprehensionInstantiatePayload.interpretedRelation_apply
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders :
      List (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameters : Fin attachments.length → model.Carrier)
    (arguments : Fin payload.arity → model.Carrier) :
    payload.interpretedRelation model named parameters arguments ↔
      comprehension.denote model named
        (Fin.addCases arguments parameters ∘
          Fin.cast payload.boundarySplit) :=
  Iff.rfl

/-- Abstraction uses the comprehension itself as its existential relation
witness. Repeated argument positions remain repeated function applications. -/
def abstractionRelation
    {signature : List Nat}
    (comprehension : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    Relation model.Carrier comprehension.val.boundary.length :=
  fun arguments => comprehension.denote model named arguments

theorem abstractionRelation_apply
    {signature : List Nat}
    (comprehension : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (arguments :
      Fin comprehension.val.boundary.length → model.Carrier) :
    abstractionRelation comprehension model named arguments ↔
      comprehension.denote model named arguments :=
  Iff.rfl

/-- Each certified diagonal occurrence denotes application of the single
abstraction witness relation to its possibly aliased ordered arguments. -/
theorem AbstractionWitness.diagonal_denote_iff_relation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {comprehension : CheckedOpenDiagram signature}
    {occurrence : AbstractionOccurrence input}
    (witness : AbstractionWitness input comprehension occurrence)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment :
      Fin occurrence.selection.touchingWires.length → model.Carrier) :
    witness.diagonal.denote model named
        ((environment ∘ Fin.cast witness.diagonal_externalClasses) ∘
          witness.diagonal.elaborate.boundary) ↔
      abstractionRelation (signature := signature) comprehension model named
        (environment ∘ witness.assignment.args) := by
  exact diagonalize_denotation witness model named environment

/-- The comprehension itself supplies the existential relation required by
positive abstraction. -/
theorem abstractionRelation_witness
    {signature : List Nat}
    (comprehension : CheckedOpenDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (body :
      Relation model.Carrier comprehension.val.boundary.length → Prop)
    (holds :
      body (abstractionRelation (signature := signature) comprehension model named)) :
    ∃ relation :
        Relation model.Carrier comprehension.val.boundary.length,
      body relation :=
  ⟨abstractionRelation (signature := signature) comprehension model named, holds⟩

end VisualProof.Rule
