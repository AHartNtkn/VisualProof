import VisualProof.Concrete.Operation.Comprehension

namespace VisualProof.Concrete

open VisualProof.Diagram

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

/-- A checked open comprehension with `arity` relation arguments followed by
fixed parameter positions denotes an actual relation in every model. -/
def interpretedComprehension
    (comprehension : CheckedOpen )
    (arity parameterCount : Nat)
    (boundarySplit :
      comprehension.val.boundary.length = arity + parameterCount)
    (model : Model)
    (parameters : Fin parameterCount → model.Carrier) :
    Relation model.Carrier arity :=
  fun arguments =>
    comprehension.denote model
      (Fin.addCases arguments parameters ∘ Fin.cast boundarySplit)

theorem interpretedComprehension_apply
    (comprehension : CheckedOpen )
    (arity parameterCount : Nat)
    (boundarySplit :
      comprehension.val.boundary.length = arity + parameterCount)
    (model : Model)
    (parameters : Fin parameterCount → model.Carrier)
    (arguments : Fin arity → model.Carrier) :
    interpretedComprehension comprehension arity parameterCount boundarySplit
        model  parameters arguments ↔
      comprehension.denote model
        (Fin.addCases arguments parameters ∘ Fin.cast boundarySplit) :=
  Iff.rfl

/-- The instantiation payload's ordered split is exactly the relation witness
used to eliminate its quantified relation. -/
def OperationComprehensionInstantiatePayload.interpretedRelation
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders :
      List (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Model)
    (parameters : Fin attachments.length → model.Carrier) :
    Relation model.Carrier payload.arity :=
  interpretedComprehension  comprehension payload.arity
    attachments.length
    payload.boundarySplit model  parameters

theorem OperationComprehensionInstantiatePayload.interpretedRelation_apply
    {input : Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders :
      List (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (model : Model)
    (parameters : Fin attachments.length → model.Carrier)
    (arguments : Fin payload.arity → model.Carrier) :
    payload.interpretedRelation model  parameters arguments ↔
      comprehension.denote model
        (Fin.addCases arguments parameters ∘
          Fin.cast payload.boundarySplit) :=
  Iff.rfl

/-- Abstraction uses the comprehension itself as its existential relation
witness. Repeated argument positions remain repeated function applications. -/
def abstractionRelation
    (comprehension : CheckedOpen )
    (model : Model)
    :
    Relation model.Carrier comprehension.val.boundary.length :=
  fun arguments => comprehension.denote model  arguments

theorem abstractionRelation_apply
    (comprehension : CheckedOpen )
    (model : Model)
    (arguments :
      Fin comprehension.val.boundary.length → model.Carrier) :
    abstractionRelation comprehension model  arguments ↔
      comprehension.denote model  arguments :=
  Iff.rfl

/-- Each certified diagonal occurrence denotes application of the single
abstraction witness relation to its possibly aliased ordered arguments. -/
theorem OperationAbstractionWitness.diagonal_denote_iff_relation
    {input : Checked }
    {comprehension : CheckedOpen }
    {occurrence : OperationAbstractionOccurrence input}
    (witness : OperationAbstractionWitness input comprehension occurrence)
    (model : Model)
    (environment :
      Fin occurrence.selection.touchingWires.length → model.Carrier) :
    witness.diagonal.denote model
        ((environment ∘ Fin.cast witness.diagonal_externalClasses) ∘
          witness.diagonal.elaborate.boundary) ↔
      abstractionRelation  comprehension model
        (environment ∘ witness.assignment.args) := by
  exact diagonalize_denotation witness model  environment

/-- The comprehension itself supplies the existential relation required by
positive abstraction. -/
theorem abstractionRelation_witness
    (comprehension : CheckedOpen )
    (model : Model)
    (body :
      Relation model.Carrier comprehension.val.boundary.length → Prop)
    (holds :
      body (abstractionRelation  comprehension model )) :
    ∃ relation :
        Relation model.Carrier comprehension.val.boundary.length,
      body relation :=
  ⟨abstractionRelation  comprehension model , holds⟩

end VisualProof.Concrete
