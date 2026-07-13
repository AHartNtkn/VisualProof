import VisualProof.Diagram.Rename
import VisualProof.Lambda.Quotient

namespace VisualProof.Diagram

open VisualProof
open Theory

def Relation (D : Type u) (arity : Nat) := (Fin arity -> D) -> Prop

def RelEnv (D : Type u) : RelCtx -> Type u
  | [] => PUnit
  | arity :: rest => Relation D arity × RelEnv D rest

def NamedEnv (D : Type u) (signature : List Nat) :=
  forall arity, NamedRel signature arity -> Relation D arity

def RelEnv.lookup {ctx : RelCtx} (env : RelEnv D ctx)
    (relation : RelVar ctx arity) : Relation D arity :=
  match ctx, env, relation with
  | head :: tail, (headRelation, tailEnv), ⟨index, hasArity⟩ =>
      Fin.cases
        (motive := fun i => (head :: tail).get i = arity -> Relation D arity)
        (fun h => h ▸ headRelation)
        (fun i h => tailEnv.lookup ⟨i, h⟩)
        index hasArity

def extendWireEnv (outerEnv : Fin outer -> D) (localEnv : Fin localWires -> D) :
    Fin (outer + localWires) -> D :=
  Fin.addCases outerEnv localEnv

@[simp] theorem extendWireEnv_zero (outerEnv : Fin outer -> D)
    (localEnv : Fin 0 -> D) :
    extendWireEnv outerEnv localEnv = outerEnv := by
  funext i
  let j : Fin outer := Fin.cast (Nat.add_zero outer) i
  have hi : i = Fin.castAdd 0 j := by
    apply Fin.ext
    rfl
  rw [hi]
  exact Fin.addCases_left j

mutual
  def denoteRegion (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin outer -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      Region signature outer relCtx -> Prop
    | .mk localWires items =>
        exists localEnv : Fin localWires -> model.Carrier,
          denoteItemSeq model named (extendWireEnv env localEnv) rels items

  def denoteItem (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin wires -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      Item signature wires relCtx -> Prop
    | .equation output term => env output = model.eval term env
    | .atom relation arguments => rels.lookup relation (env ∘ arguments)
    | .named relation arguments => named _ relation (env ∘ arguments)
    | .cut body => Not (denoteRegion model named env rels body)
    | .bubble arity body =>
        exists relation : Relation model.Carrier arity,
          denoteRegion (relCtx := arity :: relCtx) model named env
            (relation, rels) body

  def denoteItemSeq (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin wires -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      ItemSeq signature wires relCtx -> Prop
    | .nil => True
    | .cons item tail =>
        denoteItem model named env rels item /\
          denoteItemSeq model named env rels tail
end

def denoteOpen (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (diagram : OpenDiagram signature arity)
    (args : Fin arity -> model.Carrier) : Prop :=
  exists assignment : BoundaryAssignment diagram model.Carrier,
    assignment.args = args /\
      denoteRegion (relCtx := []) model named assignment.classes PUnit.unit
        diagram.body

@[simp] theorem denoteRegion_mk
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin outer -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (localWires : Nat)
    (items : ItemSeq signature (outer + localWires) relCtx) :
    denoteRegion model named env rels (Region.mk localWires items) <->
      exists localEnv : Fin localWires -> model.Carrier,
        denoteItemSeq model named (extendWireEnv env localEnv) rels items := by
  rfl

@[simp] theorem denoteItem_equation
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (output : Fin wires)
    (term : Lambda.Term 0 (Fin wires)) :
    denoteItem model named env rels (Item.equation output term) <->
      env output = model.eval term env := by
  rfl

@[simp] theorem denoteItem_atom
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (relation : RelVar relCtx arity)
    (arguments : Fin arity -> Fin wires) :
    denoteItem model named env rels (Item.atom relation arguments) <->
      rels.lookup relation (env ∘ arguments) := by
  rfl

@[simp] theorem denoteItem_named
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (relation : NamedRel signature arity)
    (arguments : Fin arity -> Fin wires) :
    denoteItem model named env rels (Item.named relation arguments) <->
      named arity relation (env ∘ arguments) := by
  rfl

@[simp] theorem cut_denotes_negation
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region signature wires relCtx) :
    denoteItem model named env rels (Item.cut body) <->
      Not (denoteRegion model named env rels body) := by
  rfl

@[simp] theorem bubble_denotes_exists
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (arity : Nat)
    (body : Region signature wires (arity :: relCtx)) :
    denoteItem model named env rels (Item.bubble arity body) <->
      exists relation : Relation model.Carrier arity,
        denoteRegion (relCtx := arity :: relCtx) model named env
          (relation, rels) body := by
  rfl

@[simp] theorem denoteItemSeq_nil
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteItemSeq model named env rels (ItemSeq.nil :
      ItemSeq signature wires relCtx) <-> True := by
  rfl

@[simp] theorem denoteItemSeq_cons
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (item : Item signature wires relCtx)
    (tail : ItemSeq signature wires relCtx) :
    denoteItemSeq model named env rels (ItemSeq.cons item tail) <->
      denoteItem model named env rels item /\
        denoteItemSeq model named env rels tail := by
  rfl

theorem blank_zero_local_denotes_true
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteRegion model named env rels
      (Region.mk 0 .nil : Region signature wires relCtx) <-> True := by
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨Fin.elim0, trivial⟩

theorem two_item_sequence_denotes_conjunction
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : Item signature wires relCtx) :
    denoteItemSeq model named env rels (.cons first (.cons second .nil)) <->
      denoteItem model named env rels first /\
        denoteItem model named env rels second := by
  simp

theorem bareLocalWireExample_denotes_iff_nonempty
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier []) :
    denoteRegion (relCtx := []) model named Fin.elim0 PUnit.unit
        bareLocalWireExample <->
      Nonempty model.Carrier := by
  constructor
  · rintro ⟨localEnv, _⟩
    exact ⟨localEnv 0⟩
  · rintro ⟨value⟩
    exact ⟨fun _ => value, trivial⟩

theorem unary_bubble_denotes_exists
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region signature wires (1 :: relCtx)) :
    denoteItem model named env rels (Item.bubble 1 body) <->
      exists predicate : (Fin 1 -> model.Carrier) -> Prop,
        denoteRegion (relCtx := 1 :: relCtx) model named env
          (predicate, rels) body := by
  rfl

theorem denoteOpen_iff_assignment
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (diagram : OpenDiagram signature arity)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model named diagram args <->
      exists assignment : BoundaryAssignment diagram model.Carrier,
        assignment.args = args /\
          denoteRegion (relCtx := []) model named assignment.classes PUnit.unit
            diagram.body := by
  rfl

theorem aliasedBinaryBoundaryExample_rejects_unequal
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier [])
    (args : Fin 2 -> model.Carrier) (unequal : args 0 ≠ args 1) :
    Not (denoteOpen model named aliasedBinaryBoundaryExample args) := by
  rintro ⟨assignment, hargs, _⟩
  apply unequal
  rw [← hargs]
  exact (aliasedBinaryBoundaryExample_consistency_iff assignment.args).mp
    ((boundaryAssignment_iff_aliasConsistent
      aliasedBinaryBoundaryExample assignment.args).mp ⟨assignment, rfl⟩)

theorem double_cut_denotes_iff
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region signature wires relCtx) :
    denoteItem model named env rels
        (Item.cut (Region.mk 0 (.cons (Item.cut body) .nil))) <->
      denoteRegion model named env rels body := by
  simp only [cut_denotes_negation, denoteRegion_mk, denoteItemSeq_cons,
    denoteItemSeq_nil, and_true]
  constructor
  · intro h
    exact Classical.byContradiction fun hbody =>
      h ⟨Fin.elim0, by simpa using hbody⟩
  · intro hbody hnot
    rcases hnot with ⟨localEnv, hlocal⟩
    exact hlocal (by simpa using hbody)

end VisualProof.Diagram
