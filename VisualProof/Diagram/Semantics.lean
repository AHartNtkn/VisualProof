import VisualProof.Diagram.Environment
import VisualProof.Model

namespace VisualProof.Diagram

open VisualProof
open Theory

def Relation (D : Type u) (arity : Nat) := (Fin arity -> D) -> Prop

def RelEnv (D : Type u) : RelCtx -> Type u
  | [] => PUnit
  | arity :: rest => Relation D arity × RelEnv D rest

def RelEnv.lookup {ctx : RelCtx} (env : RelEnv D ctx)
    (relation : RelVar ctx arity) : Relation D arity :=
  match ctx, env, relation with
  | head :: tail, (headRelation, tailEnv), ⟨index, hasArity⟩ =>
      Fin.cases
        (motive := fun i => (head :: tail).get i = arity -> Relation D arity)
        (fun h => h ▸ headRelation)
        (fun i h => tailEnv.lookup ⟨i, h⟩)
        index hasArity

mutual
  def denoteRegion (model : Model)
      (env : Fin outer -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      Region outer relCtx -> Prop
    | .mk localWires items =>
        exists localEnv : Fin localWires -> model.Carrier,
          denoteItemSeq model (extendWireEnv env localEnv) rels items

  def denoteItem (model : Model)
      (env : Fin wires -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      Item wires relCtx -> Prop
    | .atom relation arguments => rels.lookup relation (env ∘ arguments)
    | .identity arity arguments =>
        ∀ left right : Fin arity, env (arguments left) = env (arguments right)
    | .cut body => Not (denoteRegion model env rels body)
    | .bubble arity body =>
        exists relation : Relation model.Carrier arity,
          denoteRegion (relCtx := arity :: relCtx) model env
            (relation, rels) body

  def denoteItemSeq (model : Model)
      (env : Fin wires -> model.Carrier)
      (rels : RelEnv model.Carrier relCtx) :
      ItemSeq wires relCtx -> Prop
    | .nil => True
    | .cons item tail =>
        denoteItem model env rels item /\
          denoteItemSeq model env rels tail
end

def denoteOpen (model : Model)
    (diagram : OpenDiagram arity)
    (args : Fin arity -> model.Carrier) : Prop :=
  exists assignment : BoundaryAssignment diagram model.Carrier,
    assignment.args = args /\
      denoteRegion (relCtx := []) model assignment.classes PUnit.unit
        diagram.body

theorem denoteOpen_castArity (model : Model)
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (args : Fin targetArity -> model.Carrier) :
    denoteOpen model (diagram.castArity equality) args <->
      denoteOpen model diagram (args ∘ Fin.cast equality) := by
  subst targetArity
  rfl

@[simp] theorem denoteRegion_mk
    (model : Model)
    (env : Fin outer -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (localWires : Nat)
    (items : ItemSeq (outer + localWires) relCtx) :
    denoteRegion model env rels (Region.mk localWires items) <->
      exists localEnv : Fin localWires -> model.Carrier,
        denoteItemSeq model (extendWireEnv env localEnv) rels items := by
  rfl

@[simp] theorem denoteItem_atom
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (relation : RelVar relCtx arity)
    (arguments : Fin arity -> Fin wires) :
    denoteItem model env rels (Item.atom relation arguments) <->
      rels.lookup relation (env ∘ arguments) := by
  rfl

@[simp] theorem denoteItem_identity
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (arity : Nat)
    (arguments : Fin arity -> Fin wires) :
    denoteItem model env rels (Item.identity arity arguments) <->
      ∀ left right : Fin arity,
        env (arguments left) = env (arguments right) := by
  rfl

@[simp] theorem cut_denotes_negation
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region wires relCtx) :
    denoteItem model env rels (Item.cut body) <->
      Not (denoteRegion model env rels body) := by
  rfl

@[simp] theorem bubble_denotes_exists
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) (arity : Nat)
    (body : Region wires (arity :: relCtx)) :
    denoteItem model env rels (Item.bubble arity body) <->
      exists relation : Relation model.Carrier arity,
        denoteRegion (relCtx := arity :: relCtx) model env
          (relation, rels) body := by
  rfl

@[simp] theorem denoteItemSeq_nil
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteItemSeq model env rels (ItemSeq.nil : ItemSeq wires relCtx) <-> True := by
  rfl

@[simp] theorem denoteItemSeq_cons
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (item : Item wires relCtx)
    (tail : ItemSeq wires relCtx) :
    denoteItemSeq model env rels (ItemSeq.cons item tail) <->
      denoteItem model env rels item /\
        denoteItemSeq model env rels tail := by
  rfl

theorem blank_zero_local_denotes_true
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteRegion model env rels
      (Region.mk 0 .nil : Region wires relCtx) <-> True := by
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨Fin.elim0, trivial⟩

theorem two_item_sequence_denotes_conjunction
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : Item wires relCtx) :
    denoteItemSeq model env rels (.cons first (.cons second .nil)) <->
      denoteItem model env rels first /\
        denoteItem model env rels second := by
  simp

theorem unary_bubble_denotes_exists
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region wires (1 :: relCtx)) :
    denoteItem model env rels (Item.bubble 1 body) <->
      exists predicate : (Fin 1 -> model.Carrier) -> Prop,
        denoteRegion (relCtx := 1 :: relCtx) model env
          (predicate, rels) body := by
  rfl

theorem denoteOpen_iff_assignment
    (model : Model)
    (diagram : OpenDiagram arity)
    (args : Fin arity -> model.Carrier) :
    denoteOpen model diagram args <->
      exists assignment : BoundaryAssignment diagram model.Carrier,
        assignment.args = args /\
          denoteRegion (relCtx := []) model assignment.classes PUnit.unit
            diagram.body := by
  rfl

theorem OpenDiagram.denote_body
    {diagram : OpenDiagram arity}
    {before after : Region diagram.externalClasses []}
    {model : Model}
    {args : Fin arity → model.Carrier}
    (h : ∀ env : Fin diagram.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model env PUnit.unit before →
      denoteRegion (relCtx := []) model env PUnit.unit after) :
    denoteOpen model (diagram.withBody before) args →
    denoteOpen model (diagram.withBody after) args := by
  rintro ⟨assignment, hargs, hbefore⟩
  let targetAssignment : BoundaryAssignment (diagram.withBody after)
      model.Carrier := {
    args := assignment.args
    classes := assignment.classes
    agrees := assignment.agrees
  }
  refine ⟨targetAssignment, hargs, ?_⟩
  exact h assignment.classes hbefore

theorem OpenDiagram.denote_body_iff
    {diagram : OpenDiagram arity}
    {before after : Region diagram.externalClasses []}
    {model : Model}
    {args : Fin arity → model.Carrier}
    (h : ∀ env : Fin diagram.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model env PUnit.unit before ↔
      denoteRegion (relCtx := []) model env PUnit.unit after) :
    denoteOpen model (diagram.withBody before) args ↔
    denoteOpen model (diagram.withBody after) args := by
  constructor
  · exact OpenDiagram.denote_body (diagram := diagram)
      (before := before) (after := after) fun env => (h env).mp
  · exact OpenDiagram.denote_body (diagram := diagram)
      (before := after) (after := before) fun env => (h env).mpr

theorem double_cut_denotes_iff
    (model : Model)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (body : Region wires relCtx) :
    denoteItem model env rels
        (Item.cut (Region.mk 0 (.cons (Item.cut body) .nil))) <->
      denoteRegion model env rels body := by
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
