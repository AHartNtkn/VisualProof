import VisualProof.Theory.Relation

namespace VisualProof.Diagram

open VisualProof
open Theory

mutual
  inductive Region : Nat -> RelCtx -> Type
    | mk {wires : Nat} {rels : RelCtx} (localWires : Nat)
        (items : ItemSeq (wires + localWires) rels) :
        Region wires rels

  inductive Item : Nat -> RelCtx -> Type
    | atom : RelVar rels arity -> (Fin arity -> Fin wires) ->
        Item wires rels
    | identity : (arity : Nat) -> (Fin arity -> Fin wires) ->
        Item wires rels
    | cut : Region wires rels -> Item wires rels
    | bubble : (arity : Nat) -> Region wires (arity :: rels) ->
        Item wires rels

  inductive ItemSeq : Nat -> RelCtx -> Type
    | nil : ItemSeq wires rels
    | cons : Item wires rels -> ItemSeq wires rels -> ItemSeq wires rels
end

def Region.localCount : Region wires rels -> Nat
  | .mk localWires _ => localWires

def Region.items (region : Region wires rels) :
    ItemSeq (wires + region.localCount) rels :=
  match region with
  | .mk _ items => items

def Region.itemsCast (region : Region wires rels)
    (localEq : region.localCount = localWires) :
    ItemSeq (wires + localWires) rels :=
  Eq.mp (congrArg (fun count => ItemSeq (wires + count) rels) localEq)
    region.items

theorem Region.itemsCast_eq_of_mk_eq
    (items : ItemSeq (wires + localWires) rels)
    (region : Region wires rels)
    (equality : Region.mk localWires items = region) :
    region.itemsCast (congrArg Region.localCount equality).symm = items := by
  cases equality
  rfl

namespace ItemSeq

def length : ItemSeq wires rels -> Nat
  | .nil => 0
  | .cons _ tail => Nat.succ tail.length

def get : (items : ItemSeq wires rels) ->
    Fin items.length -> Item wires rels
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

def append : ItemSeq wires rels -> ItemSeq wires rels -> ItemSeq wires rels
  | .nil, suffix => suffix
  | .cons item initial, suffix => .cons item (append initial suffix)

@[simp] theorem nil_append (items : ItemSeq wires rels) :
    append .nil items = items := rfl

@[simp] theorem append_nil : (items : ItemSeq wires rels) ->
    append items .nil = items
  | .nil => rfl
  | .cons item tail => congrArg (ItemSeq.cons item) (append_nil tail)

@[simp] theorem append_assoc :
    (first second third : ItemSeq wires rels) ->
    append (append first second) third = append first (append second third)
  | .nil, _, _ => rfl
  | .cons item tail, second, third =>
      congrArg (ItemSeq.cons item) (append_assoc tail second third)

end ItemSeq

end VisualProof.Diagram
