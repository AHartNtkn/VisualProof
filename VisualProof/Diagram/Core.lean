import VisualProof.Model
import VisualProof.Theory.Signature

namespace VisualProof.Diagram

open VisualProof
open Theory

mutual
  inductive Region (signature : List Nat) : Nat -> RelCtx -> Type
    | mk {wires : Nat} {rels : RelCtx} (localWires : Nat)
        (items : ItemSeq signature (wires + localWires) rels) :
        Region signature wires rels

  inductive Item (signature : List Nat) : Nat -> RelCtx -> Type
    | atom : RelVar rels arity -> (Fin arity -> Fin wires) ->
        Item signature wires rels
    | identity : (arity : Nat) -> (Fin arity -> Fin wires) ->
        Item signature wires rels
    | named : NamedRel signature arity -> (Fin arity -> Fin wires) ->
        Item signature wires rels
    | cut : Region signature wires rels -> Item signature wires rels
    | bubble : (arity : Nat) -> Region signature wires (arity :: rels) ->
        Item signature wires rels

  inductive ItemSeq (signature : List Nat) : Nat -> RelCtx -> Type
    | nil : ItemSeq signature wires rels
    | cons : Item signature wires rels -> ItemSeq signature wires rels ->
        ItemSeq signature wires rels
end

namespace ItemSeq

def length : ItemSeq signature wires rels -> Nat
  | .nil => 0
  | .cons _ tail => Nat.succ tail.length

def get : (items : ItemSeq signature wires rels) ->
    Fin items.length -> Item signature wires rels
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

def append : ItemSeq signature wires rels -> ItemSeq signature wires rels ->
    ItemSeq signature wires rels
  | .nil, suffix => suffix
  | .cons item initial, suffix => .cons item (append initial suffix)

@[simp] theorem nil_append (items : ItemSeq signature wires rels) :
    append .nil items = items := rfl

@[simp] theorem append_nil : (items : ItemSeq signature wires rels) ->
    append items .nil = items
  | .nil => rfl
  | .cons item tail => congrArg (ItemSeq.cons item) (append_nil tail)

@[simp] theorem append_assoc :
    (first second third : ItemSeq signature wires rels) ->
    append (append first second) third = append first (append second third)
  | .nil, _, _ => rfl
  | .cons item tail, second, third =>
      congrArg (ItemSeq.cons item) (append_assoc tail second third)

end ItemSeq

end VisualProof.Diagram
