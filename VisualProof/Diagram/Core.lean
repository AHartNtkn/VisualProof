import VisualProof.Lambda.Syntax
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
    | equation : Fin wires -> Lambda.Term 0 (Fin wires) ->
        Item signature wires rels
    | atom : RelVar rels arity -> (Fin arity -> Fin wires) ->
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

def cutExample : Item [] 0 [] :=
  .cut (.mk 0 .nil)

theorem cutExample_constructible :
    cutExample = Item.cut (Region.mk 0 .nil) := rfl

private def binaryHead : RelVar [2] 2 where
  index := 0
  hasArity := rfl

def binaryBubbleAtomExample : Item [] 2 [] :=
  .bubble 2 (.mk 0 (.cons (.atom binaryHead id) .nil))

theorem binaryBubbleAtomExample_constructible :
    binaryBubbleAtomExample =
      Item.bubble 2
        (Region.mk 0 (ItemSeq.cons (Item.atom binaryHead id) .nil)) := rfl

def ancestorWireUnderCutExample : Item [] 1 [] :=
  .cut (.mk 0 (.cons (.equation 0 (.port 0)) .nil))

theorem ancestorWireUnderCutExample_scoped :
    ancestorWireUnderCutExample =
      Item.cut
        (Region.mk 0 (ItemSeq.cons (Item.equation 0 (.port 0)) .nil)) := rfl

def bareLocalWireExample : Region [] 0 [] :=
  .mk 1 .nil

theorem bareLocalWireExample_constructible :
    bareLocalWireExample = Region.mk 1 .nil := rfl

end VisualProof.Diagram
