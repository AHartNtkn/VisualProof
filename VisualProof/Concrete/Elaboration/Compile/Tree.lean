import VisualProof.Concrete.Elaboration.Context
import VisualProof.Diagram.Algebra

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
The ordinary elaborator retains the concrete origin and recursive source shape
of every intrinsic item it produces.  Items deliberately own their origins as
data: no item or sequence is indexed by a `LocalOccurrence`.
-/

structure RegionWireSplit (outerWires totalWires localWires : Nat) : Prop where
  total_eq : totalWires = outerWires + localWires

mutual
  inductive CompiledRegion (d : Diagram) :
      Fin d.regionCount -> Nat -> RelCtx -> Type
    | mk {origin : Fin d.regionCount} {outerWires totalWires : Nat}
        {rels : RelCtx}
        (localWires : Nat)
        (items : CompiledItems d totalWires rels)
        (split : RegionWireSplit outerWires totalWires localWires) :
        CompiledRegion d origin outerWires rels

  inductive CompiledItem (d : Diagram) : Nat -> RelCtx -> Type
    | node {wires : Nat} {rels : RelCtx} (origin : Fin d.nodeCount)
        (item : Item wires rels) : CompiledItem d wires rels
    | cut {wires : Nat} {rels : RelCtx} (origin : Fin d.regionCount)
        (body : CompiledRegion d origin wires rels) : CompiledItem d wires rels
    | bubble {wires : Nat} {rels : RelCtx} (origin : Fin d.regionCount)
        (arity : Nat)
        (body : CompiledRegion d origin wires (arity :: rels)) :
        CompiledItem d wires rels

  inductive CompiledItems (d : Diagram) : Nat -> RelCtx -> Type
    | nil {wires : Nat} {rels : RelCtx} : CompiledItems d wires rels
    | cons {wires : Nat} {rels : RelCtx} (head : CompiledItem d wires rels)
        (tail : CompiledItems d wires rels) : CompiledItems d wires rels
end

mutual
  def CompiledRegion.erase :
      CompiledRegion d origin wires rels -> Region wires rels
    | .mk localWires items split =>
        .mk localWires (items.erase.castWiresEq split.total_eq)

  def CompiledItem.erase : CompiledItem d wires rels -> Item wires rels
    | .node _ item => item
    | .cut _ body => .cut body.erase
    | .bubble _ arity body => .bubble arity body.erase

  def CompiledItems.erase : CompiledItems d wires rels -> ItemSeq wires rels
    | .nil => .nil
    | .cons head tail => .cons head.erase tail.erase
end

namespace CompiledRegion

def localCount : CompiledRegion d origin wires rels -> Nat
  | .mk localWires _ _ => localWires

@[simp] theorem erase_localCount
    (region : CompiledRegion d origin wires rels) :
    region.erase.localCount = region.localCount := by
  cases region
  rfl

end CompiledRegion

def CompiledItem.origin (item : CompiledItem d wires rels) :
    LocalOccurrence d.regionCount d.nodeCount := by
  cases item with
  | node node _ => exact LocalOccurrence.node node
  | cut origin _ => exact LocalOccurrence.child origin
  | bubble origin _ _ => exact LocalOccurrence.child origin

namespace CompiledItems

def origins : CompiledItems d wires rels ->
    List (LocalOccurrence d.regionCount d.nodeCount)
  | .nil => []
  | .cons head tail => head.origin :: tail.origins

def length (items : CompiledItems d wires rels) : Nat := items.erase.length

def append : CompiledItems d wires rels -> CompiledItems d wires rels ->
    CompiledItems d wires rels
  | .nil, suffix => suffix
  | .cons head tail, suffix => .cons head (tail.append suffix)

def get : (items : CompiledItems d wires rels) ->
    Fin items.length -> CompiledItem d wires rels
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

@[simp] theorem erase_nil :
    erase (CompiledItems.nil : CompiledItems d wires rels) = .nil := rfl

@[simp] theorem erase_cons
    (head : CompiledItem d wires rels) (tail : CompiledItems d wires rels) :
    erase (.cons head tail) = .cons head.erase tail.erase := rfl

@[simp] theorem origins_nil :
    origins (CompiledItems.nil : CompiledItems d wires rels) = [] := rfl

@[simp] theorem origins_cons
    (head : CompiledItem d wires rels) (tail : CompiledItems d wires rels) :
    origins (.cons head tail) = head.origin :: tail.origins := rfl

@[simp] theorem erase_length (items : CompiledItems d wires rels) :
    items.erase.length = items.length := rfl

@[simp] theorem erase_append
    (initial suffix : CompiledItems d wires rels) :
    (initial.append suffix).erase = initial.erase.append suffix.erase :=
  match initial with
  | .nil => rfl
  | .cons _ tail => congrArg (ItemSeq.cons _) (erase_append tail suffix)

@[simp] theorem origins_append
    (initial suffix : CompiledItems d wires rels) :
    (initial.append suffix).origins = initial.origins ++ suffix.origins :=
  match initial with
  | .nil => rfl
  | .cons _ tail => congrArg (List.cons _) (origins_append tail suffix)

@[simp] theorem erase_get (items : CompiledItems d wires rels)
    (index : Fin items.length) :
    items.erase.get index = (items.get index).erase :=
  match items with
  | .nil => Fin.elim0 index
  | .cons _ tail => Fin.cases rfl (fun tailIndex => erase_get tail tailIndex) index

end CompiledItems

end VisualProof.Concrete.Elaboration
