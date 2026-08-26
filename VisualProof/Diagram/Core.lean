import VisualProof.Lambda.Syntax
import VisualProof.Theory.Signature

namespace VisualProof.Diagram

open VisualProof.Theory

mutual
  /-- A recursive region with an inherited wire interface and locally bound
  signature-indexed wires. -/
  inductive Region : List Sig → Type
    | mk {outer : List Sig} (locals : List Sig)
        (items : ItemSeq (outer ++ locals)) : Region outer

  /-- Direct recursive diagram content. Quantification is carried by typed
  regional wires rather than a second syntactic binder. -/
  inductive Item : List Sig → Type
    | atom {wires arguments : List Sig}
        (head : Var wires (.rel arguments))
        (ports : Vars wires arguments) : Item wires
    | identity {wires : List Sig} (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var wires signature) : Item wires
    | term {wires : List Sig} (output : Var wires .iota)
        (freeArity : Nat) (ports : Fin freeArity → Var wires .iota)
        (term : Lambda.Term 0 (Fin freeArity)) : Item wires
    | cut {wires : List Sig} (body : Region wires) : Item wires

  inductive ItemSeq : List Sig → Type
    | nil : ItemSeq wires
    | cons : Item wires → ItemSeq wires → ItemSeq wires
end

namespace Region

def locals : Region outer → List Sig
  | .mk locals _ => locals

def items (region : Region outer) : ItemSeq (outer ++ region.locals) :=
  match region with
  | .mk _ items => items

end Region

namespace ItemSeq

def length : ItemSeq wires → Nat
  | .nil => 0
  | .cons _ tail => Nat.succ tail.length

def get : (items : ItemSeq wires) → Fin items.length → Item wires
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

def append : ItemSeq wires → ItemSeq wires → ItemSeq wires
  | .nil, suffix => suffix
  | .cons item initial, suffix => .cons item (append initial suffix)

@[simp] theorem nil_append (items : ItemSeq wires) :
    append .nil items = items := rfl

@[simp] theorem append_nil : (items : ItemSeq wires) →
    append items .nil = items
  | .nil => rfl
  | .cons item tail => congrArg (ItemSeq.cons item) (append_nil tail)

@[simp] theorem append_assoc :
    (first second third : ItemSeq wires) →
    append (append first second) third = append first (append second third)
  | .nil, _, _ => rfl
  | .cons item tail, second, third =>
      congrArg (ItemSeq.cons item) (append_assoc tail second third)

@[simp] theorem length_append
    (first second : ItemSeq wires) :
    (first.append second).length = first.length + second.length :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ first => ∀ second,
      (first.append second).length = first.length + second.length)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun second => by simp [ItemSeq.append, ItemSeq.length])
    (fun _ _ _ induction second => by
      simp only [ItemSeq.append, ItemSeq.length]
      rw [induction second]
      omega)
    first second

end ItemSeq

end VisualProof.Diagram
