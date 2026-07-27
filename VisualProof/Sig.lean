namespace VisualProof

universe u

/-- The recursively signature-indexed wire vocabulary. -/
inductive Sig where
  | iota
  | rel (args : List Sig)
  deriving Repr

namespace Sig

mutual
  /-- Structural Boolean equality for signatures. -/
  def beq : Sig → Sig → Bool
    | .iota, .iota => true
    | .rel left, .rel right => beqList left right
    | _, _ => false

  /-- Structural Boolean equality for signature lists. -/
  def beqList : List Sig → List Sig → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        beq left right && beqList lefts rights
    | _, _ => false
end

mutual
  @[simp] theorem beq_eq_true_iff (left right : Sig) :
      beq left right = true ↔ left = right := by
    cases left <;> cases right
    · simp [beq]
    · simp [beq]
    · simp [beq]
    · simp only [beq, beqList_eq_true_iff, Sig.rel.injEq]

  @[simp] theorem beqList_eq_true_iff (left right : List Sig) :
      beqList left right = true ↔ left = right := by
    cases left <;> cases right
    · simp [beqList]
    · simp [beqList]
    · simp [beqList]
    · simp only [beqList, Bool.and_eq_true, beq_eq_true_iff,
        beqList_eq_true_iff, List.cons.injEq]
end

instance : BEq Sig where
  beq := Sig.beq

instance : LawfulBEq Sig where
  eq_of_beq := by
    intro left right h
    exact (beq_eq_true_iff left right).mp h
  rfl := by
    intro sig
    exact (beq_eq_true_iff sig sig).mpr rfl

mutual
  /-- The full semantic domain of a wire signature over an individual carrier. -/
  def denote (Carrier : Type u) : Sig → Type u
    | .iota => Carrier
    | .rel args => Args Carrier args → Prop

  /-- A signature-indexed tuple of semantic values. -/
  def Args (Carrier : Type u) : List Sig → Type u
    | [] => PUnit
    | sig :: rest => denote Carrier sig × Args Carrier rest
end

theorem denote_nonempty (carrier_nonempty : Nonempty Carrier) :
    (sig : Sig) → Nonempty (denote Carrier sig)
  | .iota => carrier_nonempty
  | .rel _ => ⟨fun _ => True⟩

end Sig

/-- A typed de Bruijn variable into a signature context. -/
inductive Var : List Sig → Sig → Type
  | here : Var (sig :: rest) sig
  | there : Var rest sig → Var (head :: rest) sig

namespace Var

/-- Embed a variable into a context extended on the right. -/
def appendLeft (var : Var left sig) (right : List Sig) :
    Var (left ++ right) sig :=
  match var with
  | .here => .here
  | .there tail => .there (appendLeft tail right)

/-- Embed a variable from the right side of an appended context. -/
def appendRight (left : List Sig) (var : Var right sig) :
    Var (left ++ right) sig :=
  match left with
  | [] => var
  | _ :: tail => .there (appendRight tail var)

end Var

/-- An ordered tuple of typed variables. -/
inductive Vars (ctx : List Sig) : List Sig → Type
  | nil : Vars ctx []
  | cons : Var ctx sig → Vars ctx rest → Vars ctx (sig :: rest)

namespace Sig.Args

/-- Typed lookup from a semantic tuple. -/
def lookup {Carrier : Type u} {ctx : List Sig}
    (values : Sig.Args Carrier ctx) {sig : Sig} (var : Var ctx sig) :
    Sig.denote Carrier sig :=
  match var, values with
  | .here, ⟨head, _⟩ => head
  | .there tail, ⟨_, rest⟩ => lookup rest tail

@[simp] theorem lookup_here
    (head : Sig.denote Carrier sig) (tail : Sig.Args Carrier rest) :
    lookup (Carrier := Carrier) (ctx := sig :: rest)
      (show Sig.Args Carrier (sig :: rest) from (head, tail))
      (Var.here : Var (sig :: rest) sig) = head := rfl

@[simp] theorem lookup_there
    (head : Sig.denote Carrier other) (tail : Sig.Args Carrier rest)
    (var : Var rest sig) :
    lookup (Carrier := Carrier) (ctx := other :: rest)
      (show Sig.Args Carrier (other :: rest) from (head, tail))
      (Var.there var) =
        lookup (Carrier := Carrier) (ctx := rest) tail var := rfl

end Sig.Args

end VisualProof
