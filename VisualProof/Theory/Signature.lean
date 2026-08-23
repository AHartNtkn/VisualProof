namespace VisualProof.Theory

/-- Recursive signatures for individual and higher-order relation wires. -/
inductive Sig where
  | iota
  | rel (arguments : List Sig)
  deriving Repr

/-- An intrinsically signature-correct de Bruijn wire reference. -/
inductive Var : List Sig → Sig → Type
  | here : Var (signature :: rest) signature
  | there : Var rest signature → Var (head :: rest) signature

namespace Var

def index : Var context signature → Fin context.length
  | .here => 0
  | .there tail => tail.index.succ

theorem eq_of_index_eq
    (left right : Var context signature) (equal : left.index = right.index) :
    left = right := by
  induction context with
  | nil => exact nomatch left
  | cons head tail induction =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have values := congrArg Fin.val equal
              simp [index] at values
      | there left =>
          cases right with
          | here =>
              have values := congrArg Fin.val equal
              simp [index] at values
          | there right =>
              exact congrArg Var.there (induction left right (by
                apply Fin.ext
                have values := congrArg Fin.val equal
                simpa [index] using values))

instance : DecidableEq (Var context signature) :=
  fun left right => decidable_of_iff (left.index = right.index)
    ⟨fun equal => eq_of_index_eq left right equal,
      fun equal => congrArg index equal⟩

/-- Recover the intrinsically typed wire at a context position. -/
def ofIndex (position : Fin context.length) :
    Var context (context.get position) :=
  match context with
  | [] => Fin.elim0 position
  | _ :: _ => Fin.cases .here (fun tail => .there (ofIndex tail)) position

@[simp] theorem index_ofIndex {context : List Sig}
    (position : Fin context.length) :
    (ofIndex position).index = position := by
  induction context with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => by
        change (ofIndex rest).index.succ = rest.succ
        exact congrArg Fin.succ (induction rest)) position

/-- Embed a wire from the left side of an appended context. -/
def appendLeft (wire : Var left signature) (right : List Sig) :
    Var (left ++ right) signature :=
  match wire with
  | .here => .here
  | .there tail => .there (tail.appendLeft right)

@[simp] theorem index_appendLeft
    (wire : Var left signature) (right : List Sig) :
    (wire.appendLeft right).index.val = wire.index.val := by
  induction wire with
  | here => rfl
  | there tail induction =>
      simp only [appendLeft, index, Fin.val_succ]
      rw [induction]

/-- Embed a wire from the right side of an appended context. -/
def appendRight (left : List Sig) (wire : Var right signature) :
    Var (left ++ right) signature :=
  match left with
  | [] => wire
  | _ :: tail => .there (appendRight tail wire)

@[simp] theorem index_appendRight
    (left : List Sig) (wire : Var right signature) :
    (appendRight left wire).index.val = left.length + wire.index.val := by
  induction left with
  | nil => simp [appendRight]
  | cons head tail induction =>
      simp only [appendRight, index, List.length_cons, Fin.val_succ]
      rw [induction]
      omega

/-- Eliminate an appended context by supplying a map for each side. -/
def appendMap
    (leftMap : ∀ {signature}, Var left signature → Var target signature)
    (rightMap : ∀ {signature}, Var right signature → Var target signature) :
    ∀ {signature}, Var (left ++ right) signature → Var target signature :=
  match left with
  | [] => rightMap
  | _ :: _ => fun wire =>
      match wire with
      | .here => leftMap .here
      | .there rest =>
          appendMap (fun wire => leftMap (.there wire)) rightMap rest

@[simp] theorem appendMap_left
    (leftMap : ∀ {signature}, Var left signature → Var target signature)
    (rightMap : ∀ {signature}, Var right signature → Var target signature)
    (wire : Var left signature) :
    appendMap leftMap rightMap (wire.appendLeft right) = leftMap wire := by
  induction wire with
  | here => rfl
  | there rest induction =>
      exact induction (leftMap := fun wire => leftMap (.there wire))

@[simp] theorem appendMap_right
    (leftMap : ∀ {signature}, Var left signature → Var target signature)
    (rightMap : ∀ {signature}, Var right signature → Var target signature)
    (wire : Var right signature) :
    appendMap leftMap rightMap (appendRight left wire) = rightMap wire := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      exact induction (leftMap := fun wire => leftMap (.there wire))

theorem appendCases
    (motive : ∀ {signature}, Var (left ++ right) signature → Prop)
    (leftCase : ∀ {signature} (wire : Var left signature),
      motive (wire.appendLeft right))
    (rightCase : ∀ {signature} (wire : Var right signature),
      motive (appendRight left wire)) :
    ∀ {signature} (wire : Var (left ++ right) signature), motive wire := by
  induction left with
  | nil =>
      intro signature wire
      exact rightCase wire
  | cons head tail induction =>
      intro signature wire
      cases wire with
      | here => exact leftCase .here
      | there rest =>
          exact induction
            (motive := fun wire => motive (.there wire))
            (leftCase := fun wire => leftCase (.there wire))
            (rightCase := rightCase) rest

end Var

/-- An ordered tuple of typed wire references. -/
inductive Vars (context : List Sig) : List Sig → Type
  | nil : Vars context []
  | cons : Var context signature → Vars context rest →
      Vars context (signature :: rest)

namespace Vars

/-- Concatenate two ordered typed wire tuples. -/
def extend : Vars context left → Vars context right →
    Vars context (left ++ right)
  | .nil, right => right
  | .cons head tail, right => .cons head (extend tail right)

theorem extend_assoc
    (first : Vars context firstSignatures)
    (second : Vars context secondSignatures)
    (third : Vars context thirdSignatures) :
    HEq (extend (extend first second) third)
      (extend first (extend second third)) := by
  induction first with
  | nil => rfl
  | @cons signature rest head tail induction =>
      simp only [extend]
      congr 1
      exact List.append_assoc _ _ _

def get : (variables : Vars context signatures) →
    (index : Fin signatures.length) → Var context (signatures.get index)
  | .cons head _, ⟨0, _⟩ => head
  | .cons _ tail, ⟨index + 1, bound⟩ =>
      tail.get ⟨index, Nat.lt_of_succ_lt_succ bound⟩

theorem extend_nil (variables : Vars context signatures) :
    HEq (extend variables .nil) variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [extend]
      congr
      exact List.append_nil _

def countIndex (wireIndex : Nat) : Vars context signatures → Nat
  | .nil => 0
  | .cons head tail =>
      (if head.index.val = wireIndex then 1 else 0) +
        tail.countIndex wireIndex

def map (rename : ∀ {signature}, Var source signature → Var target signature) :
    Vars source signatures → Vars target signatures
  | .nil => .nil
  | .cons head tail => .cons (rename head) (tail.map rename)

@[simp] theorem map_extend
    (left : Vars source leftSignatures)
    (right : Vars source rightSignatures)
    (rename : ∀ {signature}, Var source signature → Var target signature) :
    (extend left right).map rename =
      extend (left.map rename) (right.map rename) := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [extend, map]
      exact congrArg (Vars.cons (rename head)) induction

@[simp] theorem map_map
    (variables : Vars source signatures)
    (first : ∀ {signature}, Var source signature → Var middle signature)
    (second : ∀ {signature}, Var middle signature → Var target signature) :
    (variables.map first).map second =
      variables.map (fun wire => second (first wire)) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [map]
      exact congrArg (Vars.cons (second (first head))) induction

theorem map_congr
    (variables : Vars source signatures)
    (first second : ∀ {signature},
      Var source signature → Var target signature)
    (equal : ∀ {signature} (wire : Var source signature),
      first wire = second wire) :
    variables.map first = variables.map second := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [map]
      rw [equal head, induction]

theorem countIndex_get_positive
    (variables : Vars context signatures)
    (position : Fin signatures.length) :
    0 < variables.countIndex (variables.get position).index.val := by
  induction variables with
  | nil => exact Fin.elim0 position
  | @cons signature rest head tail induction =>
      refine Fin.cases ?_ (fun index => ?_) position
      · change 0 < (if head.index.val = head.index.val then 1 else 0) +
          tail.countIndex head.index.val
        simp only [if_pos]
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using
          Nat.zero_lt_succ (tail.countIndex head.index.val)
      · change 0 <
          (if head.index.val = (tail.get index).index.val then 1 else 0) +
            tail.countIndex (tail.get index).index.val
        exact Nat.lt_of_lt_of_le (induction index) (Nat.le_add_left _ _)

/-- Renamings with the same raw de Bruijn action preserve the same tuple
incidence count, even when their codomain contexts differ. -/
theorem countIndex_map_eq_of_index_eq
    (variables : Vars source signatures)
    (first : ∀ {signature}, Var source signature → Var firstTarget signature)
    (second : ∀ {signature}, Var source signature → Var secondTarget signature)
    (sameIndex : ∀ {signature} (wire : Var source signature),
      (first wire).index.val = (second wire).index.val)
    (wireIndex : Nat) :
    (variables.map first).countIndex wireIndex =
      (variables.map second).countIndex wireIndex := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [map, countIndex, sameIndex head, induction]

@[simp] theorem countIndex_map_appendLeft_nil
    (variables : Vars context signatures) (wireIndex : Nat) :
    (variables.map fun wire => wire.appendLeft []).countIndex wireIndex =
      variables.countIndex wireIndex := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [map, countIndex, Var.index_appendLeft, induction]

end Vars

/-- A signature-preserving map between typed wire contexts. -/
structure WireRenaming (source target : List Sig) where
  apply : ∀ {signature}, Var source signature → Var target signature

instance : CoeFun (WireRenaming source target)
    (fun _ => ∀ {signature}, Var source signature → Var target signature) :=
  ⟨WireRenaming.apply⟩

namespace WireRenaming

@[ext] theorem ext
    (left right : WireRenaming source target)
    (applyEq : ∀ {signature} (wire : Var source signature),
      left wire = right wire) : left = right := by
  cases left with
  | mk left =>
      cases right with
      | mk right =>
          congr
          apply @funext
          intro signature
          funext wire
          exact applyEq wire

def id : WireRenaming context context := ⟨fun wire => wire⟩

def comp (second : WireRenaming middle target)
    (first : WireRenaming source middle) : WireRenaming source target :=
  ⟨fun wire => second (first wire)⟩

/-- Extend a renaming across locally bound wires, preserving those locals. -/
def appendRight (rename : WireRenaming source target)
    (locals : List Sig) : WireRenaming (source ++ locals) (target ++ locals) :=
  ⟨Var.appendMap
    (fun wire => (rename wire).appendLeft locals)
    (fun wire => Var.appendRight target wire)⟩

theorem appendRight_id_apply (locals : List Sig)
    (wire : Var (source ++ locals) signature) :
    appendRight id locals wire = wire := by
  apply Var.appendCases
    (motive := fun wire => appendRight id locals wire = wire)
  · intro signature inherited
    simp [appendRight, id]
  · intro signature localWire
    simp [appendRight]

theorem appendRight_comp_apply
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) (locals : List Sig)
    (wire : Var (source ++ locals) signature) :
    appendRight second locals (appendRight first locals wire) =
      appendRight (comp second first) locals wire := by
  apply Var.appendCases
    (motive := fun wire =>
      appendRight second locals (appendRight first locals wire) =
        appendRight (comp second first) locals wire)
  · intro signature inherited
    simp [appendRight, comp]
  · intro signature localWire
    simp [appendRight]

end WireRenaming

end VisualProof.Theory
