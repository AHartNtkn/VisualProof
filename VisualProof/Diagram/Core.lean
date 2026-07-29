import VisualProof.Model

namespace VisualProof

/-- An intrinsically signature-correct reference into an ordered definition list. -/
inductive DefVar : List (List Sig) → List Sig → Type
  | here : DefVar (args :: rest) args
  | there : DefVar rest args → DefVar (head :: rest) args

/-- A typed map between heterogeneous wire contexts. -/
def WireRenaming (source target : List Sig) : Type :=
  {sig : Sig} → Var source sig → Var target sig

namespace WireRenaming

/-- Keep a newly bound variable fixed while renaming the outer context. -/
def lift (rho : WireRenaming source target) (bound : Sig) :
    WireRenaming (bound :: source) (bound :: target) :=
  fun {_} var =>
    match var with
    | .here => .here
    | .there outer => .there (rho outer)

end WireRenaming

/-- A typed map between ordered definition contexts. -/
def DefinitionRenaming (source target : List (List Sig)) : Type :=
  {args : List Sig} → DefVar source args → DefVar target args

namespace Vars

/-- Rename every variable in an ordered typed variable tuple. -/
def rename (rho : WireRenaming source target) :
    Vars source args → Vars target args
  | .nil => .nil
  | .cons head tail => .cons (rho head) (rename rho tail)

end Vars

mutual
  /-- A region contains an intrinsically scoped sequence of logical items. -/
  inductive Region (defs : List (List Sig)) : List Sig → Type
    | mk {ctx : List Sig} (items : ItemSeq defs ctx) : Region defs ctx

  /-- The complete intrinsic zero-signature diagram vocabulary. -/
  inductive Item (defs : List (List Sig)) : List Sig → Type
    | atom {ctx args} (head : Var ctx (.rel args))
        (arguments : Vars ctx args) : Item defs ctx
    | named {ctx args} (definition : DefVar defs args)
        (arguments : Vars ctx args) : Item defs ctx
    | identity (sig : Sig) (ports : List (Var ctx sig))
        (atLeastTwo : 2 ≤ ports.length) : Item defs ctx
    | cut (body : Region defs ctx) : Item defs ctx
    | bind (sig : Sig) (body : Region defs (sig :: ctx)) : Item defs ctx

  /-- Ordered conjunction of intrinsic items. -/
  inductive ItemSeq (defs : List (List Sig)) : List Sig → Type
    | nil : ItemSeq defs ctx
    | cons (head : Item defs ctx) (tail : ItemSeq defs ctx) :
        ItemSeq defs ctx
end

/-- The empty diagram in any typed wire and definition context. -/
def blank : Region defs ctx := .mk .nil

namespace ItemSeq

/-- Concatenate two intrinsic conjunctions. -/
def append : ItemSeq defs ctx → ItemSeq defs ctx → ItemSeq defs ctx
  | .nil, suffix => suffix
  | .cons head tail, suffix => .cons head (append tail suffix)

@[simp] theorem nil_append (items : ItemSeq defs ctx) :
    append .nil items = items := rfl

@[simp] theorem append_nil :
    (items : ItemSeq defs ctx) → append items .nil = items
  | .nil => rfl
  | .cons head tail => congrArg (ItemSeq.cons head) (append_nil tail)

@[simp] theorem append_assoc :
    (first second third : ItemSeq defs ctx) →
      append (append first second) third = append first (append second third)
  | .nil, _, _ => rfl
  | .cons head tail, second, third =>
      congrArg (ItemSeq.cons head) (append_assoc tail second third)

end ItemSeq

namespace Region

/-- Conjoin two same-scope regions by appending their intrinsic item sequences. -/
def conjoin (left right : Region defs ctx) : Region defs ctx :=
  match left, right with
  | .mk leftItems, .mk rightItems =>
      .mk (leftItems.append rightItems)

end Region

mutual
  /-- Rename every wire occurrence, lifting safely through binders. -/
  def Region.renameWires (rho : WireRenaming source target) :
      Region defs source → Region defs target
    | .mk items => .mk (items.renameWires rho)

  /-- Rename every wire occurrence in one item. -/
  def Item.renameWires (rho : WireRenaming source target) :
      Item defs source → Item defs target
    | .atom head arguments =>
        .atom (rho head) (arguments.rename rho)
    | .named definition arguments =>
        .named definition (arguments.rename rho)
    | .identity sig ports atLeastTwo =>
        .identity sig (ports.map (rho (sig := sig))) (by
          simpa using atLeastTwo)
    | .cut body => .cut (body.renameWires rho)
    | .bind sig body =>
        .bind sig (body.renameWires (WireRenaming.lift rho sig))

  /-- Rename every wire occurrence in an item sequence. -/
  def ItemSeq.renameWires (rho : WireRenaming source target) :
      ItemSeq defs source → ItemSeq defs target
    | .nil => .nil
    | .cons head tail =>
        .cons (head.renameWires rho) (tail.renameWires rho)
end

mutual
  /-- Rename every named-definition reference in a region. -/
  def Region.renameDefinitions (rho : DefinitionRenaming source target) :
      Region source ctx → Region target ctx
    | .mk items => .mk (items.renameDefinitions rho)

  /-- Rename every named-definition reference in one item. -/
  def Item.renameDefinitions (rho : DefinitionRenaming source target) :
      Item source ctx → Item target ctx
    | .atom head arguments => .atom head arguments
    | .named definition arguments => .named (rho definition) arguments
    | .identity sig ports atLeastTwo =>
        .identity sig ports atLeastTwo
    | .cut body => .cut (body.renameDefinitions rho)
    | .bind sig body => .bind sig (body.renameDefinitions rho)

  /-- Rename every named-definition reference in an item sequence. -/
  def ItemSeq.renameDefinitions (rho : DefinitionRenaming source target) :
      ItemSeq source ctx → ItemSeq target ctx
    | .nil => .nil
    | .cons head tail =>
        .cons (head.renameDefinitions rho) (tail.renameDefinitions rho)
end

/--
A binder-safe typed substitution. In the variable-only intrinsic language,
substitution maps each source variable to a target variable of the same
signature; binder lifting prevents capture.
-/
abbrev WireSubstitution := WireRenaming

/-- Apply a typed, capture-avoiding substitution to a region. -/
def Region.substitute (substitution : WireSubstitution source target)
    (region : Region defs source) : Region defs target :=
  region.renameWires substitution

/-- Apply a typed, capture-avoiding substitution to one item. -/
def Item.substitute (substitution : WireSubstitution source target)
    (item : Item defs source) : Item defs target :=
  item.renameWires substitution

/-- Apply a typed, capture-avoiding substitution to an item sequence. -/
def ItemSeq.substitute (substitution : WireSubstitution source target)
    (items : ItemSeq defs source) : ItemSeq defs target :=
  items.renameWires substitution

namespace Item

/-- Binary identity with its intrinsic arity witness discharged definitionally. -/
def binaryIdentity (sig : Sig) (left right : Var ctx sig) : Item defs ctx :=
  .identity sig [left, right] (Nat.le_refl 2)

theorem identity_ports_nonempty (atLeastTwo : 2 ≤ ports.length) :
    ports ≠ [] := by
  intro empty
  subst ports
  simp at atLeastTwo

theorem identity_ports_not_singleton (atLeastTwo : 2 ≤ ports.length) :
    ports ≠ [port] := by
  intro singleton
  subst ports
  simp at atLeastTwo

end Item

end VisualProof
