import VisualProof.Concrete.Elaboration.Context
import VisualProof.Diagram.Algebra

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
The compiler owns concrete identities.  Lexical wire and relation positions are
derived only when a checked symbolic tree is erased to intrinsic diagram syntax.
-/

mutual
  /-- One source-owned symbolic region.  Direct nodes and child regions remain
  separate because that is the concrete compiler's canonical block order. -/
  inductive CompiledRegion (d : Diagram) where
    | mk (origin : Fin d.regionCount)
        (nodes children : CompiledItems d) : CompiledRegion d

  /-- One symbolic item containing concrete source identities only. -/
  inductive CompiledItem (d : Diagram) where
    | atom (origin : Fin d.nodeCount) (binder : Fin d.regionCount)
        (arity : Nat) (ports : Fin arity → Fin d.wireCount) : CompiledItem d
    | identity (origin : Fin d.nodeCount) (arity : Nat)
        (ports : Fin arity → Fin d.wireCount) : CompiledItem d
    | cut (body : CompiledRegion d) : CompiledItem d
    | bubble (arity : Nat) (body : CompiledRegion d) : CompiledItem d

  /-- An ordered symbolic item sequence. -/
  inductive CompiledItems (d : Diagram) where
    | nil : CompiledItems d
    | cons (head : CompiledItem d) (tail : CompiledItems d) : CompiledItems d
end

namespace CompiledRegion

def origin : CompiledRegion d → Fin d.regionCount
  | .mk origin _ _ => origin

def nodeItems : CompiledRegion d → CompiledItems d
  | .mk _ nodes _ => nodes

def childItems : CompiledRegion d → CompiledItems d
  | .mk _ _ children => children

end CompiledRegion

def CompiledItem.origin : CompiledItem d →
    LocalOccurrence d.regionCount d.nodeCount
  | .atom node _ _ _ => .node node
  | .identity node _ _ => .node node
  | .cut body => .child body.origin
  | .bubble _ body => .child body.origin

namespace CompiledItems

def origins : CompiledItems d →
    List (LocalOccurrence d.regionCount d.nodeCount)
  | .nil => []
  | .cons head tail => head.origin :: tail.origins

def length : CompiledItems d → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

def append : CompiledItems d → CompiledItems d → CompiledItems d
  | .nil, suffix => suffix
  | .cons head tail, suffix => .cons head (tail.append suffix)

def get : (items : CompiledItems d) → Fin items.length → CompiledItem d
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

@[simp] theorem origins_nil :
    origins (CompiledItems.nil : CompiledItems d) = [] := rfl

@[simp] theorem origins_cons (head : CompiledItem d) (tail : CompiledItems d) :
    origins (.cons head tail) = head.origin :: tail.origins := rfl

@[simp] theorem length_nil :
    length (CompiledItems.nil : CompiledItems d) = 0 := rfl

@[simp] theorem length_cons (head : CompiledItem d) (tail : CompiledItems d) :
    length (.cons head tail) = tail.length + 1 := rfl

@[simp] theorem origins_append (initial suffix : CompiledItems d) :
    (initial.append suffix).origins = initial.origins ++ suffix.origins :=
  match initial with
  | .nil => rfl
  | .cons _ tail => congrArg (List.cons _) (origins_append tail suffix)

@[simp] theorem length_eq_origins_length (items : CompiledItems d) :
    items.length = items.origins.length :=
  match items with
  | .nil => rfl
  | .cons _ tail => by simp [length, length_eq_origins_length tail]

/-- The two stable subsequences determined by one origin classifier. -/
structure Partition (items : CompiledItems d) where
  retained : CompiledItems d
  material : CompiledItems d

def partition (classifier :
    LocalOccurrence d.regionCount d.nodeCount → Bool) :
    (items : CompiledItems d) → Partition items
  | .nil => ⟨.nil, .nil⟩
  | .cons head tail =>
      let divided := tail.partition classifier
      if classifier head.origin then
        ⟨divided.retained, .cons head divided.material⟩
      else
        ⟨.cons head divided.retained, divided.material⟩

@[simp] theorem partition_retained_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d) :
    (items.partition classifier).retained.origins =
      items.origins.filter fun origin => !classifier origin :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_retained_origins]

@[simp] theorem partition_material_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d) :
    (items.partition classifier).material.origins =
      items.origins.filter classifier :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_material_origins]

theorem partition_retained_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d) :
    List.Sublist (items.partition classifier).retained.origins items.origins := by
  rw [partition_retained_origins]
  exact List.filter_sublist

theorem partition_material_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d) :
    List.Sublist (items.partition classifier).material.origins items.origins := by
  rw [partition_material_origins]
  exact List.filter_sublist

theorem partition_origins_perm
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d) :
    items.origins.Perm
      ((items.partition classifier).retained.origins ++
        (items.partition classifier).material.origins) :=
  match items with
  | .nil => .nil
  | .cons head tail => by
      cases hclassifier : classifier head.origin with
      | false => simpa [partition, hclassifier] using
          (partition_origins_perm classifier tail).cons head.origin
      | true =>
          exact ((partition_origins_perm classifier tail).cons
            head.origin).trans (by
              simpa [partition, hclassifier] using
                (List.perm_middle (a := head.origin)).symm)

end CompiledItems

namespace CompiledRegion

def items (region : CompiledRegion d) : CompiledItems d :=
  region.nodeItems.append region.childItems

@[simp] theorem items_mk (origin : Fin d.regionCount)
    (nodes children : CompiledItems d) :
    items (.mk origin nodes children : CompiledRegion d) =
      nodes.append children := rfl

end CompiledRegion

/-! Source validity is proof-only and is derived by the sole compiler. -/

def bubbleParent (d : Diagram) (binder : Fin d.regionCount) :
    Fin d.regionCount :=
  match d.regions binder with
  | .bubble parent _ => parent
  | _ => d.root

@[simp] theorem bubbleParent_of_bubble
    (shape : d.regions binder = .bubble parent arity) :
    bubbleParent d binder = parent := by
  simp [bubbleParent, shape]

mutual
  def CompiledRegion.Valid : (region : CompiledRegion d) → Prop
    | .mk origin nodes children =>
        nodes.origins = localNodeOccurrences d origin ∧
        children.origins = localChildOccurrences d origin ∧
        nodes.ValidAt origin ∧ children.ValidAt origin

  def CompiledItem.ValidAt (parent : Fin d.regionCount) :
      CompiledItem d → Prop
    | .atom origin binder arity ports =>
        d.nodes origin = .atom parent binder ∧
        d.regions binder = .bubble (bubbleParent d binder) arity ∧
        d.Encloses binder parent ∧
        ∀ index, d.EndpointOccurs (ports index) ⟨origin, .arg index⟩
    | .identity origin arity ports =>
        d.nodes origin = .identity parent arity ∧
        ∀ index, d.EndpointOccurs (ports index) ⟨origin, .arg index⟩
    | .cut body =>
        d.regions body.origin = .cut parent ∧ body.Valid
    | .bubble arity body =>
        d.regions body.origin = .bubble parent arity ∧ body.Valid

  def CompiledItems.ValidAt (parent : Fin d.regionCount) :
      CompiledItems d → Prop
    | .nil => True
    | .cons head tail => head.ValidAt parent ∧ tail.ValidAt parent
end

/-! Intrinsic erasure is the sole concrete-identity-to-position boundary. -/

mutual
  noncomputable def CompiledRegion.erase
      (region : CompiledRegion d) (valid : region.Valid)
      (hwf : d.WellFormed )
      (outer locals : WireContext d) (rels : RelCtx)
      (binders : BinderContext d rels)
      (exact : (outer ++ locals).Exact region.origin)
      (covers : binders.Covers region.origin) :
      Region outer.length rels := by
    cases region with
    | mk origin nodes children =>
        let erased :=
          (CompiledItems.erase _ valid.2.2.1 hwf (outer ++ locals) rels
            binders exact covers).append
          (CompiledItems.erase _ valid.2.2.2 hwf (outer ++ locals) rels
            binders exact covers)
        exact .mk locals.length
          (erased.castWiresEq (by simp only [List.length_append]))

  noncomputable def CompiledItem.erase
      (item : CompiledItem d) {parent : Fin d.regionCount}
      (valid : item.ValidAt parent) (hwf : d.WellFormed )
      (context : WireContext d) (rels : RelCtx)
      (binders : BinderContext d rels)
      (exact : context.Exact parent) (covers : binders.Covers parent) :
      Item context.length rels := by
    cases item with
    | atom origin binder arity ports =>
        exact .atom
          (binders.relationAt covers binder (bubbleParent d binder) arity
            valid.2.1 valid.2.2.1)
          (fun index => context.position exact _ (by
            have visible := hwf.wire_scopes_enclose _ _ (valid.2.2.2 index)
            rw [valid.1] at visible
            exact visible))
    | identity origin arity ports =>
        exact .identity arity (fun index => context.position exact _ (by
          have visible := hwf.wire_scopes_enclose _ _ (valid.2 index)
          rw [valid.1] at visible
          exact visible))
    | cut body =>
        have parentShape : (d.regions body.origin).parent? = some parent := by
          simp [valid.1, CRegion.parent?]
        exact .cut (CompiledRegion.erase _ valid.2 hwf context
          (exactScopeWires d body.origin) rels binders
          (exact.extend_child hwf parentShape)
          (BinderContext.covers_cut_child covers valid.1))
    | bubble arity body =>
        have parentShape : (d.regions body.origin).parent? = some parent := by
          simp [valid.1, CRegion.parent?]
        exact .bubble arity (CompiledRegion.erase _ valid.2 hwf context
          (exactScopeWires d body.origin) (arity :: rels)
          (binders.push body.origin arity)
          (exact.extend_child hwf parentShape)
          (BinderContext.push_covers_bubble_child covers valid.1))

  noncomputable def CompiledItems.erase
      (items : CompiledItems d) {parent : Fin d.regionCount}
      (valid : items.ValidAt parent) (hwf : d.WellFormed )
      (context : WireContext d) (rels : RelCtx)
      (binders : BinderContext d rels)
      (exact : context.Exact parent) (covers : binders.Covers parent) :
      ItemSeq context.length rels := by
    cases items with
    | nil => exact .nil
    | cons head tail =>
        exact .cons
          (CompiledItem.erase _ valid.1 hwf context rels binders exact covers)
          (CompiledItems.erase _ valid.2 hwf context rels binders exact covers)
end

@[simp] theorem CompiledRegion.erase_localCount
    (region : CompiledRegion d) (valid : region.Valid)
    (hwf : d.WellFormed ) (outer locals : WireContext d) (rels : RelCtx)
    (binders : BinderContext d rels)
    (exact : (outer ++ locals).Exact region.origin)
    (covers : binders.Covers region.origin) :
    (region.erase valid hwf outer locals rels binders exact covers).localCount =
      locals.length := by
  cases region
  rfl

end VisualProof.Concrete.Elaboration
