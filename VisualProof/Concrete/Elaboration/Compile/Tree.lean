import VisualProof.Concrete.Elaboration.Context
import VisualProof.Diagram.Algebra
import VisualProof.Diagram.RenamingIsomorphism

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

/-- The two stable subsequences determined by one origin classifier.  This is
derived data: callers retain the original annotated sequence as authority. -/
structure Partition (items : CompiledItems d wires rels) where
  retained : CompiledItems d wires rels
  material : CompiledItems d wires rels

/-- Stably partition annotated items without descending into child bodies. -/
def partition (classifier :
    LocalOccurrence d.regionCount d.nodeCount → Bool) :
    (items : CompiledItems d wires rels) → Partition items
  | .nil => ⟨.nil, .nil⟩
  | .cons head tail =>
      let divided := tail.partition classifier
      if classifier head.origin then
        ⟨divided.retained, .cons head divided.material⟩
      else
        ⟨.cons head divided.retained, divided.material⟩

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

@[simp] theorem partition_retained_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d wires rels) :
    (items.partition classifier).retained.origins =
      items.origins.filter fun origin => !classifier origin :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_retained_origins]

@[simp] theorem partition_material_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d wires rels) :
    (items.partition classifier).material.origins =
      items.origins.filter classifier :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_material_origins]

theorem partition_retained_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d wires rels) :
    List.Sublist (items.partition classifier).retained.origins
      items.origins := by
  rw [partition_retained_origins]
  exact List.filter_sublist

theorem partition_material_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d wires rels) :
    List.Sublist (items.partition classifier).material.origins
      items.origins := by
  rw [partition_material_origins]
  exact List.filter_sublist

theorem partition_origins_perm
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d wires rels) :
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

private noncomputable def intrinsicTrans
    {source middle target : ItemSeq wires rels}
    (first : ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels source middle)
    (second : ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels middle target) :
    ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels source target := by
  have composed := first.trans second
  have wireEquality :
      (FiniteEquiv.refl (Fin wires)).trans
          (FiniteEquiv.refl (Fin wires)) =
        FiniteEquiv.refl (Fin wires) := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [wireEquality] at composed
  exact composed

/-- The canonical intrinsic braid from compiler order to the stable retained
block followed by the stable material block. -/
noncomputable def partitionFactorization
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool) :
    (items : CompiledItems d wires rels) →
      ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels items.erase
        (((items.partition classifier).retained.append
          (items.partition classifier).material).erase)
  | .nil => ItemSeqIso.refl .nil
  | .cons head tail => by
      let tailFactorization := tail.partitionFactorization classifier
      let headItems : ItemSeq wires rels := .cons head.erase .nil
      let lifted := (ItemSeqIso.refl headItems).append tailFactorization
      cases hclassifier : classifier head.origin with
      | false =>
          simpa [partition, hclassifier, headItems, CompiledItems.erase_append,
            ItemSeq.append_assoc] using lifted
      | true =>
          let retained := (tail.partition classifier).retained.erase
          let material := (tail.partition classifier).material.erase
          let rotated :=
            (ItemSeqIso.appendCommRename headItems retained
              (FiniteEquiv.refl (Fin wires))).append
                (ItemSeqIso.refl material)
          apply intrinsicTrans lifted
          simpa [partition, hclassifier, headItems, retained, material,
            CompiledItems.erase_append, ItemSeq.append_assoc,
            FiniteEquiv.refl, ItemSeq.renameWires_id] using rotated

end CompiledItems

end VisualProof.Concrete.Elaboration
