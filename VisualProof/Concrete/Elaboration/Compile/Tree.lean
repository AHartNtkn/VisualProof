import VisualProof.Concrete.Elaboration.Context
import VisualProof.Diagram.Algebra
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
The sole compiler result is indexed by the exact root or nested compiler call.
Concrete occurrence origins remain ordinary owned data, while recursive child
results carry the exact wire context, relation context, and binder context used
by their compiler invocation.
-/

/-- The exact inputs of one successful root or nested region compilation. -/
inductive CompilerCall (d : Diagram) where
  | root (ambient locals : WireContext d)
  | nested (origin : Fin d.regionCount)
      (context : WireContext d) (rels : RelCtx)
      (binders : BinderContext d rels)

namespace CompilerCall

def origin : CompilerCall d → Fin d.regionCount
  | .root _ _ => d.root
  | .nested origin _ _ _ => origin

def outerContext : CompilerCall d → WireContext d
  | .root ambient _ => ambient
  | .nested _ context _ _ => context

def localContext : CompilerCall d → WireContext d
  | .root _ locals => locals
  | .nested origin _ _ _ => exactScopeWires d origin

def fullContext (call : CompilerCall d) : WireContext d :=
  call.outerContext ++ call.localContext

def rels : CompilerCall d → RelCtx
  | .root _ _ => []
  | .nested _ _ rels _ => rels

def binders : (call : CompilerCall d) → BinderContext d call.rels
  | .root _ _ => BinderContext.empty
  | .nested _ _ _ binders => binders

theorem fullContext_length (call : CompilerCall d) :
    call.fullContext.length =
      call.outerContext.length + call.localContext.length := by
  simp [fullContext]

def castFullItems {rels : RelCtx} (call : CompilerCall d)
    (items : ItemSeq call.fullContext.length rels) :
    ItemSeq (call.outerContext.length + call.localContext.length) rels :=
  items.castWiresEq call.fullContext_length

def finish (call : CompilerCall d)
    (items : ItemSeq call.fullContext.length call.rels) :
    Region call.outerContext.length call.rels := by
  exact .mk call.localContext.length (call.castFullItems items)

/-- Finishing a nested compiler call commutes with relation renaming; binder
contexts do not affect the intrinsic region produced by `finish`. -/
theorem finishNested_renameRelations {d : Diagram}
    {sourceRels targetRels : RelCtx} (origin : Fin d.regionCount)
    (context : WireContext d)
    (sourceBinders : BinderContext d sourceRels)
    (targetBinders : BinderContext d targetRels)
    (items : ItemSeq (context.extend origin).length sourceRels)
    (relationMap : RelationRenaming sourceRels targetRels) :
    (CompilerCall.nested origin context targetRels targetBinders).finish
        (items.renameRelations relationMap) =
      ((CompilerCall.nested origin context sourceRels sourceBinders).finish
        items).renameRelations relationMap := by
  simp only [finish, castFullItems, Region.renameRelations,
    ItemSeq.castWiresEq_eq_renameWires]
  apply congrArg (Region.mk (exactScopeWires d origin).length)
  exact (ItemSeq.renameWires_renameRelations items _ relationMap).symm

end CompilerCall

mutual
  /-- The sole successful compiler result, indexed by its exact call. -/
  inductive CompiledRegion (d : Diagram) : CompilerCall d → Type
    | mk {call : CompilerCall d}
        (items : CompiledItems d call.fullContext call.rels call.binders) :
        CompiledRegion d call

  /-- One compiled occurrence with an ordinary concrete origin. -/
  inductive CompiledItem (d : Diagram) :
      (context : WireContext d) → (rels : RelCtx) →
      BinderContext d rels → Type
    | node {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} (origin : Fin d.nodeCount)
        (item : Item context.length rels) :
        CompiledItem d context rels binders
    | cut {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        (body : CompiledRegion d
          (.nested origin context rels binders)) :
        CompiledItem d context rels binders
    | bubble {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        (arity : Nat)
        (body : CompiledRegion d
          (.nested origin context (arity :: rels)
            (binders.push origin arity))) :
        CompiledItem d context rels binders

  /-- An origin-owning ordered result at one exact occurrence compiler
  signature. -/
  inductive CompiledItems (d : Diagram) :
      (context : WireContext d) → (rels : RelCtx) →
      BinderContext d rels → Type
    | nil {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} :
        CompiledItems d context rels binders
    | cons {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels}
        (head : CompiledItem d context rels binders)
        (tail : CompiledItems d context rels binders) :
        CompiledItems d context rels binders
end

mutual
  def CompiledRegion.erase : CompiledRegion d call →
      Region call.outerContext.length call.rels
    | .mk items => call.finish items.erase

  def CompiledItem.erase :
      CompiledItem d context rels binders → Item context.length rels
    | .node _ item => item
    | .cut body => .cut body.erase
    | .bubble arity body => .bubble arity body.erase

  def CompiledItems.erase :
      CompiledItems d context rels binders → ItemSeq context.length rels
    | .nil => .nil
    | .cons head tail => .cons head.erase tail.erase
end

namespace CompiledRegion

def localCount (_region : CompiledRegion d call) : Nat :=
  call.localContext.length

def items : (region : CompiledRegion d call) →
    CompiledItems d call.fullContext call.rels call.binders
  | .mk items => items

@[simp] theorem erase_localCount (region : CompiledRegion d call) :
    region.erase.localCount = region.localCount := by
  cases region
  cases call <;> rfl

end CompiledRegion

def CompiledItem.origin
    (item : CompiledItem d context rels binders) :
    LocalOccurrence d.regionCount d.nodeCount := by
  cases item with
  | node node _ => exact .node node
  | @cut _ _ _ origin _ => exact .child origin
  | @bubble _ _ _ origin _ _ => exact .child origin

namespace CompiledItems

/-- The two stable subsequences determined by one origin classifier. -/
structure Partition
    (items : CompiledItems d context rels binders) where
  retained : CompiledItems d context rels binders
  material : CompiledItems d context rels binders

/-- Stably partition annotated items without descending into child bodies. -/
def partition (classifier :
    LocalOccurrence d.regionCount d.nodeCount → Bool) :
    (items : CompiledItems d context rels binders) → Partition items
  | .nil => ⟨.nil, .nil⟩
  | .cons head tail =>
      let divided := tail.partition classifier
      if classifier head.origin then
        ⟨divided.retained, .cons head divided.material⟩
      else
        ⟨.cons head divided.retained, divided.material⟩

def origins : CompiledItems d context rels binders →
    List (LocalOccurrence d.regionCount d.nodeCount)
  | .nil => []
  | .cons head tail => head.origin :: tail.origins

def length (items : CompiledItems d context rels binders) : Nat :=
  items.erase.length

def append : CompiledItems d context rels binders →
    CompiledItems d context rels binders →
      CompiledItems d context rels binders
  | .nil, suffix => suffix
  | .cons head tail, suffix => .cons head (tail.append suffix)

def get : (items : CompiledItems d context rels binders) →
    Fin items.length → CompiledItem d context rels binders
  | .nil, index => Fin.elim0 index
  | .cons head tail, index => Fin.cases head tail.get index

@[simp] theorem erase_nil :
    erase (CompiledItems.nil : CompiledItems d context rels binders) =
      .nil := rfl

@[simp] theorem erase_cons
    (head : CompiledItem d context rels binders)
    (tail : CompiledItems d context rels binders) :
    erase (.cons head tail) = .cons head.erase tail.erase := rfl

@[simp] theorem origins_nil :
    origins (CompiledItems.nil : CompiledItems d context rels binders) =
      [] := rfl

@[simp] theorem origins_cons
    (head : CompiledItem d context rels binders)
    (tail : CompiledItems d context rels binders) :
    origins (.cons head tail) = head.origin :: tail.origins := rfl

@[simp] theorem erase_length
    (items : CompiledItems d context rels binders) :
    items.erase.length = items.length := rfl

@[simp] theorem length_eq_origins_length
    (items : CompiledItems d context rels binders) :
    items.length = items.origins.length :=
  match items with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (length_eq_origins_length tail)

@[simp] theorem erase_append
    (initial suffix : CompiledItems d context rels binders) :
    (initial.append suffix).erase = initial.erase.append suffix.erase :=
  match initial with
  | .nil => rfl
  | .cons _ tail => congrArg (ItemSeq.cons _) (erase_append tail suffix)

@[simp] theorem origins_append
    (initial suffix : CompiledItems d context rels binders) :
    (initial.append suffix).origins = initial.origins ++ suffix.origins :=
  match initial with
  | .nil => rfl
  | .cons _ tail => congrArg (List.cons _) (origins_append tail suffix)

@[simp] theorem erase_get
    (items : CompiledItems d context rels binders)
    (index : Fin items.length) :
    items.erase.get index = (items.get index).erase :=
  match items with
  | .nil => Fin.elim0 index
  | .cons _ tail => Fin.cases rfl (fun tailIndex => erase_get tail tailIndex) index

@[simp] theorem partition_retained_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders) :
    (items.partition classifier).retained.origins =
      items.origins.filter fun origin => !classifier origin :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_retained_origins]

@[simp] theorem partition_material_origins
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders) :
    (items.partition classifier).material.origins =
      items.origins.filter classifier :=
  match items with
  | .nil => rfl
  | .cons head tail => by
      cases hclassifier : classifier head.origin <;>
        simp [partition, hclassifier, partition_material_origins]

theorem partition_retained_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders) :
    List.Sublist (items.partition classifier).retained.origins items.origins := by
  rw [partition_retained_origins]
  exact List.filter_sublist

theorem partition_material_stable
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders) :
    List.Sublist (items.partition classifier).material.origins items.origins := by
  rw [partition_material_origins]
  exact List.filter_sublist

theorem partition_origins_perm
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders) :
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
    {d : Diagram} {context : WireContext d} {rels : RelCtx}
    {source middle target : ItemSeq context.length rels}
    (first : ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels
      source middle)
    (second : ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels
      middle target) :
    ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels source target := by
  have composed := first.trans second
  have wireEquality :
      (FiniteEquiv.refl (Fin context.length)).trans
          (FiniteEquiv.refl (Fin context.length)) =
        FiniteEquiv.refl (Fin context.length) := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [wireEquality] at composed
  exact composed

/-- The canonical intrinsic braid from compiler order to the stable retained
block followed by the stable material block. -/
noncomputable def partitionFactorization
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool) :
    (items : CompiledItems d context rels binders) →
      ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels items.erase
        (((items.partition classifier).retained.append
          (items.partition classifier).material).erase)
  | .nil => ItemSeqIso.refl .nil
  | .cons head tail => by
      let tailFactorization := tail.partitionFactorization classifier
      let headItems : ItemSeq context.length rels := .cons head.erase .nil
      let lifted := (ItemSeqIso.refl headItems).append tailFactorization
      cases hclassifier : classifier head.origin with
      | false =>
          simpa [partition, hclassifier, headItems, erase_append,
            ItemSeq.append_assoc] using lifted
      | true =>
          let retained := (tail.partition classifier).retained.erase
          let material := (tail.partition classifier).material.erase
          let rotated :=
            (ItemSeqIso.appendCommRename headItems retained
              (FiniteEquiv.refl (Fin context.length))).append
                (ItemSeqIso.refl material)
          apply intrinsicTrans lifted
          simpa [partition, hclassifier, headItems, retained, material,
            erase_append, ItemSeq.append_assoc, FiniteEquiv.refl,
            ItemSeq.renameWires_id] using rotated

end CompiledItems

end VisualProof.Concrete.Elaboration
