import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory


namespace Region

/-- Embed the first conjunct's inherited and local wires into the block sum. -/
def conjoinLeftWire (outer firstLocal secondLocal : Nat) :
    Fin (outer + firstLocal) → Fin (outer + (firstLocal + secondLocal)) :=
  Fin.addCases
    (fun wire => Fin.castAdd (firstLocal + secondLocal) wire)
    (fun wire => Fin.natAdd outer (Fin.castAdd secondLocal wire))

/-- Embed the second conjunct's inherited and local wires into the block sum. -/
def conjoinRightWire (outer firstLocal secondLocal : Nat) :
    Fin (outer + secondLocal) → Fin (outer + (firstLocal + secondLocal)) :=
  Fin.addCases
    (fun wire => Fin.castAdd (firstLocal + secondLocal) wire)
    (fun wire => Fin.natAdd outer (Fin.natAdd firstLocal wire))

/-- Intrinsic conjunction with disjoint ownership of each operand's local wires. -/
def conjoin : Region  wires rels → Region  wires rels →
    Region  wires rels
  | .mk firstLocal firstItems, .mk secondLocal secondItems =>
      .mk (firstLocal + secondLocal)
        ((firstItems.renameWires
            (conjoinLeftWire wires firstLocal secondLocal)).append
          (secondItems.renameWires
            (conjoinRightWire wires firstLocal secondLocal)))

def blank : Region  wires rels := .mk 0 .nil

/-- Embed a site's inherited and already-local wires into the combined local
block used when material is adjoined at that exact site. -/
def adjoinHostWire (outer hostLocal addedLocal : Nat) :
    Fin (outer + hostLocal) → Fin (outer + (hostLocal + addedLocal)) :=
  fun wire => Fin.cast (Nat.add_assoc outer hostLocal addedLocal)
    (Fin.castAdd addedLocal wire)

/-- Reassociate every wire visible to the adjoined material into the site's
combined local block. -/
def adjoinMaterialWire (outer hostLocal addedLocal : Nat) :
    Fin ((outer + hostLocal) + addedLocal) →
      Fin (outer + (hostLocal + addedLocal)) :=
  Fin.cast (Nat.add_assoc outer hostLocal addedLocal)

@[simp] theorem adjoinHostWire_inherited
    (inherited : Fin outer) :
    adjoinHostWire outer hostLocal addedLocal
        (Fin.castAdd hostLocal inherited) =
      Fin.castAdd (hostLocal + addedLocal) inherited := by
  apply Fin.ext
  rfl

@[simp] theorem adjoinHostWire_local
    (localWire : Fin hostLocal) :
    adjoinHostWire outer hostLocal addedLocal
        (Fin.natAdd outer localWire) =
      Fin.natAdd outer (Fin.castAdd addedLocal localWire) := by
  apply Fin.ext
  rfl

@[simp] theorem adjoinMaterialWire_prior
    (prior : Fin (outer + hostLocal)) :
    adjoinMaterialWire outer hostLocal addedLocal
        (Fin.castAdd addedLocal prior) =
      adjoinHostWire outer hostLocal addedLocal prior := by
  apply Fin.ext
  rfl

@[simp] theorem adjoinMaterialWire_added
    (added : Fin addedLocal) :
    adjoinMaterialWire outer hostLocal addedLocal
        (Fin.natAdd (outer + hostLocal) added) =
      Fin.natAdd outer (Fin.natAdd hostLocal added) := by
  apply Fin.ext
  change outer + hostLocal + added.val = outer + (hostLocal + added.val)
  omega

/-- Adjoin material inside a region after its existing local binders.  Unlike
`conjoin`, the material can refer to the site's existing local witnesses. -/
def adjoinAt (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) rels)
    (material : Region  (outer + hostLocal) rels) :
    Region  outer rels :=
  match material with
  | .mk addedLocal addedItems =>
      .mk (hostLocal + addedLocal)
        ((hostItems.renameWires
            (adjoinHostWire outer hostLocal addedLocal)).append
          (addedItems.renameWires
            (adjoinMaterialWire outer hostLocal addedLocal)))

/-- The intrinsic capture-avoiding insertion kernel.  Concrete splicing must
elaborate to this operation: pattern wires are mapped into the complete site
wire context, pattern relation variables are mapped into the lexical host
relation context, and the renamed material is adjoined after the host items. -/
def spliceAt (hostLocal : Nat)
    (hostItems : ItemSeq  (outer + hostLocal) hostRels)
    (material : Region  patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels) :
    Region  outer hostRels :=
  adjoinAt hostLocal hostItems
    ((material.renameWires wireMap).renameRelations relationMap)

end Region

structure ItemSeq.Focus (items : ItemSeq  wires rels) where
  before : ItemSeq  wires rels
  item : Item  wires rels
  after : ItemSeq  wires rels
  rebuild : before.append (.cons item after) = items

def Item.castWiresEq (equality : source = target)
    (item : Item  source rels) : Item  target rels :=
  Eq.mp (congrArg (fun wires => Item  wires rels) equality) item

def ItemSeq.castWiresEq (equality : source = target)
    (items : ItemSeq  source rels) : ItemSeq  target rels :=
  Eq.mp (congrArg (fun wires => ItemSeq  wires rels) equality) items

def Region.castWiresEq (equality : source = target)
    (region : Region  source rels) : Region  target rels :=
  Eq.mp (congrArg (fun wires => Region  wires rels) equality) region

@[simp] theorem ItemSeq.castWiresEq_trans
    (first : source = middle) (second : middle = target)
    (items : ItemSeq  source rels) :
    (items.castWiresEq first).castWiresEq second =
      items.castWiresEq (first.trans second) := by
  subst middle
  subst target
  rfl

@[simp] theorem Region.castWiresEq_mk
    (equality : sourceOuter = targetOuter)
    (items : ItemSeq  (sourceOuter + localWires) rels) :
    Region.castWiresEq equality (Region.mk localWires items) =
      Region.mk localWires
        (items.castWiresEq
          (congrArg (fun outer => outer + localWires) equality)) := by
  subst targetOuter
  rfl


theorem Region.castWiresEq_eq_renameWires (equality : source = target)
    (region : Region  source rels) :
    region.castWiresEq equality = region.renameWires (Fin.cast equality) := by
  subst target
  simp [Region.castWiresEq, Region.renameWires_id]

theorem Item.castWiresEq_eq_renameWires (equality : source = target)
    (item : Item  source rels) :
    item.castWiresEq equality = item.renameWires (Fin.cast equality) := by
  subst target
  simp [Item.castWiresEq, Item.renameWires_id]

theorem ItemSeq.castWiresEq_eq_renameWires (equality : source = target)
    (items : ItemSeq  source rels) :
    items.castWiresEq equality = items.renameWires (Fin.cast equality) := by
  subst target
  simp [ItemSeq.castWiresEq, ItemSeq.renameWires_id]

@[simp] theorem Region.adjoinMaterialWire_zero (outer hostLocal : Nat) :
    Region.adjoinMaterialWire outer hostLocal 0 = id := by
  funext wire
  apply Fin.ext
  rfl

@[simp] theorem Region.conjoinLeftWire_zero (wires : Nat) :
    Region.conjoinLeftWire wires 0 0 = id := by
  funext wire
  refine Fin.addCases (fun inherited => ?_)
    (fun localIndex => Fin.elim0 localIndex) wire
  change Region.conjoinLeftWire wires 0 0 (Fin.castAdd 0 inherited) =
    Fin.castAdd 0 inherited
  simp only [Region.conjoinLeftWire, Fin.addCases_left]

@[simp] theorem Region.conjoinRightWire_zero (wires : Nat) :
    Region.conjoinRightWire wires 0 0 = id := by
  funext wire
  refine Fin.addCases (fun inherited => ?_)
    (fun localIndex => Fin.elim0 localIndex) wire
  change Region.conjoinRightWire wires 0 0 (Fin.castAdd 0 inherited) =
    Fin.castAdd 0 inherited
  simp only [Region.conjoinRightWire, Fin.addCases_left]

/-- Changing only a later material block does not affect the host prefix of
an extended wire equivalence. -/
theorem Region.extendWireEquiv_adjoinHostWire
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (material : FiniteEquiv (Fin sourceMaterial) (Fin targetMaterial))
    (localEquiv : FiniteEquiv (Fin (hostLocal + targetMaterial))
      (Fin targetLocal)) :
    (extendWireEquiv outer
        ((extendWireEquiv (FiniteEquiv.refl (Fin hostLocal)) material).trans
          localEquiv)).toFun ∘
        Region.adjoinHostWire sourceOuter hostLocal sourceMaterial =
      (extendWireEquiv outer localEquiv).toFun ∘
        Region.adjoinHostWire sourceOuter hostLocal targetMaterial := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun host => ?_) wire
  · simp only [Function.comp_apply]
    calc
      _ = (extendWireEquiv outer
            ((extendWireEquiv (FiniteEquiv.refl (Fin hostLocal)) material
              ).trans localEquiv))
            (Fin.castAdd (hostLocal + sourceMaterial) inherited) := by
          apply congrArg
          apply Fin.ext
          rfl

      _ = Fin.castAdd targetLocal (outer inherited) :=
          extendWireEquiv_outer _ _ _
      _ = (extendWireEquiv outer localEquiv)
            (Fin.castAdd (hostLocal + targetMaterial) inherited) :=
          (extendWireEquiv_outer _ _ _).symm
      _ = _ := by
          apply congrArg
          apply Fin.ext
          rfl

  · simp only [Function.comp_apply]
    calc
      _ = (extendWireEquiv outer
            ((extendWireEquiv (FiniteEquiv.refl (Fin hostLocal)) material
              ).trans localEquiv))
            (Fin.natAdd sourceOuter
              (Fin.castAdd sourceMaterial host)) := by
          apply congrArg
          apply Fin.ext
          rfl
      _ = Fin.natAdd targetOuter
            (localEquiv (Fin.castAdd targetMaterial host)) := by
          rw [extendWireEquiv_local, FiniteEquiv.trans_apply,
            extendWireEquiv_outer]
          rfl
      _ = (extendWireEquiv outer localEquiv)
            (Fin.natAdd sourceOuter
              (Fin.castAdd targetMaterial host)) :=
          (extendWireEquiv_local _ _ _).symm
      _ = _ := by
          apply congrArg
          apply Fin.ext
          rfl

/-- Extending an ambient equivalence across a host and a retained trailing
block commutes with embedding that host ahead of the trailing block. -/
theorem Region.extendWireEquiv_adjoinHostWire_commutes
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (hostLocal extra : Nat) :
    (extendWireEquiv outer
        (FiniteEquiv.refl (Fin (hostLocal + extra)))).toFun ∘
        Region.adjoinHostWire sourceOuter hostLocal extra =
      Region.adjoinHostWire targetOuter hostLocal extra ∘
        (extendWireEquiv outer
          (FiniteEquiv.refl (Fin hostLocal))).toFun := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun host => ?_) wire
  · simp only [Function.comp_apply]
    calc
      _ = (extendWireEquiv outer
            (FiniteEquiv.refl (Fin (hostLocal + extra))))
            (Fin.castAdd (hostLocal + extra) inherited) := by
          apply congrArg
          apply Fin.ext
          rfl
      _ = Fin.castAdd (hostLocal + extra) (outer inherited) :=
          extendWireEquiv_outer _ _ _
      _ = Region.adjoinHostWire targetOuter hostLocal extra
            (Fin.castAdd hostLocal (outer inherited)) := by
          apply Fin.ext
          rfl
      _ = _ := by
          apply congrArg
          exact (extendWireEquiv_outer outer
            (FiniteEquiv.refl (Fin hostLocal)) inherited).symm
  · simp only [Function.comp_apply]
    calc
      _ = (extendWireEquiv outer
            (FiniteEquiv.refl (Fin (hostLocal + extra))))
            (Fin.natAdd sourceOuter (Fin.castAdd extra host)) := by
          apply congrArg
          apply Fin.ext
          rfl
      _ = Fin.natAdd targetOuter (Fin.castAdd extra host) :=
          extendWireEquiv_local _ _ _
      _ = Region.adjoinHostWire targetOuter hostLocal extra
            (Fin.natAdd targetOuter host) := by
          apply Fin.ext
          rfl
      _ = _ := by
          apply congrArg
          exact (extendWireEquiv_local outer
            (FiniteEquiv.refl (Fin hostLocal)) host).symm

@[simp] theorem Region.renameWires_localCount
    (region : Region sourceWires rels)
    (wire : Fin sourceWires → Fin targetWires) :
    (region.renameWires wire).localCount = region.localCount := by
  cases region
  rfl

@[simp] theorem Region.renameRelations_localCount
    (region : Region wires sourceRels)
    (relation : RelationRenaming sourceRels targetRels) :
    (region.renameRelations relation).localCount = region.localCount := by
  cases region
  rfl

@[simp] theorem Region.conjoin_localCount
    (first second : Region wires rels) :
    (first.conjoin second).localCount =
      first.localCount + second.localCount := by
  cases first
  cases second
  rfl

@[simp] theorem Region.adjoinAt_localCount
    (hostLocal : Nat) (hostItems : ItemSeq (wires + hostLocal) rels)
    (material : Region (wires + hostLocal) rels) :
    (Region.adjoinAt hostLocal hostItems material).localCount =
      hostLocal + material.localCount := by
  cases material
  rfl

@[simp] theorem Region.castWiresEq_localCount
    (region : Region sourceWires rels)
    (equality : sourceWires = targetWires) :
    (region.castWiresEq equality).localCount = region.localCount := by
  subst targetWires
  cases region
  rfl

theorem Region.mk_itemsCast (region : Region wires rels)
    (localEq : region.localCount = localWires) :
    Region.mk localWires (region.itemsCast localEq) = region := by
  cases region with
  | mk actualLocal items =>
    dsimp only [Region.localCount] at localEq
    subst localWires
    rfl

theorem Region.itemsCast_eq_renameWires
    (region : Region wires rels)
    (localEq : region.localCount = localWires) :
    region.itemsCast localEq =
      region.items.renameWires
        (Fin.cast (congrArg (fun count => wires + count) localEq)) := by
  exact ItemSeq.castWiresEq_eq_renameWires _ _

private theorem Region.conjoinLeftWire_zero_val
    (wire : Fin (outer + 0)) :
    (Region.conjoinLeftWire outer 0 added wire).val = wire.val := by
  refine Fin.addCases (fun inherited => ?_)
    (fun impossible => Fin.elim0 impossible) wire
  change (Fin.addCases (motive := fun _ => Fin (outer + (0 + added)))
      (fun wire : Fin outer => Fin.castAdd (0 + added) wire)
      (fun wire : Fin 0 => Fin.natAdd outer (Fin.castAdd added wire))
      (Fin.castAdd 0 inherited)).val = (Fin.castAdd 0 inherited).val
  rw [Fin.addCases_left]
  rfl

private theorem Region.conjoinRightWire_zero_val
    (wire : Fin (outer + added)) :
    (Region.conjoinRightWire outer 0 added wire).val = wire.val := by
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · change (Fin.addCases (motive := fun _ => Fin (outer + (0 + added)))
        (fun wire : Fin outer => Fin.castAdd (0 + added) wire)
        (fun wire : Fin added => Fin.natAdd outer (Fin.natAdd 0 wire))
        (Fin.castAdd added inherited)).val =
      (Fin.castAdd added inherited).val
    rw [Fin.addCases_left]
    rfl
  · change (Fin.addCases (motive := fun _ => Fin (outer + (0 + added)))
        (fun wire : Fin outer => Fin.castAdd (0 + added) wire)
        (fun wire : Fin added => Fin.natAdd outer (Fin.natAdd 0 wire))
        (Fin.natAdd outer localWire)).val =
      (Fin.natAdd outer localWire).val
    rw [Fin.addCases_right]
    change outer + (0 + localWire.val) = outer + localWire.val
    omega

@[simp] theorem ItemSeq.castWiresEq_append
    (equality : source = target)
    (first second : ItemSeq  source rels) :
    (first.append second).castWiresEq equality =
      (first.castWiresEq equality).append
        (second.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem ItemSeq.castWiresEq_cons
    (equality : source = target)
    (item : Item  source rels)
    (tail : ItemSeq  source rels) :
    (ItemSeq.cons item tail).castWiresEq equality =
      ItemSeq.cons (item.castWiresEq equality)
        (tail.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem Region.castWiresEq_adjoinAt_nil
    (equality : source = target)
    (hostLocal : Nat)
    (material : Region  (source + hostLocal) rels) :
    (Region.adjoinAt hostLocal .nil material).castWiresEq equality =
      Region.adjoinAt hostLocal .nil
        (material.castWiresEq
          (congrArg (fun outer => outer + hostLocal) equality)) := by
  subst target
  rfl

@[simp] theorem Region.castWiresEq_trans
    (first : source = middle) (second : middle = target)
    (region : Region  source rels) :
    (region.castWiresEq first).castWiresEq second =
      region.castWiresEq (first.trans second) := by
  subst middle
  subst target
  rfl

theorem Region.castWiresEq_proof_irrel
    (first second : source = target)
    (region : Region  source rels) :
    region.castWiresEq first = region.castWiresEq second := by
  rw [show first = second from Subsingleton.elim _ _]

theorem Region.castWiresEq_castRels
    (wireEquality : sourceWires = targetWires)
    (relsEquality : sourceRels = targetRels)
    (region : Region  sourceWires sourceRels) :
    (relsEquality ▸ region).castWiresEq wireEquality =
      relsEquality ▸ (region.castWiresEq wireEquality) := by
  subst targetWires
  subst targetRels
  rfl

@[simp] theorem Item.castWiresEq_cut
    (equality : source = target) (body : Region  source rels) :
    (Item.cut body).castWiresEq equality =
      Item.cut (body.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem Item.castWiresEq_bubble
    (equality : source = target) (arity : Nat)
    (body : Region  source (arity :: rels)) :
    (Item.bubble arity body).castWiresEq equality =
      Item.bubble arity (body.castWiresEq equality) := by
  subst target
  rfl

def ItemSeq.focusAt? :
    (items : ItemSeq  wires rels) → Nat → Option (ItemSeq.Focus items)
  | .nil, _ => none
  | .cons item tail, 0 => some {
      before := .nil
      item := item
      after := tail
      rebuild := rfl
    }
  | .cons item tail, index + 1 => do
      let focus ← tail.focusAt? index
      pure {
        before := .cons item focus.before
        item := focus.item
        after := focus.after
        rebuild := by
          simp only [ItemSeq.append]
          exact congrArg (ItemSeq.cons item) focus.rebuild
      }

/-- The canonical proof-relevant result of focusing a valid finite item
position.  It is computed directly from the sequence and retains both the
lookup equation and the indexed item equation. -/
structure ItemSeq.IndexedFocus
    (items : ItemSeq wires rels) (index : Fin items.length) where
  focus : ItemSeq.Focus items
  atIndex : items.focusAt? index.val = some focus
  item_eq : focus.item = items.get index

def ItemSeq.focusAt :
    (items : ItemSeq wires rels) →
    (index : Fin items.length) → ItemSeq.IndexedFocus items index
  | .nil, index => Fin.elim0 index
  | .cons item tail, index =>
      Fin.cases {
        focus := {
          before := .nil
          item := item
          after := tail
          rebuild := rfl
        }
        atIndex := rfl
        item_eq := rfl
      } (fun tailIndex =>
        let nested := ItemSeq.focusAt tail tailIndex
        {
          focus := {
            before := .cons item nested.focus.before
            item := nested.focus.item
            after := nested.focus.after
            rebuild := by
              simp only [ItemSeq.append]
              exact congrArg (ItemSeq.cons item) nested.focus.rebuild
          }
          atIndex := by
            simp [ItemSeq.focusAt?, nested.atIndex]
          item_eq := by
            simpa only [ItemSeq.get] using nested.item_eq
        }) index

theorem ItemSeq.focusAt?_complete
    (items : ItemSeq  wires rels) (index : Fin items.length) :
    ∃ focus, items.focusAt? index.val = some focus ∧
      focus.item = items.get index := by
  let result := items.focusAt index
  exact ⟨result.focus, result.atIndex, result.item_eq⟩

/-- A successful natural-number focus lookup determines a valid finite
position.  This is the converse bound needed to transport a context path
through an item permutation. -/
theorem ItemSeq.focusAt?_index_lt
    (items : ItemSeq  wires rels) (index : Nat)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index = some focus) :
    index < items.length := by
  cases items with
  | nil => simp [ItemSeq.focusAt?] at hfocus
  | cons head tail =>
      cases index with
      | zero => simp [ItemSeq.length]
      | succ index =>
          cases htail : tail.focusAt? index with
          | none => simp [ItemSeq.focusAt?, htail] at hfocus
          | some tailFocus =>
              simpa [ItemSeq.length] using
                ItemSeq.focusAt?_index_lt tail index tailFocus htail
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

def ItemSeq.Focus.castWiresEq (equality : source = target)
    (focus : ItemSeq.Focus items) :
    ItemSeq.Focus (items.castWiresEq equality) := by
  subst target
  exact focus

@[simp] theorem ItemSeq.Focus.castWiresEq_item
    (equality : source = target) (focus : ItemSeq.Focus items) :
    (focus.castWiresEq equality).item =
      focus.item.castWiresEq equality := by
  subst target
  rfl

@[simp] theorem ItemSeq.Focus.castWiresEq_before
    (equality : source = target) (focus : ItemSeq.Focus items) :
    (focus.castWiresEq equality).before =
      focus.before.castWiresEq equality := by
  subst target
  rfl

@[simp] theorem ItemSeq.Focus.castWiresEq_after
    (equality : source = target) (focus : ItemSeq.Focus items) :
    (focus.castWiresEq equality).after =
      focus.after.castWiresEq equality := by
  subst target
  rfl

theorem ItemSeq.focusAt?_castWiresEq
    (equality : source = target)
    (items : ItemSeq  source rels) (index : Nat)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index = some focus) :
    (items.castWiresEq equality).focusAt? index =
      some (focus.castWiresEq equality) := by
  subst target
  exact hfocus

/-- The structural focus decomposition is the corresponding single-item
replacement. -/
theorem ItemSeq.replaceAt_eq_focus
    (items : ItemSeq  wires rels) (index : Fin items.length)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index.val = some focus)
    (replacement : Item  wires rels) :
    items.replaceAt index replacement =
      focus.before.append (.cons replacement focus.after) := by
  cases items with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      induction index using Fin.cases with
      | zero =>
          simp [ItemSeq.focusAt?] at hfocus
          subst focus
          rfl
      | succ rest =>
          cases htail : tail.focusAt? rest.val with
          | none => simp [ItemSeq.focusAt?, htail] at hfocus
          | some tailFocus =>
              simp [ItemSeq.focusAt?, htail] at hfocus
              subst focus
              simp only [ItemSeq.replaceAt, ItemSeq.append]
              exact congrArg (ItemSeq.cons head)
                (ItemSeq.replaceAt_eq_focus tail rest tailFocus htail replacement)
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

structure Region.ContextFocus
    (region : Region  wires rels) where
  holeWires : Nat
  holeRels : RelCtx
  context : DiagramContext  wires holeWires rels holeRels
  body : Region  holeWires holeRels
  rebuild : context.fill body = region

/-- Intrinsic evidence that a list of item positions selects a nested region.
Unlike the executable lookup below, this type exposes the constructor evidence
needed by semantic proofs without comparing dependent proof fields. -/
inductive Region.ContextPath :
    (region : Region  wires rels) → List Nat → Type
  | here (region : Region  wires rels) : ContextPath region []
  | cut {localWires : Nat}
      {items : ItemSeq  (wires + localWires) rels}
      {index : Nat} {rest : List Nat}
      (focus : ItemSeq.Focus items)
      (atIndex : items.focusAt? index = some focus)
      {child : Region  (wires + localWires) rels}
      (isCut : focus.item = .cut child)
      (nested : ContextPath child rest) :
      ContextPath (.mk localWires items) (index :: rest)
  | bubble {localWires arity : Nat}
      {items : ItemSeq  (wires + localWires) rels}
      {index : Nat} {rest : List Nat}
      (focus : ItemSeq.Focus items)
      (atIndex : items.focusAt? index = some focus)
      {child : Region  (wires + localWires) (arity :: rels)}
      (isBubble : focus.item = .bubble arity child)
      (nested : ContextPath child rest) :
      ContextPath (.mk localWires items) (index :: rest)

/-- An intrinsic path is proof-unique once its region and position list are
fixed.  All constructor evidence is recovered from the deterministic item
focus at each path position. -/
theorem Region.ContextPath.unique
    (left right : Region.ContextPath region path) : left = right := by
  induction left with
  | here region =>
      cases right
      rfl
  | cut focus atIndex isCut nested ih =>
      cases right with
      | cut otherFocus otherAt otherIsCut otherNested =>
          have hfocus : otherFocus = focus :=
            Option.some.inj (otherAt.symm.trans atIndex)
          subst otherFocus
          have hitem := otherIsCut.symm.trans isCut
          have hchild := Item.cut.inj hitem
          cases hchild
          have hnested := ih otherNested
          subst otherNested
          rfl
      | bubble otherFocus otherAt otherIsBubble otherNested =>
          have hfocus : otherFocus = focus :=
            Option.some.inj (otherAt.symm.trans atIndex)
          subst otherFocus
          have impossible := otherIsBubble.symm.trans isCut
          contradiction
  | bubble focus atIndex isBubble nested ih =>
      cases right with
      | cut otherFocus otherAt otherIsCut otherNested =>
          have hfocus : otherFocus = focus :=
            Option.some.inj (otherAt.symm.trans atIndex)
          subst otherFocus
          have impossible := otherIsCut.symm.trans isBubble
          contradiction
      | bubble otherFocus otherAt otherIsBubble otherNested =>
          have hfocus : otherFocus = focus :=
            Option.some.inj (otherAt.symm.trans atIndex)
          subst otherFocus
          have hitem := otherIsBubble.symm.trans isBubble
          have harity := (Item.bubble.inj hitem).1
          cases harity
          have hchild := (Item.bubble.inj hitem).2
          cases hchild
          have hnested := ih otherNested
          subst otherNested
          rfl

def Region.ContextPath.toFocus :
    {region : Region  wires rels} → {path : List Nat} →
      Region.ContextPath region path → Region.ContextFocus region
  | region, [], .here _ => {
      holeWires := wires
      holeRels := rels
      context := .hole
      body := region
      rebuild := rfl
    }
  | _, _ :: _, .cut focus _ isCut nested =>
      let nestedFocus := nested.toFocus
      {
        holeWires := nestedFocus.holeWires
        holeRels := nestedFocus.holeRels
        context := .cut _ focus.before focus.after nestedFocus.context
        body := nestedFocus.body
        rebuild := by
          simp only [DiagramContext.fill]
          rw [nestedFocus.rebuild, ← isCut, focus.rebuild]
      }
  | _, _ :: _, .bubble focus _ isBubble nested =>
      let nestedFocus := nested.toFocus
      {
        holeWires := nestedFocus.holeWires
        holeRels := nestedFocus.holeRels
        context := .bubble _ focus.before focus.after _ nestedFocus.context
        body := nestedFocus.body
        rebuild := by
          simp only [DiagramContext.fill]
          rw [nestedFocus.rebuild, ← isBubble, focus.rebuild]
      }

/-- Compose an outer intrinsic path with a path beginning at its focused
body.  List concatenation is therefore the authoritative composition law for
intrinsic region paths. -/
noncomputable def Region.ContextPath.nest
    {root : Region  wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    Region.ContextPath root (outerPath ++ innerPath) := by
  induction outer with
  | here region =>
      simpa using inner
  | cut focus atIndex isCut nested induction =>
      exact .cut focus atIndex isCut (induction inner)
  | bubble focus atIndex isBubble nested induction =>
      exact .bubble focus atIndex isBubble (induction inner)

@[simp] theorem Region.ContextPath.nest_toFocus_holeWires
    {root : Region  wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    (outer.nest inner).toFocus.holeWires = inner.toFocus.holeWires := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction => exact induction inner
  | bubble focus atIndex isBubble nested induction => exact induction inner

@[simp] theorem Region.ContextPath.nest_toFocus_holeRels
    {root : Region  wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    (outer.nest inner).toFocus.holeRels = inner.toFocus.holeRels := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction => exact induction inner
  | bubble focus atIndex isBubble nested induction => exact induction inner

theorem Region.ContextPath.nest_toFocus_body_heq
    {root : Region  wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    HEq (outer.nest inner).toFocus.body inner.toFocus.body := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction => exact induction inner
  | bubble focus atIndex isBubble nested induction => exact induction inner

def Region.ContextPath.castWiresEq (equality : source = target)
    (witness : Region.ContextPath region path) :
    Region.ContextPath (region.castWiresEq equality) path := by
  subst target
  exact witness

def Region.ContextPath.castRelsEq
    {source target : RelCtx} {region : Region  wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    Region.ContextPath (equality ▸ region) path := by
  subst target
  exact witness

@[simp] theorem Region.ContextPath.castRelsEq_toFocus_holeWires
    {source target : RelCtx} {region : Region  wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castRelsEq equality).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst target
  rfl

@[simp] theorem Region.ContextPath.castRelsEq_toFocus_holeRels
    {source target : RelCtx} {region : Region  wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castRelsEq equality).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst target
  rfl

theorem Region.ContextPath.castRelsEq_fill
    {source target : RelCtx} {region : Region  wires source}
    {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath region path)
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness := witness.castRelsEq equality
    let holeWiresEq : targetWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      witness.castRelsEq_toFocus_holeWires equality
    let holeRelsEq : targetWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      witness.castRelsEq_toFocus_holeRels equality
    let targetReplacement : Region
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    targetWitness.toFocus.context.fill targetReplacement =
      equality ▸ witness.toFocus.context.fill replacement := by
  subst target
  rfl

/-- Reclassify a region's complete wire block between inherited and locally
bound ownership without changing the distinguished child path.  The item
sequence sees only the complete block, so every nested child is transported
by the same finite-carrier equality. -/
def Region.ContextPath.relocal
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {items : ItemSeq  (sourceOuter + sourceLocal) rels}
    {path : List Nat}
    (equality : sourceOuter + sourceLocal = targetOuter + targetLocal)
    (witness : Region.ContextPath (Region.mk sourceLocal items) path) :
    Region.ContextPath
      (Region.mk targetLocal (items.castWiresEq equality)) path := by
  cases witness with
  | here region => exact .here _
  | @cut _ _ _ _ index rest focus atIndex child isCut nested =>
      let targetFocus := focus.castWiresEq equality
      have targetAt := ItemSeq.focusAt?_castWiresEq equality items index focus
        atIndex
      have targetIsCut : targetFocus.item =
          .cut (child.castWiresEq equality) := by
        rw [ItemSeq.Focus.castWiresEq_item, isCut,
          Item.castWiresEq_cut]
      exact .cut targetFocus targetAt targetIsCut
        (nested.castWiresEq equality)
  | @bubble _ _ _ arity _ index rest focus atIndex child isBubble nested =>
      let targetFocus := focus.castWiresEq equality
      have targetAt := ItemSeq.focusAt?_castWiresEq equality items index focus
        atIndex
      have targetIsBubble : targetFocus.item =
          .bubble arity (child.castWiresEq equality) := by
        rw [ItemSeq.Focus.castWiresEq_item, isBubble,
          Item.castWiresEq_bubble]
      exact .bubble targetFocus targetAt targetIsBubble
        (nested.castWiresEq equality)

@[simp] theorem Region.ContextPath.castWiresEq_toFocus_cutDepth
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castWiresEq equality).toFocus.context.cutDepth =
      witness.toFocus.context.cutDepth := by
  subst target
  rfl

@[simp] theorem Region.ContextPath.castWiresEq_toFocus_holeWires
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castWiresEq equality).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst target
  rfl

@[simp] theorem Region.ContextPath.castWiresEq_toFocus_holeRels
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castWiresEq equality).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst target
  rfl

theorem Region.ContextPath.castWiresEq_toFocus_body_heq
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    HEq (witness.castWiresEq equality).toFocus.body
      witness.toFocus.body := by
  subst target
  rfl

/-- Rebuilding after an outer-wire cast is the cast of the rebuilt region;
the focused replacement is transported by the induced hole equalities. -/
theorem Region.ContextPath.castWiresEq_fill
    {source target : Nat} {region : Region  source rels}
    {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath region path)
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness := witness.castWiresEq equality
    let holeWiresEq : targetWitness.toFocus.holeWires =
      witness.toFocus.holeWires :=
        witness.castWiresEq_toFocus_holeWires equality
    let holeRelsEq : targetWitness.toFocus.holeRels =
      witness.toFocus.holeRels :=
        witness.castWiresEq_toFocus_holeRels equality
    let targetReplacement : Region
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    DiagramContext.fill
        targetWitness.toFocus.context targetReplacement =
      (DiagramContext.fill
        witness.toFocus.context replacement).castWiresEq equality := by
  subst target
  rfl

theorem Region.ContextPath.relocal_toFocus_holeWires_of_nonempty
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {items : ItemSeq  (sourceOuter + sourceLocal) rels}
    {path : List Nat}
    (equality : sourceOuter + sourceLocal = targetOuter + targetLocal)
    (witness : Region.ContextPath (Region.mk sourceLocal items) path)
    (nonempty : path ≠ []) :
    (witness.relocal equality).toFocus.holeWires =
      witness.toFocus.holeWires := by
  cases witness with
  | here region => exact False.elim (nonempty rfl)
  | cut focus atIndex isCut nested =>
      exact nested.castWiresEq_toFocus_holeWires equality
  | bubble focus atIndex isBubble nested =>
      exact nested.castWiresEq_toFocus_holeWires equality

@[simp] theorem Region.ContextPath.relocal_toFocus_holeRels
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {items : ItemSeq  (sourceOuter + sourceLocal) rels}
    {path : List Nat}
    (equality : sourceOuter + sourceLocal = targetOuter + targetLocal)
    (witness : Region.ContextPath (Region.mk sourceLocal items) path) :
    (witness.relocal equality).toFocus.holeRels =
      witness.toFocus.holeRels := by
  cases witness with
  | here region => rfl
  | cut focus atIndex isCut nested =>
      exact nested.castWiresEq_toFocus_holeRels equality
  | bubble focus atIndex isBubble nested =>
      exact nested.castWiresEq_toFocus_holeRels equality

/-- For a flattened zero-local presentation, reclassification commutes with
replacing the distinguished descendant.  The right side states the same
operation as existentially closing the newly local root wires around the
cast flattened replacement. -/
theorem Region.ContextPath.relocal_zero_fill
    {sourceOuter targetOuter targetLocal : Nat}
    {items : ItemSeq  sourceOuter rels}
    {path : List Nat}
    (equality : sourceOuter = targetOuter + targetLocal)
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (nonempty : path ≠ [])
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let totalEquality : sourceOuter + 0 = targetOuter + targetLocal := by
      simpa using equality
    let targetWitness := witness.relocal totalEquality
    let holeWiresEq : targetWitness.toFocus.holeWires =
      witness.toFocus.holeWires :=
        witness.relocal_toFocus_holeWires_of_nonempty totalEquality nonempty
    let holeRelsEq : targetWitness.toFocus.holeRels =
      witness.toFocus.holeRels :=
        witness.relocal_toFocus_holeRels totalEquality
    let targetReplacement : Region
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    DiagramContext.fill
        targetWitness.toFocus.context targetReplacement =
      Region.adjoinAt targetLocal .nil
        ((DiagramContext.fill
          witness.toFocus.context replacement).castWiresEq equality) := by
  subst sourceOuter
  cases witness with
  | here region => exact False.elim (nonempty rfl)
  | cut focus atIndex isCut nested =>
      have hmaterial :
          Region.adjoinMaterialWire targetOuter targetLocal 0 = id := by
        funext wire
        apply Fin.ext
        rfl
      simp [Region.ContextPath.relocal, Region.ContextPath.toFocus,
        DiagramContext.fill, Region.adjoinAt, hmaterial,
        ItemSeq.renameWires, ItemSeq.renameWires_id]
      congr 3
  | bubble focus atIndex isBubble nested =>
      have hmaterial :
          Region.adjoinMaterialWire targetOuter targetLocal 0 = id := by
        funext wire
        apply Fin.ext
        rfl
      simp [Region.ContextPath.relocal, Region.ContextPath.toFocus,
        DiagramContext.fill, Region.adjoinAt, hmaterial,
        ItemSeq.renameWires, ItemSeq.renameWires_id]
      congr 3

/-- Follow an intrinsic child-item path and return the unique typed context and
focused region together with a reconstruction equation.  A path step must name
a cut or bubble item; atoms and  relations cannot contain a region. -/
def Region.contextAtPath? :
    (region : Region  wires rels) →
      List Nat → Option (Region.ContextFocus region)
  | region, [] => some {
      holeWires := wires
      holeRels := rels
      context := .hole
      body := region
      rebuild := rfl
    }
  | .mk localWires items, index :: rest => do
      let focus ← items.focusAt? index
      match hitem : focus.item with
      | .cut child =>
          let nested ← child.contextAtPath? rest
          pure {
            holeWires := nested.holeWires
            holeRels := nested.holeRels
            context := .cut localWires focus.before focus.after nested.context
            body := nested.body
            rebuild := by
              simp only [DiagramContext.fill]
              rw [nested.rebuild, ← hitem, focus.rebuild]
          }
      | .bubble arity child =>
          let nested ← child.contextAtPath? rest
          pure {
            holeWires := nested.holeWires
            holeRels := nested.holeRels
            context := .bubble localWires focus.before focus.after arity
              nested.context
            body := nested.body
            rebuild := by
              simp only [DiagramContext.fill]
              rw [nested.rebuild, ← hitem, focus.rebuild]
          }
      | .atom .. | .identity .. => none

theorem Region.contextAtPath?_castWiresEq
    (equality : source = target)
    (region : Region  source rels) (path : List Nat)
    (focus : Region.ContextFocus region)
    (hfocus : region.contextAtPath? path = some focus) :
    ∃ transported,
      (region.castWiresEq equality).contextAtPath? path = some transported := by
  subst target
  exact ⟨focus, hfocus⟩

@[simp] theorem Region.conjoin_localWires
    (firstItems : ItemSeq  (wires + firstLocal) rels)
    (secondItems : ItemSeq  (wires + secondLocal) rels) :
    Region.conjoin (.mk firstLocal firstItems) (.mk secondLocal secondItems) =
      .mk (firstLocal + secondLocal)
        ((firstItems.renameWires
            (Region.conjoinLeftWire wires firstLocal secondLocal)).append
          (secondItems.renameWires
            (Region.conjoinRightWire wires firstLocal secondLocal))) := rfl

theorem ItemSeq.renameWires_append
    : (first second : ItemSeq  source rels) →
    (rho : Fin source → Fin target) →
    (first.append second).renameWires rho =
      (first.renameWires rho).append (second.renameWires rho)
  | .nil, _, _ => rfl
  | .cons item tail, second, rho =>
      congrArg (ItemSeq.cons (item.renameWires rho))
        (ItemSeq.renameWires_append tail second rho)

/-- Project the exact item sequence of a zero-local first conjunct after
adjoining it with a second region. -/
theorem Region.itemsCast_adjoinAt_nil_conjoin_zero
    (first second : Region (outer + hostLocal) rels)
    (firstZero : first.localCount = 0)
    (secondLocalEq : second.localCount = addedLocal)
    (combinedLocalEq :
      (Region.adjoinAt hostLocal .nil (first.conjoin second)).localCount =
        hostLocal + addedLocal) :
    let firstAdjoinEq :
        (Region.adjoinAt hostLocal .nil first).localCount = hostLocal := by
      rw [Region.adjoinAt_localCount, firstZero]
      omega
    (Region.adjoinAt hostLocal .nil (first.conjoin second)).itemsCast
        combinedLocalEq =
      (((Region.adjoinAt hostLocal .nil first).itemsCast firstAdjoinEq
          ).renameWires
        (Region.adjoinHostWire outer hostLocal addedLocal)).append
      ((second.itemsCast secondLocalEq).renameWires
        (Region.adjoinMaterialWire outer hostLocal addedLocal)) := by
  cases first with
  | mk firstLocal firstItems =>
    cases second with
    | mk secondLocal secondItems =>
      dsimp only [Region.localCount] at firstZero secondLocalEq
      subst firstLocal
      subst secondLocal
      have combinedDef :
          (Region.adjoinAt hostLocal .nil
            ((Region.mk 0 firstItems).conjoin
              (Region.mk addedLocal secondItems))).localCount =
            hostLocal + addedLocal := by
        change hostLocal + (0 + addedLocal) = hostLocal + addedLocal
        omega
      rw [show combinedLocalEq = combinedDef from Subsingleton.elim _ _]
      simp only [Region.itemsCast_eq_renameWires]
      simp only [Region.adjoinAt, Region.conjoin,
        Region.items, Region.localCount,
        ItemSeq.renameWires_append, ItemSeq.renameWires_comp]
      simp only [ItemSeq.renameWires, ItemSeq.nil_append]
      congr 1
      · apply congrArg (fun wireMap =>
          ItemSeq.renameWires wireMap firstItems)
        funext index
        refine Fin.addCases (fun prior => ?_)
          (fun impossible => Fin.elim0 impossible) index
        apply Fin.ext
        simp [Function.comp_apply, Region.adjoinMaterialWire,
          Region.adjoinHostWire,
          Region.conjoinLeftWire_zero_val]
      · apply congrArg (fun wireMap =>
          ItemSeq.renameWires wireMap secondItems)
        funext index
        refine Fin.addCases (fun prior => ?_) (fun added => ?_) index
        · apply Fin.ext
          simp [Function.comp_apply, Region.adjoinMaterialWire,
            Region.conjoinRightWire_zero_val]
        · apply Fin.ext
          simp [Function.comp_apply, Region.adjoinMaterialWire,
            Region.conjoinRightWire_zero_val]

theorem ItemSeq.renameRelations_append
    : (first second : ItemSeq  wires source) →
    (rho : RelationRenaming source target) →
    (first.append second).renameRelations rho =
      (first.renameRelations rho).append (second.renameRelations rho)
  | .nil, _, _ => rfl
  | .cons item tail, second, rho =>
      congrArg (ItemSeq.cons (item.renameRelations rho))
        (ItemSeq.renameRelations_append tail second rho)

@[simp] theorem ItemSeq.renameRelations_length :
    (items : ItemSeq  wires source) →
    (rho : RelationRenaming source target) →
    (items.renameRelations rho).length = items.length
  | .nil, _ => rfl
  | .cons _ tail, rho =>
      congrArg Nat.succ (ItemSeq.renameRelations_length tail rho)

theorem ItemSeq.get_renameRelations
    : (items : ItemSeq  wires source) →
      (rho : RelationRenaming source target) →
      (index : Fin items.length) →
      (items.renameRelations rho).get
          (Fin.cast (ItemSeq.renameRelations_length items rho).symm index) =
        (items.get index).renameRelations rho
  | .nil, _, index => Fin.elim0 index
  | .cons item tail, rho, index => by
      refine Fin.cases ?_ (fun rest => ?_) index
      · rfl
      · simpa [ItemSeq.get] using
          ItemSeq.get_renameRelations tail rho rest

@[simp] theorem ItemSeq.castWiresEq_length (equality : source = target)
    (items : ItemSeq  source rels) :
    (items.castWiresEq equality).length = items.length := by
  subst target
  rfl

theorem ItemSeq.get_castWiresEq (equality : source = target)
    (items : ItemSeq  source rels) (index : Fin items.length) :
    (items.castWiresEq equality).get
        (Fin.cast (ItemSeq.castWiresEq_length equality items).symm index) =
      (items.get index).castWiresEq equality := by
  subst target
  rfl

@[simp] theorem ItemSeq.renameWires_length :
    (items : ItemSeq  source rels) →
    (rho : Fin source → Fin target) →
    (items.renameWires rho).length = items.length
  | .nil, _ => rfl
  | .cons _ tail, rho =>
      congrArg Nat.succ (ItemSeq.renameWires_length tail rho)

/-- Renaming wires preserves the finite carrier of item positions. -/
def ItemSeq.renameWiresPositionEquiv
    (items : ItemSeq  source rels)
    (rho : Fin source → Fin target) :
    FiniteEquiv (Fin items.length) (Fin (items.renameWires rho).length) where
  toFun := Fin.cast (ItemSeq.renameWires_length items rho).symm
  invFun := Fin.cast (ItemSeq.renameWires_length items rho)
  left_inv := by
    intro index
    apply Fin.ext
    rfl
  right_inv := by
    intro index
    apply Fin.ext
    rfl

/-- Transport a finite carrier across an equality of its cardinalities. -/
def FiniteEquiv.finCast (equality : source = target) :
    FiniteEquiv (Fin source) (Fin target) where
  toFun := Fin.cast equality
  invFun := Fin.cast equality.symm
  left_inv := by
    intro index
    apply Fin.ext
    rfl
  right_inv := by
    intro index
    apply Fin.ext
    rfl

/-- Swap two adjacent finite blocks while preserving order within each block. -/
def FiniteEquiv.finAddComm (left right : Nat) :
    FiniteEquiv (Fin (left + right)) (Fin (right + left)) where
  toFun := Fin.addCases (Fin.natAdd right) (Fin.castAdd left)
  invFun := Fin.addCases (Fin.natAdd left) (Fin.castAdd right)
  left_inv := by
    intro index
    refine Fin.addCases (fun leftIndex => ?_) (fun rightIndex => ?_) index <;>
      simp
  right_inv := by
    intro index
    refine Fin.addCases (fun rightIndex => ?_) (fun leftIndex => ?_) index <;>
      simp

@[simp] theorem ItemSeq.length_append :
    (first second : ItemSeq  wires rels) →
    (first.append second).length = first.length + second.length
  | .nil, second => (Nat.zero_add second.length).symm
  | .cons _ tail, second => by
      simpa [ItemSeq.append, ItemSeq.length, Nat.succ_add] using
        congrArg Nat.succ (ItemSeq.length_append tail second)

def ItemSeq.appendRenamePositionSwap
    (first second : ItemSeq  source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    FiniteEquiv (Fin (first.append second).length)
      (Fin ((second.renameWires wire).append
        (first.renameWires wire)).length) :=
  (FiniteEquiv.finCast (ItemSeq.length_append first second)).trans
    ((FiniteEquiv.finAddComm first.length second.length).trans
      ((extendWireEquiv
        (second.renameWiresPositionEquiv wire)
        (first.renameWiresPositionEquiv wire)).trans
      (FiniteEquiv.finCast (ItemSeq.length_append
        (second.renameWires wire) (first.renameWires wire)).symm)))

theorem ItemSeq.get_append_left :
    (first second : ItemSeq  wires rels) →
    (index : Fin first.length) →
    (first.append second).get
        (Fin.cast (ItemSeq.length_append first second).symm
          (Fin.castAdd second.length index)) =
      first.get index
  | .nil, _, index => Fin.elim0 index
  | .cons _ tail, second, index => by
      refine Fin.cases ?_ (fun rest => ?_) index
      · rfl
      · simpa [ItemSeq.append, ItemSeq.get, ItemSeq.length,
          ItemSeq.length_append] using
            ItemSeq.get_append_left tail second rest

theorem ItemSeq.get_append_right :
    (first second : ItemSeq  wires rels) →
    (index : Fin second.length) →
    (first.append second).get
        (Fin.cast (ItemSeq.length_append first second).symm
          (Fin.natAdd first.length index)) =
      second.get index
  | .nil, second, index => by
      have hindex :
          Fin.cast (ItemSeq.length_append (.nil : ItemSeq  wires rels)
            second).symm (Fin.natAdd 0 index) = index := by
        apply Fin.ext
        simp
      exact congrArg second.get hindex
  | .cons item tail, second, index => by
      have hindex :
          Fin.cast (ItemSeq.length_append (ItemSeq.cons item tail) second).symm
              (Fin.natAdd (ItemSeq.cons item tail).length index) =
            Fin.succ (Fin.cast (ItemSeq.length_append tail second).symm
              (Fin.natAdd tail.length index)) := by
        apply Fin.ext
        simp [ItemSeq.length, Nat.succ_add]
      rw [hindex]
      exact ItemSeq.get_append_right tail second index

theorem ItemSeq.get_renameWires :
    (items : ItemSeq  source rels) →
    (wire : Fin source → Fin target) →
    (index : Fin items.length) →
    (items.renameWires wire).get
        (items.renameWiresPositionEquiv wire index) =
      (items.get index).renameWires wire
  | .nil, _, index => Fin.elim0 index
  | .cons _ tail, wire, index => by
      refine Fin.cases ?_ (fun rest => ?_) index
      · rfl
      · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
          ItemSeq.renameWires_length] using
            ItemSeq.get_renameWires tail wire rest
mutual
  theorem Region.renameWires_renameRelations
      (region : Region  wires source)
      (wire : Fin wires → Fin targetWires)
      (relation : RelationRenaming source target) :
      (region.renameWires wire).renameRelations relation =
        (region.renameRelations relation).renameWires wire := by
    cases region with
    | mk localWires items =>
        exact congrArg (Region.mk localWires)
          (ItemSeq.renameWires_renameRelations items
            (extendWireRenaming wire localWires) relation)

  theorem Item.renameWires_renameRelations
      (item : Item  wires source)
      (wire : Fin wires → Fin targetWires)
      (relation : RelationRenaming source target) :
      (item.renameWires wire).renameRelations relation =
        (item.renameRelations relation).renameWires wire := by
    cases item with
    | atom rel arguments => rfl
    | identity arity arguments => rfl
    | cut body =>
        exact congrArg Item.cut
          (Region.renameWires_renameRelations body wire relation)
    | bubble arity body =>
        exact congrArg (Item.bubble arity)
          (Region.renameWires_renameRelations body wire
            (RelationRenaming.lift relation arity))

  theorem ItemSeq.renameWires_renameRelations
      (items : ItemSeq  wires source)
      (wire : Fin wires → Fin targetWires)
      (relation : RelationRenaming source target) :
      (items.renameWires wire).renameRelations relation =
        (items.renameRelations relation).renameWires wire := by
    cases items with
    | nil => rfl
    | cons item tail =>
        simp only [ItemSeq.renameWires, ItemSeq.renameRelations]
        rw [Item.renameWires_renameRelations,
          ItemSeq.renameWires_renameRelations]
end

private theorem conjoinLeftWire_natural
    (rho : Fin source → Fin target) :
    extendWireRenaming rho (firstLocal + secondLocal) ∘
        Region.conjoinLeftWire source firstLocal secondLocal =
      Region.conjoinLeftWire target firstLocal secondLocal ∘
        extendWireRenaming rho firstLocal := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinLeftWire, extendWireRenaming]
  · simp [Region.conjoinLeftWire, extendWireRenaming]

private theorem conjoinRightWire_natural
    (rho : Fin source → Fin target) :
    extendWireRenaming rho (firstLocal + secondLocal) ∘
        Region.conjoinRightWire source firstLocal secondLocal =
      Region.conjoinRightWire target firstLocal secondLocal ∘
        extendWireRenaming rho secondLocal := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinRightWire, extendWireRenaming]
  · simp [Region.conjoinRightWire, extendWireRenaming]

theorem Region.conjoin_renameWires
    (first second : Region  source rels)
    (rho : Fin source → Fin target) :
    (first.conjoin second).renameWires rho =
      (first.renameWires rho).conjoin (second.renameWires rho) := by
  cases first with
  | mk firstLocal firstItems =>
      cases second with
      | mk secondLocal secondItems =>
          simp only [Region.conjoin, Region.renameWires,
            ItemSeq.renameWires_append, ItemSeq.renameWires_comp]
          apply congrArg (Region.mk (firstLocal + secondLocal))
          rw [conjoinLeftWire_natural, conjoinRightWire_natural]

theorem Region.conjoin_renameRelations
    (first second : Region  wires source)
    (rho : RelationRenaming source target) :
    (first.conjoin second).renameRelations rho =
      (first.renameRelations rho).conjoin (second.renameRelations rho) := by
  cases first with
  | mk firstLocal firstItems =>
      cases second with
      | mk secondLocal secondItems =>
          simp only [Region.conjoin, Region.renameRelations,
            ItemSeq.renameRelations_append]
          apply congrArg (Region.mk (firstLocal + secondLocal))
          rw [ItemSeq.renameWires_renameRelations,
            ItemSeq.renameWires_renameRelations]

noncomputable def RegionIso.renameWiresEquiv
    (region : Region  source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    RegionIso  wire rels region (region.renameWires wire) := by
  apply Region.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso  wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso  wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso  wire rels (items.get index)
          ((items.renameWires wire).get
            (items.renameWiresPositionEquiv wire index)))
  · intro source rels localWires items itemsIH target wire
    refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
    have hwire :
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))).toFun =
          extendWireRenaming wire.toFun localWires := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [extendWireEquiv, extendWireRenaming]
      · simp [extendWireEquiv, extendWireRenaming, FiniteEquiv.refl]
    refine ItemSeqIso.permute
      (items.renameWiresPositionEquiv
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires)))) ?_
    intro index
    simpa only [Region.renameWires, hwire, FiniteEquiv.refl_apply] using
      itemsIH (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))) index
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity arguments target wire
    exact ItemIso.identity rfl
  · intro source rels body bodyIH target wire
    exact ItemIso.cut (bodyIH wire)
  · intro source rels arity body bodyIH target wire
    exact ItemIso.bubble (bodyIH wire)
  · intro source rels target wire
    intro index
    exact Fin.elim0 index
  · intro source rels item tail itemIH tailIH target wire
    intro index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using itemIH wire
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using tailIH wire rest

/-- Renaming the relation context uniformly on both sides preserves an
intrinsic region isomorphism. -/
noncomputable def RegionIso.renameRelations
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region  sourceWires sourceRels}
    {target : Region  targetWires sourceRels}
    (iso : RegionIso  wire sourceRels source target)
    (rho : RelationRenaming sourceRels targetRels) :
    RegionIso  wire targetRels
      (source.renameRelations rho) (target.renameRelations rho) := by
  exact RegionIso.rec
    (motive_1 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        RegionIso  wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (motive_2 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        ItemIso  wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (motive_3 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        ItemSeqIso  wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (fun {_ _ _ _} {_} {_} {_} {_} localEquiv _ itemsIH {_} rho =>
      RegionIso.mk localEquiv (itemsIH rho))
    (fun {_ _ _} {_} {_} relation {_} {_} arguments_eq {_} rho =>
      ItemIso.atom (rho relation) arguments_eq)
    (fun {_ _ _} {_} {_} {_} {_} arguments_eq {_} _ =>
      ItemIso.identity arguments_eq)
    (fun {_ _} {_} {_} {_} {_} _ bodyIH {_} rho =>
      ItemIso.cut (bodyIH rho))
    (fun {_ _ _} {_} {_} {_} {_} _ bodyIH {_} rho =>
      ItemIso.bubble (bodyIH (RelationRenaming.lift rho _)))
    (fun {_ _} {_} {_} {source} {target} positions _ itemsIH {_} rho => by
      let sourceLength := ItemSeq.renameRelations_length source rho
      let targetLength := ItemSeq.renameRelations_length target rho
      let renamedPositions := (FiniteEquiv.finCast sourceLength).trans
        (positions.trans (FiniteEquiv.finCast targetLength).symm)
      refine ItemSeqIso.permute renamedPositions ?_
      intro index
      let originalIndex := Fin.cast sourceLength index
      have sourceIndexEq :
          Fin.cast sourceLength.symm originalIndex = index := by
        apply Fin.ext
        rfl
      have targetIndexEq : renamedPositions index =
          Fin.cast targetLength.symm (positions originalIndex) := by
        apply Fin.ext
        rfl
      have sourceGet : (source.renameRelations rho).get index =
          (source.get originalIndex).renameRelations rho := by
        simpa only [sourceIndexEq] using
          ItemSeq.get_renameRelations source rho originalIndex
      have targetGet :
          (target.renameRelations rho).get (renamedPositions index) =
            (target.get (positions originalIndex)).renameRelations rho := by
        rw [targetIndexEq]
        exact ItemSeq.get_renameRelations target rho (positions originalIndex)
      rw [sourceGet, targetGet]
      exact itemsIH originalIndex rho)
    iso rho

noncomputable def ItemSeqIso.renameWiresEquiv
    (items : ItemSeq  source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemSeqIso  wire rels items (items.renameWires wire) := by
  refine ItemSeqIso.permute (items.renameWiresPositionEquiv wire) ?_
  apply ItemSeq.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso  wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso  wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso  wire rels (items.get index)
          ((items.renameWires wire).get
            (items.renameWiresPositionEquiv wire index)))
  · intro source rels localWires nested nestedIH target wire
    refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
    have hwire :
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))).toFun =
          extendWireRenaming wire.toFun localWires := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [extendWireEquiv, extendWireRenaming]
      · simp [extendWireEquiv, extendWireRenaming, FiniteEquiv.refl]
    refine ItemSeqIso.permute
      (nested.renameWiresPositionEquiv
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires)))) ?_
    intro index
    simpa only [Region.renameWires, hwire] using
      nestedIH (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))) index
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity arguments target wire
    exact ItemIso.identity rfl
  · intro source rels body bodyIH target wire
    exact ItemIso.cut (bodyIH wire)
  · intro source rels arity body bodyIH target wire
    exact ItemIso.bubble (bodyIH wire)
  · intro source rels target wire
    intro index
    exact Fin.elim0 index
  · intro source rels item tail itemIH tailIH target wire
    intro index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using itemIH wire
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using tailIH wire rest

/-- A single isomorphic item forms an isomorphic singleton block. -/
noncomputable def ItemSeqIso.singleton
    {source : Item sourceWires rels} {target : Item targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (item : ItemIso wire rels source target) :
    ItemSeqIso wire rels (.cons source .nil) (.cons target .nil) := by
  refine .permute (FiniteEquiv.refl (Fin 1)) ?_
  intro index
  exact Fin.cases item (fun rest => Fin.elim0 rest) index

noncomputable def ItemIso.renameWiresEquiv
    (item : Item  source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemIso  wire rels item (item.renameWires wire) := by
  apply Item.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso  wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso  wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso  wire rels (items.get index)
          ((items.renameWires wire).get
            (items.renameWiresPositionEquiv wire index)))
  · intro source rels localWires nested nestedIH target wire
    refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
    have hwire :
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))).toFun =
          extendWireRenaming wire.toFun localWires := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [extendWireEquiv, extendWireRenaming]
      · simp [extendWireEquiv, extendWireRenaming, FiniteEquiv.refl]
    refine ItemSeqIso.permute
      (nested.renameWiresPositionEquiv
        (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires)))) ?_
    intro index
    simpa only [Region.renameWires, hwire] using
      nestedIH (extendWireEquiv wire (FiniteEquiv.refl (Fin localWires))) index
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity arguments target wire
    exact ItemIso.identity rfl
  · intro source rels body bodyIH target wire
    exact ItemIso.cut (bodyIH wire)
  · intro source rels arity body bodyIH target wire
    exact ItemIso.bubble (bodyIH wire)
  · intro source rels target wire index
    exact Fin.elim0 index
  · intro source rels head tail headIH tailIH target wire index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using headIH wire
    · simpa [ItemSeq.get, ItemSeq.renameWiresPositionEquiv,
        ItemSeq.renameWires_length] using tailIH wire rest

noncomputable def ItemSeqIso.appendCommRename
    (first second : ItemSeq  source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemSeqIso  wire rels (first.append second)
      ((second.renameWires wire).append (first.renameWires wire)) := by
  refine ItemSeqIso.permute (first.appendRenamePositionSwap second wire) ?_
  intro index
  let sumIndex : Fin (first.length + second.length) :=
    Fin.cast (ItemSeq.length_append first second) index
  refine Fin.addCases (motive := fun splitIndex =>
      sumIndex = splitIndex →
        ItemIso  wire rels ((first.append second).get index)
          (((second.renameWires wire).append (first.renameWires wire)).get
            (first.appendRenamePositionSwap second wire index)))
    (fun firstIndex hsum => by
      have hsource : index =
        Fin.cast (ItemSeq.length_append first second).symm
          (Fin.castAdd second.length firstIndex) := by
        apply Fin.ext
        simpa [sumIndex] using congrArg Fin.val hsum
      subst index
      rw [ItemSeq.get_append_left]
      have htarget : first.appendRenamePositionSwap second wire
          (Fin.cast (ItemSeq.length_append first second).symm
            (Fin.castAdd second.length firstIndex)) =
        Fin.cast (ItemSeq.length_append
          (second.renameWires wire) (first.renameWires wire)).symm
          (Fin.natAdd (second.renameWires wire).length
            (first.renameWiresPositionEquiv wire firstIndex)) := by
        apply Fin.ext
        simp [ItemSeq.appendRenamePositionSwap, FiniteEquiv.finAddComm,
          FiniteEquiv.finCast, extendWireEquiv]
      rw [htarget, ItemSeq.get_append_right]
      rw [ItemSeq.get_renameWires]
      exact ItemIso.renameWiresEquiv (first.get firstIndex) wire)
    (fun secondIndex hsum => by
      have hsource : index =
        Fin.cast (ItemSeq.length_append first second).symm
          (Fin.natAdd first.length secondIndex) := by
        apply Fin.ext
        simpa [sumIndex] using congrArg Fin.val hsum
      subst index
      rw [ItemSeq.get_append_right]
      have htarget : first.appendRenamePositionSwap second wire
          (Fin.cast (ItemSeq.length_append first second).symm
            (Fin.natAdd first.length secondIndex)) =
        Fin.cast (ItemSeq.length_append
          (second.renameWires wire) (first.renameWires wire)).symm
          (Fin.castAdd (first.renameWires wire).length
            (second.renameWiresPositionEquiv wire secondIndex)) := by
        apply Fin.ext
        simp [ItemSeq.appendRenamePositionSwap, FiniteEquiv.finAddComm,
          FiniteEquiv.finCast, extendWireEquiv]
      rw [htarget, ItemSeq.get_append_left]
      rw [ItemSeq.get_renameWires]
      exact ItemIso.renameWiresEquiv (second.get secondIndex) wire)
    sumIndex rfl

noncomputable def RegionIso.conjoin_blank_left
    (region : Region  wires rels) :
    RegionIso  (FiniteEquiv.refl (Fin wires)) rels
      region (Region.blank.conjoin region) := by
  cases region with
  | mk localWires items =>
      let localEquiv : FiniteEquiv (Fin localWires) (Fin (0 + localWires)) :=
        FiniteEquiv.finCast (Nat.zero_add localWires).symm
      refine RegionIso.mk localEquiv ?_
      have hwire :
          (extendWireEquiv (FiniteEquiv.refl (Fin wires)) localEquiv).toFun =
            Region.conjoinRightWire wires 0 localWires := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
        · simp [extendWireEquiv, Region.conjoinRightWire,
            FiniteEquiv.refl]
        · apply Fin.ext
          simp [extendWireEquiv, Region.conjoinRightWire, localEquiv,
            FiniteEquiv.finCast]
      simpa only [Region.blank, Region.conjoin, ItemSeq.nil_append, hwire] using
        ItemSeqIso.renameWiresEquiv items
          (extendWireEquiv (FiniteEquiv.refl (Fin wires)) localEquiv)

noncomputable def RegionIso.conjoin_blank_right
    (region : Region  wires rels) :
    RegionIso  (FiniteEquiv.refl (Fin wires)) rels
      region (region.conjoin Region.blank) := by
  cases region with
  | mk localWires items =>
      let localEquiv : FiniteEquiv (Fin localWires) (Fin (localWires + 0)) :=
        FiniteEquiv.finCast (Nat.add_zero localWires).symm
      refine RegionIso.mk localEquiv ?_
      have hwire :
          (extendWireEquiv (FiniteEquiv.refl (Fin wires)) localEquiv).toFun =
            Region.conjoinLeftWire wires localWires 0 := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
        · simp [extendWireEquiv, Region.conjoinLeftWire,
            FiniteEquiv.refl]
        · apply Fin.ext
          rfl
      simpa only [Region.blank, Region.conjoin, ItemSeq.renameWires,
        ItemSeq.append_nil, hwire] using
        ItemSeqIso.renameWiresEquiv items
          (extendWireEquiv (FiniteEquiv.refl (Fin wires)) localEquiv)

noncomputable def RegionIso.conjoin_assoc
    (first second third : Region  wires rels) :
    RegionIso  (FiniteEquiv.refl (Fin wires)) rels
      ((first.conjoin second).conjoin third)
      (first.conjoin (second.conjoin third)) := by
  cases first with
  | mk firstLocal firstItems =>
    cases second with
    | mk secondLocal secondItems =>
      cases third with
      | mk thirdLocal thirdItems =>
        let localEquiv :
            FiniteEquiv (Fin ((firstLocal + secondLocal) + thirdLocal))
              (Fin (firstLocal + (secondLocal + thirdLocal))) :=
          FiniteEquiv.finCast (Nat.add_assoc firstLocal secondLocal thirdLocal)
        let extended := extendWireEquiv
          (FiniteEquiv.refl (Fin wires)) localEquiv
        refine RegionIso.mk localEquiv ?_
        let sourceItems :=
          (((firstItems.renameWires
              (Region.conjoinLeftWire wires firstLocal secondLocal)).append
            (secondItems.renameWires
              (Region.conjoinRightWire wires firstLocal secondLocal))).renameWires
            (Region.conjoinLeftWire wires (firstLocal + secondLocal) thirdLocal)).append
          (thirdItems.renameWires
            (Region.conjoinRightWire wires (firstLocal + secondLocal) thirdLocal))
        have hfirst :
            extended.toFun ∘
                Region.conjoinLeftWire wires (firstLocal + secondLocal) thirdLocal ∘
                Region.conjoinLeftWire wires firstLocal secondLocal =
              Region.conjoinLeftWire wires firstLocal (secondLocal + thirdLocal) := by
          funext index
          refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
          · simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinLeftWire, FiniteEquiv.finCast,
              FiniteEquiv.refl, Function.comp_def]
          · apply Fin.ext
            simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinLeftWire, FiniteEquiv.finCast,
              FiniteEquiv.refl, Function.comp_def]
        have hsecond :
            extended.toFun ∘
                Region.conjoinLeftWire wires (firstLocal + secondLocal) thirdLocal ∘
                Region.conjoinRightWire wires firstLocal secondLocal =
              Region.conjoinRightWire wires firstLocal (secondLocal + thirdLocal) ∘
                Region.conjoinLeftWire wires secondLocal thirdLocal := by
          funext index
          refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
          · simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinLeftWire, Region.conjoinRightWire,
              FiniteEquiv.finCast, FiniteEquiv.refl, Function.comp_def]
          · apply Fin.ext
            simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinLeftWire, Region.conjoinRightWire,
              FiniteEquiv.finCast, FiniteEquiv.refl, Function.comp_def]
        have hthird :
            extended.toFun ∘
                Region.conjoinRightWire wires (firstLocal + secondLocal) thirdLocal =
              Region.conjoinRightWire wires firstLocal (secondLocal + thirdLocal) ∘
                Region.conjoinRightWire wires secondLocal thirdLocal := by
          funext index
          refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
          · simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinRightWire, FiniteEquiv.finCast,
              FiniteEquiv.refl]
          · apply Fin.ext
            simp [extended, localEquiv, extendWireEquiv,
              Region.conjoinRightWire, FiniteEquiv.finCast,
              FiniteEquiv.refl, Nat.add_assoc]
        have hitems :
            sourceItems.renameWires extended =
              (firstItems.renameWires
                (Region.conjoinLeftWire wires firstLocal
                  (secondLocal + thirdLocal))).append
              (((secondItems.renameWires
                  (Region.conjoinLeftWire wires secondLocal thirdLocal)).append
                (thirdItems.renameWires
                  (Region.conjoinRightWire wires secondLocal thirdLocal))).renameWires
                (Region.conjoinRightWire wires firstLocal
                  (secondLocal + thirdLocal))) := by
          simp only [sourceItems, ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp]
          rw [hfirst, hsecond, hthird]
          exact ItemSeq.append_assoc _ _ _
        have hiso := ItemSeqIso.renameWiresEquiv sourceItems extended
        rw [hitems] at hiso
        simpa only [Region.conjoin, sourceItems, extended] using hiso

noncomputable def RegionIso.conjoin_comm
    (first second : Region  wires rels) :
    RegionIso  (FiniteEquiv.refl (Fin wires)) rels
      (first.conjoin second) (second.conjoin first) := by
  cases first with
  | mk firstLocal firstItems =>
    cases second with
    | mk secondLocal secondItems =>
      let localEquiv := FiniteEquiv.finAddComm firstLocal secondLocal
      let extended := extendWireEquiv
        (FiniteEquiv.refl (Fin wires)) localEquiv
      refine RegionIso.mk localEquiv ?_
      have hfirst :
          extended.toFun ∘
              Region.conjoinLeftWire wires firstLocal secondLocal =
            Region.conjoinRightWire wires secondLocal firstLocal := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
        · simp [extended, localEquiv, extendWireEquiv,
            Region.conjoinLeftWire, Region.conjoinRightWire,
            FiniteEquiv.finAddComm, FiniteEquiv.refl]
        · apply Fin.ext
          simp [extended, localEquiv, extendWireEquiv,
            Region.conjoinLeftWire, Region.conjoinRightWire,
            FiniteEquiv.finAddComm, FiniteEquiv.refl]
      have hsecond :
          extended.toFun ∘
              Region.conjoinRightWire wires firstLocal secondLocal =
            Region.conjoinLeftWire wires secondLocal firstLocal := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
        · simp [extended, localEquiv, extendWireEquiv,
            Region.conjoinLeftWire, Region.conjoinRightWire,
            FiniteEquiv.finAddComm, FiniteEquiv.refl]
        · apply Fin.ext
          simp [extended, localEquiv, extendWireEquiv,
            Region.conjoinLeftWire, Region.conjoinRightWire,
            FiniteEquiv.finAddComm, FiniteEquiv.refl]
      have hiso := ItemSeqIso.appendCommRename
        (firstItems.renameWires
          (Region.conjoinLeftWire wires firstLocal secondLocal))
        (secondItems.renameWires
          (Region.conjoinRightWire wires firstLocal secondLocal)) extended
      simpa only [Region.conjoin, ItemSeq.renameWires_comp,
        hfirst, hsecond] using hiso

/-- Pull a focused-frame presentation back across an ambient wire renaming of
its source sequence. -/
noncomputable def ItemSeqIso.Frame.prependRenameWires
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    (sourceIndex : Fin source.length) {targetIndex : Fin target.length}
    (frame : ItemSeqIso.Frame secondWire
      (source.renameWiresPositionEquiv firstWire sourceIndex) targetIndex) :
    ItemSeqIso.Frame (firstWire.trans secondWire) sourceIndex targetIndex := by
  let firstPositions := source.renameWiresPositionEquiv firstWire
  refine {
    positions := firstPositions.trans frame.positions
    mapped := ?_
    siblings := ?_
  }
  · exact frame.mapped
  · intro index hne
    have hrenamedNe : firstPositions index ≠ firstPositions sourceIndex := by
      intro heq
      exact hne (firstPositions.injective heq)
    have hfirst := ItemIso.renameWiresEquiv (source.get index) firstWire
    have hsecond := frame.siblings (firstPositions index) hrenamedNe
    have hsecond' : ItemIso  secondWire rels
        ((source.get index).renameWires firstWire)
        (target.get (frame.positions (firstPositions index))) := by
      simpa only [firstPositions, ItemSeq.get_renameWires] using hsecond
    exact hfirst.trans hsecond'

/-- Push a focused-frame presentation forward across an ambient wire
renaming of its target sequence. -/
noncomputable def ItemSeqIso.Frame.appendRenameWires
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (lastWire : FiniteEquiv (Fin targetWires) (Fin finalWires))
    {sourceIndex : Fin source.length} (targetIndex : Fin target.length)
    (frame : ItemSeqIso.Frame firstWire sourceIndex targetIndex) :
    ItemSeqIso.Frame (firstWire.trans lastWire) sourceIndex
      (target.renameWiresPositionEquiv lastWire targetIndex) := by
  let lastPositions := target.renameWiresPositionEquiv lastWire
  refine {
    positions := frame.positions.trans lastPositions
    mapped := congrArg lastPositions frame.mapped
    siblings := ?_
  }
  intro index hne
  have hfirst := frame.siblings index hne
  have hlast := ItemIso.renameWiresEquiv
    (target.get (frame.positions index)) lastWire
  have hlast' : ItemIso  lastWire rels
      (target.get (frame.positions index))
      ((target.renameWires lastWire).get
        (lastPositions (frame.positions index))) := by
    simpa only [lastPositions, ItemSeq.get_renameWires] using hlast
  exact hfirst.trans hlast'

/-- Transport a focused-frame presentation through canonical source and
target wire presentations, preserving the distinguished position values. -/
structure ItemSeqIso.Frame.Indexed
    {sourceWires targetWires : Nat} {rels : Theory.RelCtx}
    (source : ItemSeq sourceWires rels) (target : ItemSeq targetWires rels)
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (sourcePosition targetPosition : Nat) where
  sourceIndex : Fin source.length
  targetIndex : Fin target.length
  sourceIndex_eq : sourceIndex.val = sourcePosition
  targetIndex_eq : targetIndex.val = targetPosition
  frame : ItemSeqIso.Frame wire sourceIndex targetIndex

noncomputable def ItemSeqIso.Frame.pullPush
    {sourceWires middleSourceWires middleTargetWires targetWires : Nat}
    {rels : Theory.RelCtx}
    {source : ItemSeq  sourceWires rels}
    {middleSource : ItemSeq  middleSourceWires rels}
    {middleTarget : ItemSeq  middleTargetWires rels}
    {target : ItemSeq  targetWires rels}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleSourceWires))
    (middleWire : FiniteEquiv (Fin middleSourceWires)
      (Fin middleTargetWires))
    (lastWire : FiniteEquiv (Fin middleTargetWires) (Fin targetWires))
    (finalWire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (hsource : source.renameWires firstWire = middleSource)
    (htarget : middleTarget.renameWires lastWire = target)
    (hwire : (firstWire.trans middleWire).trans lastWire = finalWire)
    {middleSourceIndex : Fin middleSource.length}
    {middleTargetIndex : Fin middleTarget.length}
    (frame : ItemSeqIso.Frame middleWire middleSourceIndex
      middleTargetIndex) :
    ItemSeqIso.Frame.Indexed source target finalWire
      middleSourceIndex.val middleTargetIndex.val := by
  subst middleSource
  let sourceIndex :=
    (source.renameWiresPositionEquiv firstWire).symm middleSourceIndex
  have hsourceMapped :
      source.renameWiresPositionEquiv firstWire sourceIndex =
        middleSourceIndex :=
    (source.renameWiresPositionEquiv firstWire).right_inv middleSourceIndex
  rw [← hsourceMapped] at frame
  let pulled := frame.prependRenameWires firstWire sourceIndex
  let targetIndex :=
    middleTarget.renameWiresPositionEquiv lastWire middleTargetIndex
  let pushed := pulled.appendRenameWires lastWire middleTargetIndex
  subst target
  have finalFrame : ItemSeqIso.Frame finalWire sourceIndex targetIndex :=
    pushed.castWire hwire
  exact ⟨sourceIndex, targetIndex, rfl, rfl, finalFrame⟩

/-- An alignment between two single-hole contexts. Each enclosing frame owns
its complete occurrence permutation; the recursively aligned child supplies
only the distinguished cut/bubble item. This permits siblings to move across
the focused position. -/
inductive DiagramContextIso :
    {sourceOuter sourceHole targetOuter targetHole : Nat} →
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)) →
    (holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)) →
    (outerRels holeRels : Theory.RelCtx) →
    DiagramContext  sourceOuter sourceHole outerRels holeRels →
    DiagramContext  targetOuter targetHole outerRels holeRels → Type
  | hole
      (wire : FiniteEquiv (Fin wires) (Fin targetWires)) :
      DiagramContextIso  wire wire rels rels
        (.hole : DiagramContext  wires wires rels rels)
        (.hole : DiagramContext  targetWires targetWires rels rels)
  | cut
      {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
      {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
      (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
      (sourceBefore sourceAfter :
        ItemSeq  (sourceOuter + sourceLocal) outerRels)
      (targetBefore targetAfter :
        ItemSeq  (targetOuter + targetLocal) outerRels)
      (sourceChild : DiagramContext
        (sourceOuter + sourceLocal) sourceHole outerRels holeRels)
      (targetChild : DiagramContext
        (targetOuter + targetLocal) targetHole outerRels holeRels)
      (child : DiagramContextIso
        (extendWireEquiv outerWire localWire) holeWire outerRels holeRels
        sourceChild targetChild)
      (frame : ∀ {sourceBody : Region
          (sourceOuter + sourceLocal) outerRels}
          {targetBody : Region
            (targetOuter + targetLocal) outerRels},
        ItemIso  (extendWireEquiv outerWire localWire) outerRels
            (.cut sourceBody) (.cut targetBody) →
          ItemSeqIso  (extendWireEquiv outerWire localWire) outerRels
            (sourceBefore.append (.cons (.cut sourceBody) sourceAfter))
            (targetBefore.append (.cons (.cut targetBody) targetAfter))) :
      DiagramContextIso  outerWire holeWire outerRels holeRels
        (.cut sourceLocal sourceBefore sourceAfter sourceChild)
        (.cut targetLocal targetBefore targetAfter targetChild)
  | bubble
      {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
      {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
      (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
      (sourceBefore sourceAfter :
        ItemSeq  (sourceOuter + sourceLocal) outerRels)
      (targetBefore targetAfter :
        ItemSeq  (targetOuter + targetLocal) outerRels)
      (sourceChild : DiagramContext
        (sourceOuter + sourceLocal) sourceHole (arity :: outerRels) holeRels)
      (targetChild : DiagramContext
        (targetOuter + targetLocal) targetHole (arity :: outerRels) holeRels)
      (child : DiagramContextIso
        (extendWireEquiv outerWire localWire) holeWire
        (arity :: outerRels) holeRels sourceChild targetChild)
      (frame : ∀ {sourceBody : Region
          (sourceOuter + sourceLocal) (arity :: outerRels)}
          {targetBody : Region
            (targetOuter + targetLocal) (arity :: outerRels)},
        ItemIso  (extendWireEquiv outerWire localWire) outerRels
            (.bubble arity sourceBody) (.bubble arity targetBody) →
          ItemSeqIso  (extendWireEquiv outerWire localWire) outerRels
            (sourceBefore.append
              (.cons (.bubble arity sourceBody) sourceAfter))
            (targetBefore.append
              (.cons (.bubble arity targetBody) targetAfter))) :
      DiagramContextIso  outerWire holeWire outerRels holeRels
        (.bubble sourceLocal sourceBefore sourceAfter arity sourceChild)
        (.bubble targetLocal targetBefore targetAfter arity targetChild)

noncomputable def DiagramContextIso.symm
    (iso : DiagramContextIso outerWire holeWire outerRels holeRels
      source target) :
    DiagramContextIso outerWire.symm holeWire.symm outerRels holeRels
      target source := by
  induction iso with
  | hole wire => exact .hole wire.symm
  | cut localWire sourceBefore sourceAfter targetBefore targetAfter
      sourceChild targetChild child frame induction =>
      rw [extendWireEquiv_symm] at induction
      apply DiagramContextIso.cut localWire.symm targetBefore targetAfter
        sourceBefore sourceAfter targetChild sourceChild induction
      intro targetBody sourceBody replacement
      exact (frame replacement.symm).symm
  | bubble localWire sourceBefore sourceAfter targetBefore targetAfter
      sourceChild targetChild child frame induction =>
      rw [extendWireEquiv_symm] at induction
      apply DiagramContextIso.bubble localWire.symm targetBefore targetAfter
        sourceBefore sourceAfter targetChild sourceChild induction
      intro targetBody sourceBody replacement
      exact (frame replacement.symm).symm

/-- Isomorphic single-hole contexts have the same number of enclosing cuts.
The occurrence permutations and wire transports carried by the isomorphism
do not affect polarity. -/
theorem DiagramContextIso.cutDepth_eq
    (iso : DiagramContextIso  outerWire holeWire outerRels holeRels
      source target) :
    source.cutDepth = target.cutDepth := by
  induction iso <;> simp_all [DiagramContext.cutDepth]

/-- Transporting only the relation-context index leaves context polarity
unchanged. -/
theorem DiagramContext.cutDepth_castRels
    {sourceRels targetRels : Theory.RelCtx}
    {outerWires holeWires : Nat} {outerRels : Theory.RelCtx}
    (equality : sourceRels = targetRels)
    (context : DiagramContext  outerWires holeWires outerRels
      sourceRels) :
    (equality ▸ context).cutDepth = context.cutDepth := by
  subst targetRels
  rfl

/-- Build one aligned cut-context layer from the recursively aligned child
and the compiler's permutation of every nonfocused sibling. -/
def DiagramContextIso.cutFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceItems : ItemSeq  (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq  (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (sourceFocus : ItemSeq.Focus sourceItems)
    (targetFocus : ItemSeq.Focus targetItems)
    (sourceAt : sourceItems.focusAt? sourceIndex.val = some sourceFocus)
    (targetAt : targetItems.focusAt? targetIndex.val = some targetFocus)
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    (sourceChild : DiagramContext
      (sourceOuter + sourceLocal) sourceHole outerRels holeRels)
    (targetChild : DiagramContext
      (targetOuter + targetLocal) targetHole outerRels holeRels)
    (child : DiagramContextIso
      (extendWireEquiv outerWire localWire) holeWire outerRels holeRels
      sourceChild targetChild) :
    DiagramContextIso  outerWire holeWire outerRels holeRels
      (.cut sourceLocal sourceFocus.before sourceFocus.after sourceChild)
      (.cut targetLocal targetFocus.before targetFocus.after targetChild) := by
  apply DiagramContextIso.cut localWire sourceFocus.before sourceFocus.after
    targetFocus.before targetFocus.after sourceChild targetChild child
  intro sourceBody targetBody replacement
  have replaced := frame.replaceAt (.cut sourceBody) (.cut targetBody) replacement
  rw [ItemSeq.replaceAt_eq_focus sourceItems sourceIndex sourceFocus sourceAt,
    ItemSeq.replaceAt_eq_focus targetItems targetIndex targetFocus targetAt]
    at replaced
  exact replaced

/-- Bubble counterpart of `DiagramContextIso.cutFrame`. -/
def DiagramContextIso.bubbleFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceItems : ItemSeq  (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq  (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (sourceFocus : ItemSeq.Focus sourceItems)
    (targetFocus : ItemSeq.Focus targetItems)
    (sourceAt : sourceItems.focusAt? sourceIndex.val = some sourceFocus)
    (targetAt : targetItems.focusAt? targetIndex.val = some targetFocus)
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    (sourceChild : DiagramContext
      (sourceOuter + sourceLocal) sourceHole (arity :: outerRels) holeRels)
    (targetChild : DiagramContext
      (targetOuter + targetLocal) targetHole (arity :: outerRels) holeRels)
    (child : DiagramContextIso
      (extendWireEquiv outerWire localWire) holeWire
      (arity :: outerRels) holeRels sourceChild targetChild) :
    DiagramContextIso  outerWire holeWire outerRels holeRels
      (.bubble sourceLocal sourceFocus.before sourceFocus.after arity sourceChild)
      (.bubble targetLocal targetFocus.before targetFocus.after arity targetChild) := by
  apply DiagramContextIso.bubble localWire sourceFocus.before sourceFocus.after
    targetFocus.before targetFocus.after sourceChild targetChild child
  intro sourceBody targetBody replacement
  have replaced := frame.replaceAt
    (.bubble arity sourceBody) (.bubble arity targetBody) replacement
  rw [ItemSeq.replaceAt_eq_focus sourceItems sourceIndex sourceFocus sourceAt,
    ItemSeq.replaceAt_eq_focus targetItems targetIndex targetFocus targetAt]
    at replaced
  exact replaced

/-- Build one cut frame directly from compiler-context wire indices. The two
length equalities are eliminated here so callers never transport a compiled
tree or thread decomposed split state. -/
def DiagramContextIso.cutCompilerFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceFull targetFull : Nat}
    (sourceSplit : sourceFull = sourceOuter + sourceLocal)
    (targetSplit : targetFull = targetOuter + targetLocal)
    (sourceBefore sourceAfter : ItemSeq sourceFull outerRels)
    (targetBefore targetAfter : ItemSeq targetFull outerRels)
    (sourceChild : DiagramContext sourceFull sourceHole outerRels holeRels)
    (targetChild : DiagramContext targetFull targetHole outerRels holeRels)
    (child : DiagramContextIso
      (extendWireEquiv outerWire localWire)
      holeWire outerRels holeRels (sourceSplit ▸ sourceChild)
        (targetSplit ▸ targetChild))
    (frame : ∀ {sourceBody : Region (sourceOuter + sourceLocal) outerRels}
        {targetBody : Region (targetOuter + targetLocal) outerRels},
      ItemIso (extendWireEquiv outerWire localWire) outerRels
          (.cut sourceBody) (.cut targetBody) →
        ItemSeqIso (extendWireEquiv outerWire localWire) outerRels
          ((sourceBefore.castWiresEq sourceSplit).append
            (.cons (.cut sourceBody) (sourceAfter.castWiresEq sourceSplit)))
          ((targetBefore.castWiresEq targetSplit).append
            (.cons (.cut targetBody) (targetAfter.castWiresEq targetSplit)))) :
    DiagramContextIso outerWire holeWire outerRels holeRels
      (.cut sourceLocal (sourceBefore.castWiresEq sourceSplit)
        (sourceAfter.castWiresEq sourceSplit)
        (sourceSplit ▸ sourceChild))
      (.cut targetLocal (targetBefore.castWiresEq targetSplit)
        (targetAfter.castWiresEq targetSplit)
        (targetSplit ▸ targetChild)) := by
  subst sourceFull
  subst targetFull
  exact .cut localWire sourceBefore sourceAfter targetBefore targetAfter
    sourceChild targetChild child frame

/-- Bubble counterpart of `DiagramContextIso.cutCompilerFrame`. -/
def DiagramContextIso.bubbleCompilerFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceFull targetFull : Nat}
    (sourceSplit : sourceFull = sourceOuter + sourceLocal)
    (targetSplit : targetFull = targetOuter + targetLocal)
    (sourceBefore sourceAfter : ItemSeq sourceFull outerRels)
    (targetBefore targetAfter : ItemSeq targetFull outerRels)
    (sourceChild : DiagramContext sourceFull sourceHole
      (arity :: outerRels) holeRels)
    (targetChild : DiagramContext targetFull targetHole
      (arity :: outerRels) holeRels)
    (child : DiagramContextIso
      (extendWireEquiv outerWire localWire)
      holeWire (arity :: outerRels) holeRels (sourceSplit ▸ sourceChild)
        (targetSplit ▸ targetChild))
    (frame : ∀
        {sourceBody : Region (sourceOuter + sourceLocal) (arity :: outerRels)}
        {targetBody : Region (targetOuter + targetLocal) (arity :: outerRels)},
      ItemIso (extendWireEquiv outerWire localWire) outerRels
          (.bubble arity sourceBody) (.bubble arity targetBody) →
        ItemSeqIso (extendWireEquiv outerWire localWire) outerRels
          ((sourceBefore.castWiresEq sourceSplit).append
            (.cons (.bubble arity sourceBody)
              (sourceAfter.castWiresEq sourceSplit)))
          ((targetBefore.castWiresEq targetSplit).append
            (.cons (.bubble arity targetBody)
              (targetAfter.castWiresEq targetSplit)))) :
    DiagramContextIso outerWire holeWire outerRels holeRels
      (.bubble sourceLocal (sourceBefore.castWiresEq sourceSplit)
        (sourceAfter.castWiresEq sourceSplit) arity
        (sourceSplit ▸ sourceChild))
      (.bubble targetLocal (targetBefore.castWiresEq targetSplit)
        (targetAfter.castWiresEq targetSplit) arity
        (targetSplit ▸ targetChild)) := by
  subst sourceFull
  subst targetFull
  exact .bubble localWire sourceBefore sourceAfter targetBefore targetAfter
    sourceChild targetChild child frame

/-- A site isomorphism lifts through every aligned compiler frame to the
complete root. -/
noncomputable def DiagramContextIso.fill
    (alignment : DiagramContextIso  outerWire holeWire
      outerRels holeRels sourceContext targetContext)
    (site : RegionIso  holeWire holeRels sourceSite targetSite) :
    RegionIso  outerWire outerRels
      (sourceContext.fill sourceSite) (targetContext.fill targetSite) := by
  induction alignment with
  | hole wire => exact site
  | cut localWire sourceBefore sourceAfter targetBefore targetAfter
      sourceChild targetChild child frame ih =>
      exact RegionIso.mk localWire (frame (ItemIso.cut (ih site)))
  | bubble localWire sourceBefore sourceAfter targetBefore targetAfter
      sourceChild targetChild child frame ih =>
      exact RegionIso.mk localWire (frame (ItemIso.bubble (ih site)))

/-- Root form of `DiagramContextIso.fill`, with reconstruction equations for
the source and target focuses. -/
noncomputable def DiagramContextIso.root
    {sourceRoot : Region  sourceOuter outerRels}
    {targetRoot : Region  targetOuter outerRels}
    {sourceContext : DiagramContext  sourceOuter sourceHole
      outerRels holeRels}
    {targetContext : DiagramContext  targetOuter targetHole
      outerRels holeRels}
    {sourceSite : Region  sourceHole holeRels}
    {targetSite : Region  targetHole holeRels}
    (alignment : DiagramContextIso  outerWire holeWire
      outerRels holeRels sourceContext targetContext)
    (site : RegionIso  holeWire holeRels sourceSite targetSite)
    (sourceRebuild : sourceContext.fill sourceSite = sourceRoot)
    (targetRebuild : targetContext.fill targetSite = targetRoot) :
    RegionIso  outerWire outerRels sourceRoot targetRoot := by
  rw [← sourceRebuild, ← targetRebuild]
  exact alignment.fill site

end VisualProof.Diagram
