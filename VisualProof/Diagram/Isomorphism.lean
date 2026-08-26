import VisualProof.Data.Finite
import VisualProof.Diagram.Context

namespace VisualProof.Diagram

open VisualProof
open Theory

/-- A bijective, signature-preserving correspondence between wire contexts. -/
structure WireEquiv (source target : List Sig) where
  toRenaming : WireRenaming source target
  invRenaming : WireRenaming target source
  left_inv : ∀ {signature} (wire : Var source signature),
    invRenaming (toRenaming wire) = wire
  right_inv : ∀ {signature} (wire : Var target signature),
    toRenaming (invRenaming wire) = wire

instance : CoeFun (WireEquiv source target)
    (fun _ => ∀ {signature}, Var source signature → Var target signature) :=
  ⟨fun equivalence => fun wire => equivalence.toRenaming wire⟩

namespace WireEquiv

@[ext] theorem ext (left right : WireEquiv source target)
    (applyEq : ∀ {signature} (wire : Var source signature),
      left wire = right wire) : left = right := by
  cases left with
  | mk leftTo leftInv leftLeft leftRight =>
      cases right with
      | mk rightTo rightInv rightLeft rightRight =>
          have toEq : leftTo = rightTo := by
            apply WireRenaming.ext
            exact applyEq
          subst rightTo
          have invEq : leftInv = rightInv := by
            apply WireRenaming.ext
            intro signature wire
            calc
              leftInv wire = leftInv (leftTo (rightInv wire)) := by
                rw [rightRight]
              _ = rightInv wire := leftLeft (rightInv wire)
          subst rightInv
          rfl

def refl (context : List Sig) : WireEquiv context context where
  toRenaming := WireRenaming.id
  invRenaming := WireRenaming.id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def ofEq (equality : source = target) : WireEquiv source target := by
  subst target
  exact refl source

@[simp] theorem ofEq_index_val (equality : source = target)
    (wire : Var source signature) :
    (ofEq equality wire).index.val = wire.index.val := by
  subst target
  rfl

def symm (equivalence : WireEquiv source target) : WireEquiv target source where
  toRenaming := equivalence.invRenaming
  invRenaming := equivalence.toRenaming
  left_inv := equivalence.right_inv
  right_inv := equivalence.left_inv

def trans (first : WireEquiv source middle)
    (second : WireEquiv middle target) : WireEquiv source target where
  toRenaming := WireRenaming.comp second.toRenaming first.toRenaming
  invRenaming := WireRenaming.comp first.invRenaming second.invRenaming
  left_inv := by
    intro signature wire
    simp only [WireRenaming.comp]
    rw [second.left_inv, first.left_inv]
  right_inv := by
    intro signature wire
    simp only [WireRenaming.comp]
    rw [first.right_inv, second.right_inv]

@[simp] theorem trans_refl (equivalence : WireEquiv source target) :
    equivalence.trans (refl target) = equivalence := by
  apply WireEquiv.ext
  intro signature wire
  rfl

@[simp] theorem refl_trans (equivalence : WireEquiv source target) :
    (refl source).trans equivalence = equivalence := by
  apply WireEquiv.ext
  intro signature wire
  rfl

private def appendRenaming
    (left : WireRenaming sourceLeft targetLeft)
    (right : WireRenaming sourceRight targetRight) :
    WireRenaming (sourceLeft ++ sourceRight) (targetLeft ++ targetRight) :=
  ⟨Var.appendMap
    (fun wire => (left wire).appendLeft targetRight)
    (fun wire => Var.appendRight targetLeft (right wire))⟩

def append (left : WireEquiv sourceLeft targetLeft)
    (right : WireEquiv sourceRight targetRight) :
    WireEquiv (sourceLeft ++ sourceRight) (targetLeft ++ targetRight) where
  toRenaming := appendRenaming left.toRenaming right.toRenaming
  invRenaming := appendRenaming left.invRenaming right.invRenaming
  left_inv := by
    intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        appendRenaming left.invRenaming right.invRenaming
          (appendRenaming left.toRenaming right.toRenaming wire) = wire)
    · intro signature inherited
      simp [appendRenaming, left.left_inv]
    · intro signature localWire
      simp [appendRenaming, right.left_inv]
  right_inv := by
    intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        appendRenaming left.toRenaming right.toRenaming
          (appendRenaming left.invRenaming right.invRenaming wire) = wire)
    · intro signature inherited
      simp [appendRenaming, left.right_inv]
    · intro signature localWire
      simp [appendRenaming, right.right_inv]

/-- Exchange two adjacent typed wire blocks. -/
def swap (left right : List Sig) :
    WireEquiv (left ++ right) (right ++ left) where
  toRenaming := ⟨Var.appendMap
      (fun inherited => Var.appendRight right inherited)
      (fun localWire => localWire.appendLeft left)⟩
  invRenaming := ⟨Var.appendMap
      (fun inherited => Var.appendRight left inherited)
      (fun localWire => localWire.appendLeft right)⟩
  left_inv := by
    intro signature wire
    apply Var.appendCases (left := left) (right := right)
      (motive := fun wire =>
        Var.appendMap
          (fun inherited => Var.appendRight left inherited)
          (fun localWire => localWire.appendLeft right)
          (Var.appendMap
            (fun inherited => Var.appendRight right inherited)
            (fun localWire => localWire.appendLeft left) wire) = wire)
    · intro inheritedSignature inherited
      simp
    · intro localSignature localWire
      simp
  right_inv := by
    intro signature wire
    apply Var.appendCases (left := right) (right := left)
      (motive := fun wire =>
        Var.appendMap
          (fun inherited => Var.appendRight right inherited)
          (fun localWire => localWire.appendLeft left)
          (Var.appendMap
            (fun inherited => Var.appendRight left inherited)
            (fun localWire => localWire.appendLeft right) wire) = wire)
    · intro inheritedSignature inherited
      simp
    · intro localSignature localWire
      simp

/-- Move a final typed block between a prefix and middle block. -/
def rotate (leading middle suffix : List Sig) :
    WireEquiv ((leading ++ middle) ++ suffix)
      (leading ++ (suffix ++ middle)) :=
  (ofEq (List.append_assoc leading middle suffix)).trans
    ((refl leading).append (swap middle suffix))

@[simp] theorem rotate_apply_leading
    (wire : Var leading signature) :
    rotate leading middle suffix
        ((wire.appendLeft middle).appendLeft suffix) =
      wire.appendLeft (suffix ++ middle) := by
  have reassociated :
      ofEq (List.append_assoc leading middle suffix)
          ((wire.appendLeft middle).appendLeft suffix) =
        wire.appendLeft (middle ++ suffix) := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    simp
  change ((refl leading).append (swap middle suffix))
    (ofEq (List.append_assoc leading middle suffix)
      ((wire.appendLeft middle).appendLeft suffix)) = _
  rw [reassociated]
  simp [append, appendRenaming, swap, refl, WireRenaming.id]

@[simp] theorem rotate_apply_middle
    (wire : Var middle signature) :
    rotate leading middle suffix
        ((Var.appendRight leading wire).appendLeft suffix) =
      Var.appendRight leading (Var.appendRight suffix wire) := by
  have reassociated :
      ofEq (List.append_assoc leading middle suffix)
          ((Var.appendRight leading wire).appendLeft suffix) =
        Var.appendRight leading (wire.appendLeft suffix) := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    simp
  change ((refl leading).append (swap middle suffix))
    (ofEq (List.append_assoc leading middle suffix)
      ((Var.appendRight leading wire).appendLeft suffix)) = _
  rw [reassociated]
  simp [append, appendRenaming, swap, refl, WireRenaming.id]

@[simp] theorem rotate_apply_suffix
    (wire : Var suffix signature) :
    rotate leading middle suffix
        (Var.appendRight (leading ++ middle) wire) =
      Var.appendRight leading (wire.appendLeft middle) := by
  have reassociated :
      ofEq (List.append_assoc leading middle suffix)
          (Var.appendRight (leading ++ middle) wire) =
        Var.appendRight leading (Var.appendRight middle wire) := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    simp
    omega
  change ((refl leading).append (swap middle suffix))
    (ofEq (List.append_assoc leading middle suffix)
      (Var.appendRight (leading ++ middle) wire)) = _
  rw [reassociated]
  simp [append, appendRenaming, swap, refl, WireRenaming.id]

@[simp] theorem append_apply_left
    (left : WireEquiv sourceLeft targetLeft)
    (right : WireEquiv sourceRight targetRight)
    (wire : Var sourceLeft signature) :
    left.append right (wire.appendLeft sourceRight) =
      (left wire).appendLeft targetRight := by
    simp [append, appendRenaming]

@[simp] theorem append_apply_right
    (left : WireEquiv sourceLeft targetLeft)
    (right : WireEquiv sourceRight targetRight)
    (wire : Var sourceRight signature) :
    left.append right (Var.appendRight sourceLeft wire) =
      Var.appendRight targetLeft (right wire) := by
  simp [append, appendRenaming]

@[simp] theorem refl_apply (wire : Var context signature) :
    WireEquiv.refl context wire = wire := rfl

theorem refl_append_left_index_val
    (right : WireEquiv sourceRight targetRight)
    (wire : Var left signature) :
    (((WireEquiv.refl left).append right)
      (wire.appendLeft sourceRight)).index.val = wire.index.val := by
  rw [WireEquiv.append_apply_left]
  rw [WireEquiv.refl_apply]
  exact Var.index_appendLeft wire targetRight

@[simp] theorem symm_apply_apply
    (equivalence : WireEquiv source target)
    (wire : Var source signature) :
    equivalence.symm (equivalence wire) = wire :=
  equivalence.left_inv wire

@[simp] theorem apply_symm_apply
    (equivalence : WireEquiv source target)
    (wire : Var target signature) :
    equivalence (equivalence.symm wire) = wire :=
  equivalence.right_inv wire

end WireEquiv

theorem WireEquiv.append_refl (left right : List Sig) :
    (WireEquiv.refl left).append (WireEquiv.refl right) =
      WireEquiv.refl (left ++ right) := by
  apply WireEquiv.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      ((WireEquiv.refl left).append (WireEquiv.refl right)) wire = wire)
  · intro signature inherited
    simp [WireEquiv.append, WireEquiv.appendRenaming]
  · intro signature localWire
    simp [WireEquiv.append, WireEquiv.appendRenaming]

theorem WireEquiv.append_trans
    (firstLeft : WireEquiv sourceLeft middleLeft)
    (secondLeft : WireEquiv middleLeft targetLeft)
    (firstRight : WireEquiv sourceRight middleRight)
    (secondRight : WireEquiv middleRight targetRight) :
    (firstLeft.append firstRight).trans
        (secondLeft.append secondRight) =
      (firstLeft.trans secondLeft).append
        (firstRight.trans secondRight) := by
  apply WireEquiv.ext
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      ((firstLeft.append firstRight).trans
        (secondLeft.append secondRight)) wire =
      ((firstLeft.trans secondLeft).append
        (firstRight.trans secondRight)) wire)
  · intro signature inherited
    simp [WireEquiv.append, WireEquiv.appendRenaming, WireEquiv.trans,
      WireRenaming.comp]
  · intro signature localWire
    simp [WireEquiv.append, WireEquiv.appendRenaming, WireEquiv.trans,
      WireRenaming.comp]

mutual
  /-- Recursive region isomorphism under a typed ambient-wire equivalence. -/
  inductive RegionIso :
      {sourceOuter targetOuter : List Sig} →
      WireEquiv sourceOuter targetOuter →
      Region sourceOuter → Region targetOuter → Type
    | mk {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireEquiv sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        (locals : WireEquiv sourceLocals targetLocals)
        (items : ItemSeqIso (ambient.append locals) sourceItems targetItems) :
        RegionIso ambient (.mk sourceLocals sourceItems)
          (.mk targetLocals targetItems)

  inductive ItemIso :
      {sourceWires targetWires : List Sig} →
      WireEquiv sourceWires targetWires →
      Item sourceWires → Item targetWires → Type
    | atom {sourceWires targetWires arguments : List Sig}
        {ambient : WireEquiv sourceWires targetWires}
        {sourceHead : Var sourceWires (.rel arguments)}
        {targetHead : Var targetWires (.rel arguments)}
        {sourcePorts : Vars sourceWires arguments}
        {targetPorts : Vars targetWires arguments}
        (head_eq : ambient sourceHead = targetHead)
        (ports_eq : sourcePorts.map (fun wire => ambient wire) = targetPorts) :
        ItemIso ambient (.atom sourceHead sourcePorts)
          (.atom targetHead targetPorts)
    | identity {sourceWires targetWires : List Sig} {signature : Sig}
        {arity : Nat} {ambient : WireEquiv sourceWires targetWires}
        {sourcePorts : Fin arity → Var sourceWires signature}
        {targetPorts : Fin arity → Var targetWires signature}
        (positions : FiniteEquiv (Fin arity) (Fin arity))
        (ports_eq : ∀ sourceIndex,
          ambient (sourcePorts sourceIndex) =
            targetPorts (positions sourceIndex)) :
        ItemIso ambient (.identity signature arity sourcePorts)
          (.identity signature arity targetPorts)
    | term {sourceWires targetWires : List Sig} {freeArity : Nat}
        {ambient : WireEquiv sourceWires targetWires}
        {sourceOutput : Var sourceWires .iota}
        {targetOutput : Var targetWires .iota}
        {sourcePorts : Fin freeArity → Var sourceWires .iota}
        {targetPorts : Fin freeArity → Var targetWires .iota}
        {lambdaTerm : Lambda.Term 0 (Fin freeArity)}
        (output_eq : ambient sourceOutput = targetOutput)
        (ports_eq : ∀ slot,
          ambient (sourcePorts slot) = targetPorts slot) :
        ItemIso ambient
          (.term sourceOutput freeArity sourcePorts lambdaTerm)
          (.term targetOutput freeArity targetPorts lambdaTerm)
    | cut {sourceWires targetWires : List Sig}
        {ambient : WireEquiv sourceWires targetWires}
        {sourceBody : Region sourceWires}
        {targetBody : Region targetWires}
        (body : RegionIso ambient sourceBody targetBody) :
        ItemIso ambient (.cut sourceBody) (.cut targetBody)

  inductive ItemSeqIso :
      {sourceWires targetWires : List Sig} →
      WireEquiv sourceWires targetWires →
      ItemSeq sourceWires → ItemSeq targetWires → Type
    | permute {sourceWires targetWires : List Sig}
        {ambient : WireEquiv sourceWires targetWires}
        {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
        (positions : FiniteEquiv (Fin source.length) (Fin target.length))
        (items : ∀ (sourceIndex : Fin source.length)
          (targetIndex : Fin target.length),
          positions sourceIndex = targetIndex →
          ItemIso ambient (source.get sourceIndex) (target.get targetIndex)) :
        ItemSeqIso ambient source target
end

def ItemSeqIso.castAmbient
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    {first second : WireEquiv sourceWires targetWires}
    (equality : first = second) (iso : ItemSeqIso first source target) :
    ItemSeqIso second source target := by
  subst second
  exact iso

def RegionIso.castAmbient
    {source : Region sourceWires} {target : Region targetWires}
    {first second : WireEquiv sourceWires targetWires}
    (equality : first = second) (iso : RegionIso first source target) :
    RegionIso second source target := by
  subst second
  exact iso

private abbrev RegionIsoReflMotive
    (wires : List Sig) (region : Region wires) :=
  RegionIso (WireEquiv.refl wires) region region

private abbrev ItemIsoReflMotive
    (wires : List Sig) (item : Item wires) :=
  ItemIso (WireEquiv.refl wires) item item

private abbrev ItemsIsoReflMotive
    (wires : List Sig) (items : ItemSeq wires) :=
  ∀ index : Fin items.length,
    ItemIso (WireEquiv.refl wires) (items.get index) (items.get index)

private noncomputable def regionIsoReflMk
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (itemsIH : ItemsIsoReflMotive (outer ++ locals) items) :
    RegionIsoReflMotive outer (.mk locals items) :=
  .mk (WireEquiv.refl locals)
    ((ItemSeqIso.permute (FiniteEquiv.refl _)
      fun sourceIndex targetIndex equality => by
        subst targetIndex
        exact itemsIH sourceIndex).castAmbient
      (WireEquiv.append_refl outer locals).symm)

private noncomputable def itemIsoReflAtom
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    ItemIsoReflMotive wires (.atom head ports) :=
  .atom rfl (vars_map_id _)

private noncomputable def itemIsoReflIdentity
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    ItemIsoReflMotive wires (.identity signature arity ports) :=
  .identity (FiniteEquiv.refl _) fun _ => rfl

private noncomputable def itemIsoReflTerm
    (output : Var wires .iota) (freeArity : Nat)
    (ports : Fin freeArity → Var wires .iota)
    (term : Lambda.Term 0 (Fin freeArity)) :
    ItemIsoReflMotive wires (.term output freeArity ports term) :=
  .term rfl fun _ => rfl

private noncomputable def itemIsoReflCut
    (body : Region wires) (bodyIH : RegionIsoReflMotive wires body) :
    ItemIsoReflMotive wires (.cut body) :=
  .cut bodyIH

private noncomputable def itemsIsoReflNil :
    ItemsIsoReflMotive wires .nil := fun index => Fin.elim0 index

private noncomputable def itemsIsoReflCons
    (head : Item wires) (tail : ItemSeq wires)
    (headIH : ItemIsoReflMotive wires head)
    (tailIH : ItemsIsoReflMotive wires tail) :
    ItemsIsoReflMotive wires (.cons head tail) :=
  fun index => Fin.cases headIH tailIH index

noncomputable def RegionIso.refl (region : Region wires) :
    RegionIso (WireEquiv.refl wires) region region :=
  Region.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity itemIsoReflTerm
    itemIsoReflCut itemsIsoReflNil itemsIsoReflCons region

noncomputable def RegionIso.ofEq
    {before after : Region wires} (equality : before = after) :
    RegionIso (WireEquiv.refl wires) before after := by
  subst after
  exact RegionIso.refl before

noncomputable def RegionIso.localEquiv
    {sourceOuter targetOuter : List Sig}
    {before : Region sourceOuter} {after : Region targetOuter}
    {ambient : WireEquiv sourceOuter targetOuter}
    (presentation : RegionIso ambient before after) :
    WireEquiv before.locals after.locals :=
  match before, after, presentation with
  | .mk _ _, .mk _ _, .mk locals _ => locals

noncomputable def RegionIso.itemSeqIso
    {sourceOuter targetOuter : List Sig}
    {before : Region sourceOuter} {after : Region targetOuter}
    {ambient : WireEquiv sourceOuter targetOuter}
    (presentation : RegionIso ambient before after) :
    ItemSeqIso (ambient.append presentation.localEquiv)
      before.items after.items :=
  match before, after, presentation with
  | .mk _ _, .mk _ _, .mk _ items => items

noncomputable def ItemIso.refl (item : Item wires) :
    ItemIso (WireEquiv.refl wires) item item :=
  Item.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity itemIsoReflTerm
    itemIsoReflCut itemsIsoReflNil itemsIsoReflCons item

noncomputable def ItemSeqIso.refl (items : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires) items items :=
  .permute (FiniteEquiv.refl _) fun sourceIndex targetIndex equality => by
    subst targetIndex
    exact ItemSeq.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity itemIsoReflTerm
      itemIsoReflCut itemsIsoReflNil itemsIsoReflCons items sourceIndex

/-- Extend an item-sequence isomorphism by one corresponding leading item. -/
noncomputable def ItemSeqIso.cons
    {sourceHead : Item sourceWires} {targetHead : Item targetWires}
    {sourceTail : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
    {ambient : WireEquiv sourceWires targetWires}
    (head : ItemIso ambient sourceHead targetHead)
    (tail : ItemSeqIso ambient sourceTail targetTail) :
    ItemSeqIso ambient (.cons sourceHead sourceTail)
      (.cons targetHead targetTail) := by
  cases tail with
  | permute positions items =>
      refine .permute (FiniteEquiv.finSucc positions) (fun sourceIndex => ?_)
      change Fin (sourceTail.length + 1) at sourceIndex
      refine Fin.cases
        (fun targetIndex equality => ?_)
        (fun sourceRest targetIndex equality => ?_) sourceIndex
      · change Fin (targetTail.length + 1) at targetIndex
        have targetZero : targetIndex.val = 0 := by
          have values := congrArg Fin.val equality
          simp [FiniteEquiv.finSucc] at values
          exact values.symm
        subst targetIndex
        exact head
      · change Fin (targetTail.length + 1) at targetIndex
        revert equality
        refine Fin.cases (fun equality => ?_)
          (fun targetRest equality => ?_) targetIndex
        · have values := congrArg Fin.val equality
          simp [FiniteEquiv.finSucc] at values
        · apply items sourceRest targetRest
          apply Fin.ext
          have values := congrArg Fin.val equality
          simp [FiniteEquiv.finSucc] at values
          exact values

private noncomputable def ItemSeqIso.frameRefl
    (before : ItemSeq wires)
    {sourceItem targetItem : Item wires}
    (focus : ItemIso (WireEquiv.refl wires) sourceItem targetItem)
    (after : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires)
      (before.append (.cons sourceItem after))
      (before.append (.cons targetItem after)) := by
  cases before with
  | nil => exact ItemSeqIso.cons focus (ItemSeqIso.refl after)
  | cons head tail =>
      exact ItemSeqIso.cons (ItemIso.refl head)
        (ItemSeqIso.frameRefl tail focus after)

/-- Lift a region isomorphism through one exact recursive diagram context. -/
noncomputable def DiagramContext.fillIso
    (context : DiagramContext outer holeWires)
    {before after : Region holeWires}
    (body : RegionIso (WireEquiv.refl holeWires) before after) :
    RegionIso (WireEquiv.refl outer)
      (context.fill before) (context.fill after) := by
  induction context with
  | hole => exact body
  | @cut currentOuter currentHole locals leading trailing child induction =>
      exact .mk (WireEquiv.refl locals)
        ((ItemSeqIso.frameRefl leading (.cut (induction body))
          trailing).castAmbient
            (WireEquiv.append_refl currentOuter locals).symm)

private theorem Vars.map_commutes
    (variables : Vars wires signatures)
    (sourceRename : WireRenaming wires sourceTarget)
    (targetRename : WireRenaming wires targetTarget)
    (ambient : WireEquiv sourceTarget targetTarget)
    (commutes : ∀ {signature} (wire : Var wires signature),
      ambient (sourceRename wire) = targetRename wire) :
    (variables.map fun wire => ambient (sourceRename wire)) =
      variables.map fun wire => targetRename wire := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map]
      calc
        Vars.cons (ambient (sourceRename head))
            (tail.map fun wire => ambient (sourceRename wire)) =
            Vars.cons (targetRename head)
              (tail.map fun wire => ambient (sourceRename wire)) :=
          congrArg (fun mapped => Vars.cons mapped
            (tail.map fun wire => ambient (sourceRename wire)))
            (commutes head)
        _ = Vars.cons (targetRename head)
              (tail.map fun wire => targetRename wire) :=
          congrArg (Vars.cons (targetRename head)) induction

mutual
  /-- Isomorphic wire renamings of one region yield isomorphic renamed
  presentations. -/
  noncomputable def RegionIso.renameWires
      (region : Region wires)
      (sourceRename : WireRenaming wires sourceTarget)
      (targetRename : WireRenaming wires targetTarget)
      (ambient : WireEquiv sourceTarget targetTarget)
      (commutes : ∀ {signature} (wire : Var wires signature),
        ambient (sourceRename wire) = targetRename wire) :
      RegionIso ambient (region.renameWires sourceRename)
        (region.renameWires targetRename) :=
    match region with
    | .mk locals items =>
        let localEquiv := WireEquiv.refl locals
        let appendCommutes : ∀ {signature}
            (wire : Var (wires ++ locals) signature),
            (ambient.append localEquiv)
                (sourceRename.appendRight locals wire) =
              targetRename.appendRight locals wire := by
          intro signature wire
          apply Var.appendCases
            (motive := fun wire =>
              (ambient.append localEquiv)
                  (sourceRename.appendRight locals wire) =
                targetRename.appendRight locals wire)
          · intro inheritedSignature inherited
            simp [WireRenaming.appendRight, commutes]
          · intro localSignature localWire
            simp [WireRenaming.appendRight, localEquiv, WireEquiv.refl,
              WireRenaming.id]
        .mk localEquiv
          (ItemSeqIso.renameWires items
            (sourceRename.appendRight locals)
            (targetRename.appendRight locals)
            (ambient.append localEquiv) appendCommutes)

  /-- Isomorphic wire renamings of one item yield isomorphic renamed
  presentations. -/
  noncomputable def ItemIso.renameWires
      (item : Item wires)
      (sourceRename : WireRenaming wires sourceTarget)
      (targetRename : WireRenaming wires targetTarget)
      (ambient : WireEquiv sourceTarget targetTarget)
      (commutes : ∀ {signature} (wire : Var wires signature),
        ambient (sourceRename wire) = targetRename wire) :
      ItemIso ambient (item.renameWires sourceRename)
        (item.renameWires targetRename) :=
    match item with
    | .atom head ports =>
        .atom (commutes head)
          (by
            calc
              (ports.map fun wire => sourceRename wire).map
                    (fun wire => ambient wire) =
                  ports.map (fun wire => ambient (sourceRename wire)) :=
                vars_map_comp ports sourceRename ambient.toRenaming
              _ = ports.map fun wire => targetRename wire :=
                Vars.map_commutes ports sourceRename targetRename ambient
                  commutes)
    | .identity signature arity ports =>
        .identity (FiniteEquiv.refl _) (fun index => commutes (ports index))
    | .term output freeArity ports term =>
        .term (commutes output) (fun slot => commutes (ports slot))
    | .cut body =>
        .cut (RegionIso.renameWires body sourceRename targetRename
          ambient commutes)

  /-- Isomorphic wire renamings of one item sequence yield isomorphic renamed
  presentations. -/
  noncomputable def ItemSeqIso.renameWires
      (items : ItemSeq wires)
      (sourceRename : WireRenaming wires sourceTarget)
      (targetRename : WireRenaming wires targetTarget)
      (ambient : WireEquiv sourceTarget targetTarget)
      (commutes : ∀ {signature} (wire : Var wires signature),
        ambient (sourceRename wire) = targetRename wire) :
      ItemSeqIso ambient (items.renameWires sourceRename)
        (items.renameWires targetRename) :=
    match items with
    | .nil => .permute (FiniteEquiv.refl _) fun index => Fin.elim0 index
    | .cons head tail =>
        ItemSeqIso.cons
          (ItemIso.renameWires head sourceRename targetRename ambient commutes)
          (ItemSeqIso.renameWires tail sourceRename targetRename ambient commutes)
end

private def ItemSeq.appendSingletonPositions
    (items : ItemSeq wires) (item : Item wires) :
    FiniteEquiv (Fin (items.append (.cons item .nil)).length)
      (Fin (ItemSeq.cons item items).length) where
  toFun position :=
    if beforeLast : position.val < items.length then
      ⟨position.val + 1, by simp only [ItemSeq.length]; omega⟩
    else
      ⟨0, by simp [ItemSeq.length]⟩
  invFun position :=
    if first : position.val = 0 then
      ⟨items.length, by simp [ItemSeq.length]⟩
    else
      ⟨position.val - 1, by
        have bound := position.isLt
        simp only [ItemSeq.length] at bound
        simp only [ItemSeq.length_append, ItemSeq.length, Nat.add_zero]
        omega⟩
  left_inv := by
    intro position
    apply Fin.ext
    dsimp
    have sourceLength :
        (items.append (.cons item .nil)).length = items.length + 1 := by
      simp [ItemSeq.length]
    have targetLength :
        (ItemSeq.cons item items).length = items.length + 1 := rfl
    have bound : position.val < items.length + 1 := by
      simpa only [ItemSeq.length_append, ItemSeq.length, Nat.add_zero]
        using position.isLt
    split <;> split <;>
      simp_all only [Fin.val_mk, ItemSeq.length_append, ItemSeq.length,
        Nat.add_zero] <;> omega
  right_inv := by
    intro position
    refine Fin.cases ?_ (fun rest => ?_) position
    · apply Fin.ext
      simp only [Fin.val_zero]
      dsimp
      split <;> rename_i beforeLast
      · omega
      · rfl
    · apply Fin.ext
      dsimp
      split <;> rename_i beforeLast <;> simp only [Fin.val_mk]
      all_goals have bound := rest.isLt; omega

private theorem ItemSeq.get_append_left
    (items suffix : ItemSeq wires) (position : Fin items.length) :
    (items.append suffix).get
      ⟨position.val, by rw [ItemSeq.length_append]; omega⟩ =
        items.get position :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ items => ∀ (suffix : ItemSeq _)
      (position : Fin items.length),
      (items.append suffix).get
        ⟨position.val, by rw [ItemSeq.length_append]; omega⟩ =
          items.get position)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ position => Fin.elim0 position)
    (fun _ _ _ induction suffix position =>
      Fin.cases rfl (induction suffix) position)
    items suffix position

private theorem ItemSeq.get_append_right
    (initial items : ItemSeq wires) (position : Fin items.length) :
    (initial.append items).get
      ⟨initial.length + position.val, by
        rw [ItemSeq.length_append]
        omega⟩ = items.get position :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ initial => ∀ (items : ItemSeq _)
      (position : Fin items.length),
      (initial.append items).get
        ⟨initial.length + position.val, by
          rw [ItemSeq.length_append]
          omega⟩ = items.get position)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun items position => by
      have indexEq :
          (⟨ItemSeq.nil.length + position.val, by
            rw [ItemSeq.length_append]
            omega⟩ : Fin (ItemSeq.nil.append items).length) = position :=
        Fin.ext (by simp [ItemSeq.length])
      rw [indexEq]
      rfl)
    (fun head tail _ induction items position => by
      let inner : Fin (tail.append items).length :=
        ⟨tail.length + position.val, by
            rw [ItemSeq.length_append]
            omega⟩
      have indexEq :
          (⟨(ItemSeq.cons head tail).length + position.val, by
            rw [ItemSeq.length_append]
            omega⟩ : Fin ((ItemSeq.cons head tail).append items).length) =
            inner.succ := by
        apply Fin.ext
        simp only [ItemSeq.length, Fin.val_succ, inner]
        omega
      rw [indexEq]
      exact induction items position)
    initial items position

/-- Append independently isomorphic item-sequence blocks. -/
noncomputable def ItemSeqIso.append
    {sourceFirst sourceSecond : ItemSeq sourceWires}
    {targetFirst targetSecond : ItemSeq targetWires}
    {ambient : WireEquiv sourceWires targetWires}
    (first : ItemSeqIso ambient sourceFirst targetFirst)
    (second : ItemSeqIso ambient sourceSecond targetSecond) :
    ItemSeqIso ambient (sourceFirst.append sourceSecond)
      (targetFirst.append targetSecond) := by
  cases first with
  | permute firstPositions firstItems =>
      cases second with
      | permute secondPositions secondItems =>
          let sourceLengthEq := ItemSeq.length_append sourceFirst sourceSecond
          let targetLengthEq := ItemSeq.length_append targetFirst targetSecond
          let positions :=
            (FiniteEquiv.finCast sourceLengthEq).trans
              ((FiniteEquiv.finAppend firstPositions secondPositions).trans
                (FiniteEquiv.finCast targetLengthEq.symm))
          refine .permute positions (fun sourceIndex targetIndex equality => ?_)
          subst targetIndex
          let sumPosition : Fin (sourceFirst.length + sourceSecond.length) :=
            Fin.cast sourceLengthEq sourceIndex
          apply Fin.addCases (i := sumPosition)
            (motive := fun sumPosition =>
              Fin.cast sourceLengthEq sourceIndex = sumPosition →
                ItemIso ambient
                  ((sourceFirst.append sourceSecond).get sourceIndex)
                  ((targetFirst.append targetSecond).get
                    (positions sourceIndex)))
          · intro sourcePosition sumEq
            let targetPosition := firstPositions sourcePosition
            have sourceValue : sourceIndex.val = sourcePosition.val := by
              have values := congrArg Fin.val sumEq
              simpa [sumPosition] using values
            have targetValue : (positions sourceIndex).val =
                targetPosition.val := by
              simp [positions, sourceLengthEq, targetLengthEq, sumPosition,
                FiniteEquiv.trans, FiniteEquiv.finCast,
                FiniteEquiv.finAppend, sumEq, targetPosition]
            have sourceEq : sourceIndex =
                ⟨sourcePosition.val, by
                  rw [ItemSeq.length_append]
                  omega⟩ := Fin.ext sourceValue
            have targetEq : positions sourceIndex =
                ⟨targetPosition.val, by
                  rw [ItemSeq.length_append]
                  omega⟩ := Fin.ext targetValue
            have sourceGet :
                (sourceFirst.append sourceSecond).get sourceIndex =
                  sourceFirst.get sourcePosition := by
              rw [sourceEq]
              exact ItemSeq.get_append_left _ _ sourcePosition
            have targetGet :
                (targetFirst.append targetSecond).get
                    (positions sourceIndex) =
                  targetFirst.get targetPosition := by
              rw [targetEq]
              exact ItemSeq.get_append_left _ _ targetPosition
            rw [sourceGet, targetGet]
            exact firstItems sourcePosition targetPosition rfl
          · intro sourcePosition sumEq
            let targetPosition := secondPositions sourcePosition
            have sourceValue : sourceIndex.val =
                sourceFirst.length + sourcePosition.val := by
              have values := congrArg Fin.val sumEq
              simpa [sumPosition] using values
            have targetValue : (positions sourceIndex).val =
                targetFirst.length + targetPosition.val := by
              simp [positions, sourceLengthEq, targetLengthEq, sumPosition,
                FiniteEquiv.trans, FiniteEquiv.finCast,
                FiniteEquiv.finAppend, sumEq, targetPosition]
            have sourceEq : sourceIndex =
                ⟨sourceFirst.length + sourcePosition.val, by
                  rw [ItemSeq.length_append]
                  omega⟩ := Fin.ext sourceValue
            have targetEq : positions sourceIndex =
                ⟨targetFirst.length + targetPosition.val, by
                  rw [ItemSeq.length_append]
                  omega⟩ := Fin.ext targetValue
            have sourceGet :
                (sourceFirst.append sourceSecond).get sourceIndex =
                  sourceSecond.get sourcePosition := by
              rw [sourceEq]
              exact ItemSeq.get_append_right _ _ sourcePosition
            have targetGet :
                (targetFirst.append targetSecond).get
                    (positions sourceIndex) =
                  targetSecond.get targetPosition := by
              rw [targetEq]
              exact ItemSeq.get_append_right _ _ targetPosition
            rw [sourceGet, targetGet]
            exact secondItems sourcePosition targetPosition rfl
          · rfl

/-- Exchange two adjacent item-sequence blocks. -/
noncomputable def ItemSeqIso.swapAppend
    (left right : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires)
      (left.append right) (right.append left) := by
  let sourceLengthEq := ItemSeq.length_append left right
  let targetLengthEq := ItemSeq.length_append right left
  let positions :=
    (FiniteEquiv.finCast sourceLengthEq).trans
      ((FiniteEquiv.finSwap left.length right.length).trans
        (FiniteEquiv.finCast targetLengthEq.symm))
  refine .permute positions (fun sourceIndex targetIndex equality => ?_)
  subst targetIndex
  let sumPosition : Fin (left.length + right.length) :=
    Fin.cast sourceLengthEq sourceIndex
  apply Fin.addCases (i := sumPosition)
    (motive := fun sumPosition =>
      Fin.cast sourceLengthEq sourceIndex = sumPosition →
        ItemIso (WireEquiv.refl wires)
          ((left.append right).get sourceIndex)
          ((right.append left).get (positions sourceIndex)))
  · intro position sumEq
    have sourceValue : sourceIndex.val = position.val := by
      have values := congrArg Fin.val sumEq
      simpa [sumPosition] using values
    have targetValue : (positions sourceIndex).val =
        right.length + position.val := by
      simp [positions, sourceLengthEq, targetLengthEq, sumPosition,
        FiniteEquiv.trans, FiniteEquiv.finCast, FiniteEquiv.finSwap,
        sumEq]
    have sourceEq : sourceIndex =
        ⟨position.val, by rw [ItemSeq.length_append]; omega⟩ :=
      Fin.ext sourceValue
    have targetEq : positions sourceIndex =
        ⟨right.length + position.val, by
          rw [ItemSeq.length_append]
          omega⟩ := Fin.ext targetValue
    have sourceGet : (left.append right).get sourceIndex =
        left.get position := by
      rw [sourceEq]
      exact ItemSeq.get_append_left _ _ position
    have targetGet : (right.append left).get (positions sourceIndex) =
        left.get position := by
      rw [targetEq]
      exact ItemSeq.get_append_right _ _ position
    rw [sourceGet, targetGet]
    exact ItemIso.refl (left.get position)
  · intro position sumEq
    have sourceValue : sourceIndex.val = left.length + position.val := by
      have values := congrArg Fin.val sumEq
      simpa [sumPosition] using values
    have targetValue : (positions sourceIndex).val = position.val := by
      simp [positions, sourceLengthEq, targetLengthEq, sumPosition,
        FiniteEquiv.trans, FiniteEquiv.finCast, FiniteEquiv.finSwap,
        sumEq]
    have sourceEq : sourceIndex =
        ⟨left.length + position.val, by
          rw [ItemSeq.length_append]
          omega⟩ := Fin.ext sourceValue
    have targetEq : positions sourceIndex =
        ⟨position.val, by rw [ItemSeq.length_append]; omega⟩ :=
      Fin.ext targetValue
    have sourceGet : (left.append right).get sourceIndex =
        right.get position := by
      rw [sourceEq]
      exact ItemSeq.get_append_right _ _ position
    have targetGet : (right.append left).get (positions sourceIndex) =
        right.get position := by
      rw [targetEq]
      exact ItemSeq.get_append_left _ _ position
    rw [sourceGet, targetGet]
    exact ItemIso.refl (right.get position)
  · rfl

private theorem ItemSeq.get_append_singleton_last
    (items : ItemSeq wires) (item : Item wires) :
    (items.append (.cons item .nil)).get
      ⟨items.length, by rw [ItemSeq.length_append]; simp [ItemSeq.length]⟩ =
        item :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun _ items => ∀ item,
      (items.append (.cons item .nil)).get
        ⟨items.length, by
          rw [ItemSeq.length_append]
          simp [ItemSeq.length]⟩ = item)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ => rfl)
    (fun _ _ _ induction item => induction item)
    items item

/-- Item permutation witnessing that appending one item and placing it first
are the same presentation. -/
noncomputable def ItemSeqIso.appendSingletonFront
    (items : ItemSeq wires) (item : Item wires) :
    ItemSeqIso (WireEquiv.refl wires)
      (items.append (.cons item .nil)) (.cons item items) := by
  let positions := ItemSeq.appendSingletonPositions items item
  refine .permute positions (fun sourceIndex targetIndex equal => ?_)
  subst targetIndex
  by_cases beforeLast : sourceIndex.val < items.length
  · let original : Fin items.length := ⟨sourceIndex.val, beforeLast⟩
    have sourceEq : sourceIndex =
        (⟨original.val, by
          simp only [ItemSeq.length_append, ItemSeq.length, Nat.add_zero]
          omega⟩ :
          Fin (items.append (.cons item .nil)).length) := Fin.ext rfl
    rw [sourceEq]
    simp only [positions, ItemSeq.appendSingletonPositions, original.isLt,
      dite_true, ItemSeq.get]
    rw [ItemSeq.get_append_left]
    exact ItemIso.refl (items.get original)
  · have last : sourceIndex.val = items.length := by
      have bound := sourceIndex.isLt
      simp only [ItemSeq.length_append, ItemSeq.length] at bound
      omega
    have sourceEq : sourceIndex =
        (⟨items.length, by
          simp [ItemSeq.length]⟩ :
          Fin (items.append (.cons item .nil)).length) := Fin.ext last
    rw [sourceEq]
    simp only [positions, ItemSeq.appendSingletonPositions, Nat.lt_irrefl, dite_false,
      ItemSeq.get]
    rw [ItemSeq.get_append_singleton_last]
    exact ItemIso.refl item

/-- Region presentation isomorphism moving one appended item to the front. -/
noncomputable def RegionIso.appendSingletonFront
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (item : Item (outer ++ locals)) :
    RegionIso (WireEquiv.refl outer)
      (.mk locals (items.append (.cons item .nil)))
      (.mk locals (.cons item items)) :=
  .mk (WireEquiv.refl locals)
    ((ItemSeqIso.appendSingletonFront items item).castAmbient
      (WireEquiv.append_refl outer locals).symm)

theorem Vars.map_equiv_left_inv
    (equivalence : WireEquiv source target)
    (variables : Vars source signatures) :
    (variables.map (fun wire => equivalence wire)).map
        (fun wire => equivalence.symm wire) = variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map]
      have headEq :
          equivalence.symm.toRenaming (equivalence.toRenaming head) = head :=
        equivalence.left_inv head
      rw [headEq, induction]

mutual
  noncomputable def RegionIso.symm
      {source : Region sourceWires} {target : Region targetWires}
      {ambient : WireEquiv sourceWires targetWires}
      (iso : RegionIso ambient source target) :
      RegionIso ambient.symm target source :=
    match iso with
    | .mk locals items => .mk locals.symm items.symm

  noncomputable def ItemIso.symm
      {source : Item sourceWires} {target : Item targetWires}
      {ambient : WireEquiv sourceWires targetWires}
      (iso : ItemIso ambient source target) :
      ItemIso ambient.symm target source :=
    match iso with
    | @ItemIso.atom _ _ _ _ sourceHead targetHead sourcePorts targetPorts
        head_eq ports_eq => .atom (by
        rw [← head_eq]
        exact ambient.left_inv _)
        (by
          rw [← ports_eq]
          exact Vars.map_equiv_left_inv ambient sourcePorts)
    | @ItemIso.identity _ _ _ _ _ sourcePorts targetPorts positions
          ports_eq =>
        .identity positions.symm (by
          intro targetIndex
          let sourceIndex := positions.symm targetIndex
          change ambient.symm (targetPorts targetIndex) =
            sourcePorts sourceIndex
          rw [← positions.apply_symm_apply targetIndex,
            ← ports_eq sourceIndex]
          exact ambient.left_inv _)
    | @ItemIso.term _ _ _ _ sourceOutput targetOutput sourcePorts targetPorts
          lambdaTerm output_eq ports_eq =>
        .term (by
          rw [← output_eq]
          exact ambient.left_inv _)
          (by
            intro slot
            rw [← ports_eq slot]
            exact ambient.left_inv _)
    | .cut body => .cut body.symm

  noncomputable def ItemSeqIso.symm
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {ambient : WireEquiv sourceWires targetWires}
      (iso : ItemSeqIso ambient source target) :
      ItemSeqIso ambient.symm target source :=
    match iso with
    | .permute positions items =>
        .permute positions.symm fun targetIndex sourceIndex equality =>
          (items sourceIndex targetIndex (by
            rw [← equality]
            exact positions.right_inv targetIndex)).symm
end

mutual
  noncomputable def RegionIso.trans
      {source : Region sourceWires} {middle : Region middleWires}
      {target : Region targetWires}
      {firstAmbient : WireEquiv sourceWires middleWires}
      {secondAmbient : WireEquiv middleWires targetWires}
      (first : RegionIso firstAmbient source middle)
      (second : RegionIso secondAmbient middle target) :
      RegionIso (firstAmbient.trans secondAmbient) source target :=
    match first, second with
    | .mk firstLocals firstItems, .mk secondLocals secondItems =>
        .mk (firstLocals.trans secondLocals)
          ((firstItems.trans secondItems).castAmbient
            (WireEquiv.append_trans firstAmbient secondAmbient
              firstLocals secondLocals))

  noncomputable def ItemIso.trans
      {source : Item sourceWires} {middle : Item middleWires}
      {target : Item targetWires}
      {firstAmbient : WireEquiv sourceWires middleWires}
      {secondAmbient : WireEquiv middleWires targetWires}
      (first : ItemIso firstAmbient source middle)
      (second : ItemIso secondAmbient middle target) :
      ItemIso (firstAmbient.trans secondAmbient) source target :=
    match first, second with
    | @ItemIso.atom _ _ _ _ sourceHead middleHead sourcePorts middlePorts
          firstHead firstPorts,
        @ItemIso.atom _ _ _ _ _ targetHead _ targetPorts
          secondHead secondPorts =>
        .atom (by
          change secondAmbient (firstAmbient sourceHead) = targetHead
          rw [firstHead, secondHead])
          (by
            calc
              sourcePorts.map
                  (fun wire => (firstAmbient.trans secondAmbient) wire) =
                  (sourcePorts.map (fun wire => firstAmbient wire)).map
                    (fun wire => secondAmbient wire) :=
                (vars_map_comp sourcePorts firstAmbient.toRenaming
                  secondAmbient.toRenaming).symm
              _ = middlePorts.map (fun wire => secondAmbient wire) := by
                rw [firstPorts]
              _ = targetPorts := secondPorts)
    | @ItemIso.identity _ _ _ _ _ sourcePorts middlePorts firstPositions
          firstPorts,
        @ItemIso.identity _ _ _ _ _ _ targetPorts secondPositions
          secondPorts =>
      .identity (firstPositions.trans secondPositions) (by
        intro sourceIndex
        change secondAmbient (firstAmbient (sourcePorts sourceIndex)) =
          targetPorts (secondPositions (firstPositions sourceIndex))
        rw [firstPorts sourceIndex,
          secondPorts (firstPositions sourceIndex)])
    | @ItemIso.term _ _ _ _ sourceOutput middleOutput sourcePorts middlePorts
          lambdaTerm firstOutput firstPorts,
        @ItemIso.term _ _ _ _ _ targetOutput _ targetPorts _
          secondOutput secondPorts =>
      .term (by
        change secondAmbient (firstAmbient sourceOutput) = targetOutput
        rw [firstOutput, secondOutput])
        (by
          intro slot
          change secondAmbient (firstAmbient (sourcePorts slot)) =
            targetPorts slot
          rw [firstPorts slot, secondPorts slot])
    | .cut firstBody, .cut secondBody => .cut (firstBody.trans secondBody)

  noncomputable def ItemSeqIso.trans
      {source : ItemSeq sourceWires} {middle : ItemSeq middleWires}
      {target : ItemSeq targetWires}
      {firstAmbient : WireEquiv sourceWires middleWires}
      {secondAmbient : WireEquiv middleWires targetWires}
      (first : ItemSeqIso firstAmbient source middle)
      (second : ItemSeqIso secondAmbient middle target) :
      ItemSeqIso (firstAmbient.trans secondAmbient) source target :=
    match first, second with
    | .permute firstPositions firstItems,
        .permute secondPositions secondItems =>
        .permute (firstPositions.trans secondPositions)
          fun sourceIndex targetIndex equality =>
            let middleIndex := firstPositions sourceIndex
            (firstItems sourceIndex middleIndex rfl).trans
              (secondItems middleIndex targetIndex (by simpa using equality))
end

end VisualProof.Diagram
