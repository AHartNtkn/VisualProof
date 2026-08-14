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
        (ports_eq : (fun index => ambient (sourcePorts index)) = targetPorts) :
        ItemIso ambient (.identity signature arity sourcePorts)
          (.identity signature arity targetPorts)
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
  .identity rfl

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
  Region.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity
    itemIsoReflCut itemsIsoReflNil itemsIsoReflCons region

noncomputable def ItemIso.refl (item : Item wires) :
    ItemIso (WireEquiv.refl wires) item item :=
  Item.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity
    itemIsoReflCut itemsIsoReflNil itemsIsoReflCons item

noncomputable def ItemSeqIso.refl (items : ItemSeq wires) :
    ItemSeqIso (WireEquiv.refl wires) items items :=
  .permute (FiniteEquiv.refl _) fun sourceIndex targetIndex equality => by
    subst targetIndex
    exact ItemSeq.rec regionIsoReflMk itemIsoReflAtom itemIsoReflIdentity
      itemIsoReflCut itemsIsoReflNil itemsIsoReflCons items sourceIndex

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
    | @ItemIso.identity _ _ _ _ _ _ _ ports_eq => .identity (by
        funext index
        rw [← congrFun ports_eq index]
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
    | @ItemIso.identity _ _ _ _ _ sourcePorts middlePorts firstPorts,
        @ItemIso.identity _ _ _ _ _ _ targetPorts secondPorts =>
      .identity (by
        funext index
        change secondAmbient (firstAmbient (sourcePorts index)) =
          targetPorts index
        rw [congrFun firstPorts index, congrFun secondPorts index])
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
