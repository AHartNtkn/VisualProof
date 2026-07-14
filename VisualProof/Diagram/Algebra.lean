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
def conjoin : Region signature wires rels → Region signature wires rels →
    Region signature wires rels
  | .mk firstLocal firstItems, .mk secondLocal secondItems =>
      .mk (firstLocal + secondLocal)
        ((firstItems.renameWires
            (conjoinLeftWire wires firstLocal secondLocal)).append
          (secondItems.renameWires
            (conjoinRightWire wires firstLocal secondLocal)))

def blank : Region signature wires rels := .mk 0 .nil

end Region

@[simp] theorem Region.conjoin_localWires
    (firstItems : ItemSeq signature (wires + firstLocal) rels)
    (secondItems : ItemSeq signature (wires + secondLocal) rels) :
    Region.conjoin (.mk firstLocal firstItems) (.mk secondLocal secondItems) =
      .mk (firstLocal + secondLocal)
        ((firstItems.renameWires
            (Region.conjoinLeftWire wires firstLocal secondLocal)).append
          (secondItems.renameWires
            (Region.conjoinRightWire wires firstLocal secondLocal))) := rfl

private theorem extendWireEnv_conjoinLeft
    (outerEnv : Fin outer → D)
    (localEnv : Fin (firstLocal + secondLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.conjoinLeftWire outer firstLocal secondLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.castAdd secondLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinLeftWire, extendWireEnv]
  · simp [Region.conjoinLeftWire, extendWireEnv]

private theorem extendWireEnv_conjoinRight
    (outerEnv : Fin outer → D)
    (localEnv : Fin (firstLocal + secondLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.conjoinRightWire outer firstLocal secondLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.natAdd firstLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [Region.conjoinRightWire, extendWireEnv]
  · simp [Region.conjoinRightWire, extendWireEnv]

private theorem extendWireEnv_rename
    (rho : Fin source → Fin target)
    (outerEnv : Fin target → D) (localEnv : Fin localWires → D) :
    extendWireEnv outerEnv localEnv ∘ extendWireRenaming rho localWires =
      extendWireEnv (outerEnv ∘ rho) localEnv := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp [extendWireRenaming, extendWireEnv, Function.comp_def]
  · simp [extendWireRenaming, extendWireEnv, Function.comp_def]

mutual
  theorem denoteRegion_renameWires
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (region : Region signature source relCtx) :
      denoteRegion model named env rels (region.renameWires rho) ↔
        denoteRegion model named (env ∘ rho) rels region := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameWires, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, hitems⟩
          refine ⟨localEnv, ?_⟩
          have hrenamed := (denoteItemSeq_renameWires model named
            (extendWireRenaming rho localWires)
            (extendWireEnv env localEnv) rels items).1 hitems
          rw [extendWireEnv_rename] at hrenamed
          exact hrenamed
        · rintro ⟨localEnv, hitems⟩
          refine ⟨localEnv, ?_⟩
          apply (denoteItemSeq_renameWires model named
            (extendWireRenaming rho localWires)
            (extendWireEnv env localEnv) rels items).2
          rw [extendWireEnv_rename]
          exact hitems

  theorem denoteItem_renameWires
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (item : Item signature source relCtx) :
      denoteItem model named env rels (item.renameWires rho) ↔
        denoteItem model named (env ∘ rho) rels item := by
    cases item with
    | equation output term =>
        simp only [Item.renameWires, denoteItem_equation,
          Function.comp_apply]
        rw [model.eval_mapFree]
    | atom relation arguments =>
        simp [Item.renameWires, denoteItem_atom, Function.comp_def]
    | named relation arguments =>
        simp [Item.renameWires, denoteItem_named, Function.comp_def]
    | cut body =>
        simp only [Item.renameWires, cut_denotes_negation]
        rw [denoteRegion_renameWires]
    | bubble arity body =>
        simp only [Item.renameWires, bubble_denotes_exists]
        constructor
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameWires (relCtx := arity :: relCtx)
              model named rho env
              (relation, rels) body).1 hbody⟩
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameWires (relCtx := arity :: relCtx)
              model named rho env
              (relation, rels) body).2 hbody⟩

  theorem denoteItemSeq_renameWires
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : Fin source → Fin target)
      (env : Fin target → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (items : ItemSeq signature source relCtx) :
      denoteItemSeq model named env rels (items.renameWires rho) ↔
        denoteItemSeq model named (env ∘ rho) rels items := by
    cases items with
    | nil => constructor <;> intro <;> trivial
    | cons item tail =>
        simp only [ItemSeq.renameWires, denoteItemSeq_cons]
        rw [denoteItem_renameWires, denoteItemSeq_renameWires]
end

theorem Region.denote_conjoin
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (first second : Region signature wires relCtx) :
    denoteRegion model named env rels (first.conjoin second) ↔
      denoteRegion model named env rels first ∧
        denoteRegion model named env rels second := by
  cases first with
  | mk firstLocal firstItems =>
      cases second with
      | mk secondLocal secondItems =>
          simp only [Region.conjoin, denoteRegion_mk]
          constructor
          · rintro ⟨localEnv, hitems⟩
            rw [denoteItemSeq_append] at hitems
            rcases hitems with ⟨hfirst, hsecond⟩
            constructor
            · refine ⟨fun wire => localEnv (Fin.castAdd secondLocal wire), ?_⟩
              rw [← extendWireEnv_conjoinLeft env localEnv]
              exact (denoteItemSeq_renameWires model named
                (Region.conjoinLeftWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels firstItems).1 hfirst
            · refine ⟨fun wire => localEnv (Fin.natAdd firstLocal wire), ?_⟩
              rw [← extendWireEnv_conjoinRight env localEnv]
              exact (denoteItemSeq_renameWires model named
                (Region.conjoinRightWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels secondItems).1 hsecond
          · rintro ⟨⟨firstEnv, hfirst⟩, ⟨secondEnv, hsecond⟩⟩
            let localEnv : Fin (firstLocal + secondLocal) → model.Carrier :=
              Fin.addCases firstEnv secondEnv
            refine ⟨localEnv, (denoteItemSeq_append model named
              (extendWireEnv env localEnv) rels _ _).2 ⟨?_, ?_⟩⟩
            · apply (denoteItemSeq_renameWires model named
                (Region.conjoinLeftWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels firstItems).2
              have henv : extendWireEnv env localEnv ∘
                    Region.conjoinLeftWire wires firstLocal secondLocal =
                  extendWireEnv env firstEnv := by
                rw [extendWireEnv_conjoinLeft]
                funext wire
                simp [localEnv]
              rw [henv]
              exact hfirst
            · apply (denoteItemSeq_renameWires model named
                (Region.conjoinRightWire wires firstLocal secondLocal)
                (extendWireEnv env localEnv) rels secondItems).2
              have henv : extendWireEnv env localEnv ∘
                    Region.conjoinRightWire wires firstLocal secondLocal =
                  extendWireEnv env secondEnv := by
                rw [extendWireEnv_conjoinRight]
                funext wire
                simp [localEnv]
              rw [henv]
              exact hsecond

@[simp] theorem Region.denote_blank
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (rels : RelEnv model.Carrier relCtx) :
    denoteRegion model named env rels (Region.blank : Region signature wires relCtx) := by
  exact ⟨Fin.elim0, trivial⟩

theorem DiagramContext.fill_conjoin_left_even
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model named env rels (ctx.fill (first.conjoin second)) →
      denoteRegion model named env rels (ctx.fill first) := by
  apply context_mono model named env rels hEven
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model named holeEnv holeRels first second).1
    hconjoin |>.1

theorem DiagramContext.fill_conjoin_right_even
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model named env rels (ctx.fill (first.conjoin second)) →
      denoteRegion model named env rels (ctx.fill second) := by
  apply context_mono model named env rels hEven
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model named holeEnv holeRels first second).1
    hconjoin |>.2

theorem DiagramContext.fill_conjoin_left_odd
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model named env rels (ctx.fill first) →
      denoteRegion model named env rels (ctx.fill (first.conjoin second)) := by
  apply context_anti model named env rels hOdd
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model named holeEnv holeRels first second).1
    hconjoin |>.1

theorem DiagramContext.fill_conjoin_right_odd
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model named env rels (ctx.fill second) →
      denoteRegion model named env rels (ctx.fill (first.conjoin second)) := by
  apply context_anti model named env rels hOdd
  intro holeEnv holeRels hconjoin
  exact (Region.denote_conjoin model named holeEnv holeRels first second).1
    hconjoin |>.2

theorem ItemSeq.renameWires_append
    : (first second : ItemSeq signature source rels) →
    (rho : Fin source → Fin target) →
    (first.append second).renameWires rho =
      (first.renameWires rho).append (second.renameWires rho)
  | .nil, _, _ => rfl
  | .cons item tail, second, rho =>
      congrArg (ItemSeq.cons (item.renameWires rho))
        (ItemSeq.renameWires_append tail second rho)

theorem ItemSeq.renameRelations_append
    : (first second : ItemSeq signature wires source) →
    (rho : RelationRenaming source target) →
    (first.append second).renameRelations rho =
      (first.renameRelations rho).append (second.renameRelations rho)
  | .nil, _, _ => rfl
  | .cons item tail, second, rho =>
      congrArg (ItemSeq.cons (item.renameRelations rho))
        (ItemSeq.renameRelations_append tail second rho)

@[simp] theorem ItemSeq.renameWires_length :
    (items : ItemSeq signature source rels) →
    (rho : Fin source → Fin target) →
    (items.renameWires rho).length = items.length
  | .nil, _ => rfl
  | .cons _ tail, rho =>
      congrArg Nat.succ (ItemSeq.renameWires_length tail rho)

/-- Renaming wires preserves the finite carrier of item positions. -/
def ItemSeq.renameWiresPositionEquiv
    (items : ItemSeq signature source rels)
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
    (first second : ItemSeq signature wires rels) →
    (first.append second).length = first.length + second.length
  | .nil, second => (Nat.zero_add second.length).symm
  | .cons _ tail, second => by
      simpa [ItemSeq.append, ItemSeq.length, Nat.succ_add] using
        congrArg Nat.succ (ItemSeq.length_append tail second)

def ItemSeq.appendRenamePositionSwap
    (first second : ItemSeq signature source rels)
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
    (first second : ItemSeq signature wires rels) →
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
    (first second : ItemSeq signature wires rels) →
    (index : Fin second.length) →
    (first.append second).get
        (Fin.cast (ItemSeq.length_append first second).symm
          (Fin.natAdd first.length index)) =
      second.get index
  | .nil, second, index => by
      have hindex :
          Fin.cast (ItemSeq.length_append (.nil : ItemSeq signature wires rels)
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
    (items : ItemSeq signature source rels) →
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
      (region : Region signature wires source)
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
      (item : Item signature wires source)
      (wire : Fin wires → Fin targetWires)
      (relation : RelationRenaming source target) :
      (item.renameWires wire).renameRelations relation =
        (item.renameRelations relation).renameWires wire := by
    cases item with
    | equation output term => rfl
    | atom rel arguments => rfl
    | named rel arguments => rfl
    | cut body =>
        exact congrArg Item.cut
          (Region.renameWires_renameRelations body wire relation)
    | bubble arity body =>
        exact congrArg (Item.bubble arity)
          (Region.renameWires_renameRelations body wire
            (RelationRenaming.lift relation arity))

  theorem ItemSeq.renameWires_renameRelations
      (items : ItemSeq signature wires source)
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
    (first second : Region signature source rels)
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
    (first second : Region signature wires source)
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

theorem RegionIso.renameWiresEquiv
    (region : Region signature source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    RegionIso signature wire rels region (region.renameWires wire) := by
  apply Region.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso signature wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso signature wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso signature wire rels (items.get index)
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
  · intro source rels output term target wire
    exact ItemIso.equation rfl rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.named relation rfl
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

theorem ItemSeqIso.renameWiresEquiv
    (items : ItemSeq signature source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemSeqIso signature wire rels items (items.renameWires wire) := by
  refine ItemSeqIso.permute (items.renameWiresPositionEquiv wire) ?_
  apply ItemSeq.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso signature wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso signature wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso signature wire rels (items.get index)
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
  · intro source rels output term target wire
    exact ItemIso.equation rfl rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.named relation rfl
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

theorem ItemIso.renameWiresEquiv
    (item : Item signature source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemIso signature wire rels item (item.renameWires wire) := by
  apply Item.rec
    (motive_1 := fun source rels region =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        RegionIso signature wire rels region (region.renameWires wire))
    (motive_2 := fun source rels item =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ItemIso signature wire rels item (item.renameWires wire))
    (motive_3 := fun source rels items =>
      ∀ {target}, (wire : FiniteEquiv (Fin source) (Fin target)) →
        ∀ index, ItemIso signature wire rels (items.get index)
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
  · intro source rels output term target wire
    exact ItemIso.equation rfl rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.atom relation rfl
  · intro source rels arity relation arguments target wire
    exact ItemIso.named relation rfl
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

theorem ItemSeqIso.appendCommRename
    (first second : ItemSeq signature source rels)
    (wire : FiniteEquiv (Fin source) (Fin target)) :
    ItemSeqIso signature wire rels (first.append second)
      ((second.renameWires wire).append (first.renameWires wire)) := by
  refine ItemSeqIso.permute (first.appendRenamePositionSwap second wire) ?_
  intro index
  let sumIndex : Fin (first.length + second.length) :=
    Fin.cast (ItemSeq.length_append first second) index
  refine Fin.addCases (motive := fun splitIndex =>
      sumIndex = splitIndex →
        ItemIso signature wire rels ((first.append second).get index)
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

theorem RegionIso.conjoin_blank_left
    (region : Region signature wires rels) :
    RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
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

theorem RegionIso.conjoin_blank_right
    (region : Region signature wires rels) :
    RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
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

theorem RegionIso.conjoin_assoc
    (first second third : Region signature wires rels) :
    RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
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

theorem RegionIso.conjoin_comm
    (first second : Region signature wires rels) :
    RegionIso signature (FiniteEquiv.refl (Fin wires)) rels
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

namespace AlgebraExamples

def oneLocalWire : Region [] 0 [] :=
  .mk 1 (.cons (.equation 0 (.port 0)) .nil)

def twoLocalWires : Region [] 0 [] :=
  .mk 2 (.cons (.equation 1 (.port 0)) .nil)

theorem reorderedLocalBlocks :
    RegionIso [] (FiniteEquiv.refl (Fin 0)) []
      (oneLocalWire.conjoin twoLocalWires)
      (twoLocalWires.conjoin oneLocalWire) :=
  RegionIso.conjoin_comm oneLocalWire twoLocalWires

theorem localBlockUnit :
    RegionIso [] (FiniteEquiv.refl (Fin 0)) [] oneLocalWire
      (oneLocalWire.conjoin Region.blank) :=
  RegionIso.conjoin_blank_right oneLocalWire

end AlgebraExamples

end VisualProof.Diagram
