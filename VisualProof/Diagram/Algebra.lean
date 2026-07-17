import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

/-- An arity-preserving renaming of named relations between signatures. -/
structure NamedRenaming (source target : List Nat) where
  named : ∀ {arity}, NamedRel source arity → NamedRel target arity

namespace NamedRenaming

/-- Canonical inclusion of a signature into a right extension. -/
def appendRight (signature suffix : List Nat) :
    NamedRenaming signature (signature ++ suffix) where
  named relation := {
    index := Fin.cast (by simp) (Fin.castAdd suffix.length relation.index)
    hasArity := by
      simpa [List.get_eq_getElem,
        List.getElem_append_left relation.index.isLt] using relation.hasArity
  }

end NamedRenaming

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
    (hostItems : ItemSeq signature (outer + hostLocal) rels)
    (material : Region signature (outer + hostLocal) rels) :
    Region signature outer rels :=
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
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels) :
    Region signature outer hostRels :=
  adjoinAt hostLocal hostItems
    ((material.renameWires wireMap).renameRelations relationMap)

end Region

mutual
  def Region.renameNamed (rho : NamedRenaming source target) :
      Region source wires rels → Region target wires rels
    | .mk localWires items => .mk localWires (items.renameNamed rho)

  def Item.renameNamed (rho : NamedRenaming source target) :
      Item source wires rels → Item target wires rels
    | .equation output term => .equation output term
    | .atom relation arguments => .atom relation arguments
    | .named relation arguments => .named (rho.named relation) arguments
    | .cut body => .cut (body.renameNamed rho)
    | .bubble arity body => .bubble arity (body.renameNamed rho)

  def ItemSeq.renameNamed (rho : NamedRenaming source target) :
      ItemSeq source wires rels → ItemSeq target wires rels
    | .nil => .nil
    | .cons item tail => .cons (item.renameNamed rho) (tail.renameNamed rho)
end

def OpenDiagram.renameNamed (rho : NamedRenaming source target)
    (diagram : OpenDiagram source arity) : OpenDiagram target arity where
  externalClasses := diagram.externalClasses
  boundary := diagram.boundary
  boundary_surjective := diagram.boundary_surjective
  body := diagram.body.renameNamed rho

def NamedEnv.Agrees (rho : NamedRenaming source target)
    (sourceEnv : NamedEnv D source) (targetEnv : NamedEnv D target) : Prop :=
  ∀ arity (relation : NamedRel source arity) args,
    targetEnv arity (rho.named relation) args ↔
      sourceEnv arity relation args

mutual
  theorem denoteRegion_renameNamed
      (model : Lambda.LambdaModel)
      (rho : NamedRenaming source target)
      (sourceNamed : NamedEnv model.Carrier source)
      (targetNamed : NamedEnv model.Carrier target)
      (agrees : NamedEnv.Agrees rho sourceNamed targetNamed)
      (env : Fin wires → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (region : Region source wires relCtx) :
      denoteRegion model targetNamed env rels (region.renameNamed rho) ↔
        denoteRegion model sourceNamed env rels region := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameNamed, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameNamed model rho sourceNamed targetNamed agrees
              (extendWireEnv env localEnv) rels items).mp hitems⟩
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameNamed model rho sourceNamed targetNamed agrees
              (extendWireEnv env localEnv) rels items).mpr hitems⟩

  theorem denoteItem_renameNamed
      (model : Lambda.LambdaModel)
      (rho : NamedRenaming source target)
      (sourceNamed : NamedEnv model.Carrier source)
      (targetNamed : NamedEnv model.Carrier target)
      (agrees : NamedEnv.Agrees rho sourceNamed targetNamed)
      (env : Fin wires → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (item : Item source wires relCtx) :
      denoteItem model targetNamed env rels (item.renameNamed rho) ↔
        denoteItem model sourceNamed env rels item := by
    cases item with
    | equation => rfl
    | atom => rfl
    | named relation arguments =>
        simpa [Item.renameNamed, denoteItem_named] using
          agrees _ relation (env ∘ arguments)
    | cut body =>
        simp only [Item.renameNamed, cut_denotes_negation]
        rw [denoteRegion_renameNamed model rho sourceNamed targetNamed agrees
          env rels body]
    | bubble arity body =>
        simp only [Item.renameNamed, bubble_denotes_exists]
        constructor
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameNamed (relCtx := arity :: relCtx)
              model rho sourceNamed targetNamed agrees
              env (relation, rels) body).mp hbody⟩
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameNamed (relCtx := arity :: relCtx)
              model rho sourceNamed targetNamed agrees
              env (relation, rels) body).mpr hbody⟩

  theorem denoteItemSeq_renameNamed
      (model : Lambda.LambdaModel)
      (rho : NamedRenaming source target)
      (sourceNamed : NamedEnv model.Carrier source)
      (targetNamed : NamedEnv model.Carrier target)
      (agrees : NamedEnv.Agrees rho sourceNamed targetNamed)
      (env : Fin wires → model.Carrier)
      (rels : RelEnv model.Carrier relCtx)
      (items : ItemSeq source wires relCtx) :
      denoteItemSeq model targetNamed env rels (items.renameNamed rho) ↔
        denoteItemSeq model sourceNamed env rels items := by
    cases items with
    | nil => rfl
    | cons item tail =>
        simp only [ItemSeq.renameNamed, denoteItemSeq_cons]
        rw [denoteItem_renameNamed model rho sourceNamed targetNamed agrees
          env rels item,
          denoteItemSeq_renameNamed model rho sourceNamed targetNamed agrees
            env rels tail]
end

theorem denoteOpen_renameNamed
    (model : Lambda.LambdaModel)
    (rho : NamedRenaming source target)
    (sourceNamed : NamedEnv model.Carrier source)
    (targetNamed : NamedEnv model.Carrier target)
    (agrees : NamedEnv.Agrees rho sourceNamed targetNamed)
    (diagram : OpenDiagram source arity)
    (args : Fin arity → model.Carrier) :
    denoteOpen model targetNamed (diagram.renameNamed rho) args ↔
      denoteOpen model sourceNamed diagram args := by
  unfold denoteOpen
  constructor
  · rintro ⟨assignment, hargs, hbody⟩
    let sourceAssignment : BoundaryAssignment diagram model.Carrier := {
      args := assignment.args
      classes := assignment.classes
      agrees := assignment.agrees
    }
    exact ⟨sourceAssignment, hargs,
      (denoteRegion_renameNamed (relCtx := []) model rho sourceNamed
        targetNamed agrees sourceAssignment.classes PUnit.unit
        diagram.body).mp hbody⟩
  · rintro ⟨assignment, hargs, hbody⟩
    let targetAssignment :
        BoundaryAssignment (diagram.renameNamed rho) model.Carrier := {
      args := assignment.args
      classes := assignment.classes
      agrees := assignment.agrees
    }
    exact ⟨targetAssignment, hargs,
      (denoteRegion_renameNamed (relCtx := []) model rho sourceNamed
        targetNamed agrees targetAssignment.classes PUnit.unit
        diagram.body).mpr hbody⟩

structure ItemSeq.Focus (items : ItemSeq signature wires rels) where
  before : ItemSeq signature wires rels
  item : Item signature wires rels
  after : ItemSeq signature wires rels
  rebuild : before.append (.cons item after) = items

def Item.castWiresEq (equality : source = target)
    (item : Item signature source rels) : Item signature target rels :=
  Eq.mp (congrArg (fun wires => Item signature wires rels) equality) item

def ItemSeq.castWiresEq (equality : source = target)
    (items : ItemSeq signature source rels) : ItemSeq signature target rels :=
  Eq.mp (congrArg (fun wires => ItemSeq signature wires rels) equality) items

def Region.castWiresEq (equality : source = target)
    (region : Region signature source rels) : Region signature target rels :=
  Eq.mp (congrArg (fun wires => Region signature wires rels) equality) region

@[simp] theorem ItemSeq.castWiresEq_trans
    (first : source = middle) (second : middle = target)
    (items : ItemSeq signature source rels) :
    (items.castWiresEq first).castWiresEq second =
      items.castWiresEq (first.trans second) := by
  subst middle
  subst target
  rfl

@[simp] theorem Region.castWiresEq_mk
    (equality : sourceOuter = targetOuter)
    (items : ItemSeq signature (sourceOuter + localWires) rels) :
    Region.castWiresEq equality (Region.mk localWires items) =
      Region.mk localWires
        (items.castWiresEq
          (congrArg (fun outer => outer + localWires) equality)) := by
  subst targetOuter
  rfl

@[simp] theorem Item.castWiresEq_renameNamed
    (equality : sourceWires = targetWires)
    (rho : NamedRenaming sourceSignature targetSignature)
    (item : Item sourceSignature sourceWires rels) :
    (item.renameNamed rho).castWiresEq equality =
      (item.castWiresEq equality).renameNamed rho := by
  subst targetWires
  rfl

@[simp] theorem ItemSeq.castWiresEq_renameNamed
    (equality : sourceWires = targetWires)
    (rho : NamedRenaming sourceSignature targetSignature)
    (items : ItemSeq sourceSignature sourceWires rels) :
    (items.renameNamed rho).castWiresEq equality =
      (items.castWiresEq equality).renameNamed rho := by
  subst targetWires
  rfl

@[simp] theorem Region.castWiresEq_renameNamed
    (equality : sourceWires = targetWires)
    (rho : NamedRenaming sourceSignature targetSignature)
    (region : Region sourceSignature sourceWires rels) :
    (region.renameNamed rho).castWiresEq equality =
      (region.castWiresEq equality).renameNamed rho := by
  subst targetWires
  rfl

theorem Region.castWiresEq_eq_renameWires (equality : source = target)
    (region : Region signature source rels) :
    region.castWiresEq equality = region.renameWires (Fin.cast equality) := by
  subst target
  simp [Region.castWiresEq, Region.renameWires_id]

theorem Item.castWiresEq_eq_renameWires (equality : source = target)
    (item : Item signature source rels) :
    item.castWiresEq equality = item.renameWires (Fin.cast equality) := by
  subst target
  simp [Item.castWiresEq, Item.renameWires_id]

theorem ItemSeq.castWiresEq_eq_renameWires (equality : source = target)
    (items : ItemSeq signature source rels) :
    items.castWiresEq equality = items.renameWires (Fin.cast equality) := by
  subst target
  simp [ItemSeq.castWiresEq, ItemSeq.renameWires_id]

@[simp] theorem ItemSeq.castWiresEq_append
    (equality : source = target)
    (first second : ItemSeq signature source rels) :
    (first.append second).castWiresEq equality =
      (first.castWiresEq equality).append
        (second.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem ItemSeq.castWiresEq_cons
    (equality : source = target)
    (item : Item signature source rels)
    (tail : ItemSeq signature source rels) :
    (ItemSeq.cons item tail).castWiresEq equality =
      ItemSeq.cons (item.castWiresEq equality)
        (tail.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem Region.castWiresEq_adjoinAt_nil
    (equality : source = target)
    (hostLocal : Nat)
    (material : Region signature (source + hostLocal) rels) :
    (Region.adjoinAt hostLocal .nil material).castWiresEq equality =
      Region.adjoinAt hostLocal .nil
        (material.castWiresEq
          (congrArg (fun outer => outer + hostLocal) equality)) := by
  subst target
  rfl

@[simp] theorem Region.castWiresEq_trans
    (first : source = middle) (second : middle = target)
    (region : Region signature source rels) :
    (region.castWiresEq first).castWiresEq second =
      region.castWiresEq (first.trans second) := by
  subst middle
  subst target
  rfl

theorem Region.castWiresEq_proof_irrel
    (first second : source = target)
    (region : Region signature source rels) :
    region.castWiresEq first = region.castWiresEq second := by
  rw [show first = second from Subsingleton.elim _ _]

theorem Region.castWiresEq_castRels
    (wireEquality : sourceWires = targetWires)
    (relsEquality : sourceRels = targetRels)
    (region : Region signature sourceWires sourceRels) :
    (relsEquality ▸ region).castWiresEq wireEquality =
      relsEquality ▸ (region.castWiresEq wireEquality) := by
  subst targetWires
  subst targetRels
  rfl

@[simp] theorem Item.castWiresEq_cut
    (equality : source = target) (body : Region signature source rels) :
    (Item.cut body).castWiresEq equality =
      Item.cut (body.castWiresEq equality) := by
  subst target
  rfl

@[simp] theorem Item.castWiresEq_bubble
    (equality : source = target) (arity : Nat)
    (body : Region signature source (arity :: rels)) :
    (Item.bubble arity body).castWiresEq equality =
      Item.bubble arity (body.castWiresEq equality) := by
  subst target
  rfl

def ItemSeq.focusAt? :
    (items : ItemSeq signature wires rels) → Nat → Option (ItemSeq.Focus items)
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

theorem ItemSeq.focusAt?_complete
    (items : ItemSeq signature wires rels) (index : Fin items.length) :
    ∃ focus, items.focusAt? index.val = some focus ∧
      focus.item = items.get index := by
  cases items with
  | nil => exact Fin.elim0 index
  | cons item tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact ⟨{
          before := .nil
          item := item
          after := tail
          rebuild := rfl
        }, rfl, rfl⟩
      · obtain ⟨focus, hfocus, hitem⟩ :=
          ItemSeq.focusAt?_complete tail tailIndex
        refine ⟨{
          before := .cons item focus.before
          item := focus.item
          after := focus.after
          rebuild := by
            simp only [ItemSeq.append]
            exact congrArg (ItemSeq.cons item) focus.rebuild
        }, ?_, ?_⟩
        · simp [ItemSeq.focusAt?, hfocus]
        · simpa only [ItemSeq.get] using hitem
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

/-- A successful natural-number focus lookup determines a valid finite
position.  This is the converse bound needed to transport a context path
through an item permutation. -/
theorem ItemSeq.focusAt?_index_lt
    (items : ItemSeq signature wires rels) (index : Nat)
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
    (items : ItemSeq signature source rels) (index : Nat)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index = some focus) :
    (items.castWiresEq equality).focusAt? index =
      some (focus.castWiresEq equality) := by
  subst target
  exact hfocus

/-- The structural focus decomposition is the corresponding single-item
replacement. -/
theorem ItemSeq.replaceAt_eq_focus
    (items : ItemSeq signature wires rels) (index : Fin items.length)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index.val = some focus)
    (replacement : Item signature wires rels) :
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
    (region : Region signature wires rels) where
  holeWires : Nat
  holeRels : RelCtx
  context : DiagramContext signature wires holeWires rels holeRels
  body : Region signature holeWires holeRels
  rebuild : context.fill body = region

/-- Intrinsic evidence that a list of item positions selects a nested region.
Unlike the executable lookup below, this type exposes the constructor evidence
needed by semantic proofs without comparing dependent proof fields. -/
inductive Region.ContextPath :
    (region : Region signature wires rels) → List Nat → Type
  | here (region : Region signature wires rels) : ContextPath region []
  | cut {localWires : Nat}
      {items : ItemSeq signature (wires + localWires) rels}
      {index : Nat} {rest : List Nat}
      (focus : ItemSeq.Focus items)
      (atIndex : items.focusAt? index = some focus)
      {child : Region signature (wires + localWires) rels}
      (isCut : focus.item = .cut child)
      (nested : ContextPath child rest) :
      ContextPath (.mk localWires items) (index :: rest)
  | bubble {localWires arity : Nat}
      {items : ItemSeq signature (wires + localWires) rels}
      {index : Nat} {rest : List Nat}
      (focus : ItemSeq.Focus items)
      (atIndex : items.focusAt? index = some focus)
      {child : Region signature (wires + localWires) (arity :: rels)}
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
    {region : Region signature wires rels} → {path : List Nat} →
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
    {root : Region signature wires rels} {outerPath : List Nat}
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
    {root : Region signature wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    (outer.nest inner).toFocus.holeWires = inner.toFocus.holeWires := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction => exact induction inner
  | bubble focus atIndex isBubble nested induction => exact induction inner

@[simp] theorem Region.ContextPath.nest_toFocus_holeRels
    {root : Region signature wires rels} {outerPath : List Nat}
    (outer : Region.ContextPath root outerPath)
    {innerPath : List Nat}
    (inner : Region.ContextPath outer.toFocus.body innerPath) :
    (outer.nest inner).toFocus.holeRels = inner.toFocus.holeRels := by
  induction outer with
  | here region => rfl
  | cut focus atIndex isCut nested induction => exact induction inner
  | bubble focus atIndex isBubble nested induction => exact induction inner

theorem Region.ContextPath.nest_toFocus_body_heq
    {root : Region signature wires rels} {outerPath : List Nat}
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
    {source target : RelCtx} {region : Region signature wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    Region.ContextPath (equality ▸ region) path := by
  subst target
  exact witness

@[simp] theorem Region.ContextPath.castRelsEq_toFocus_holeWires
    {source target : RelCtx} {region : Region signature wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castRelsEq equality).toFocus.holeWires =
      witness.toFocus.holeWires := by
  subst target
  rfl

@[simp] theorem Region.ContextPath.castRelsEq_toFocus_holeRels
    {source target : RelCtx} {region : Region signature wires source}
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    (witness.castRelsEq equality).toFocus.holeRels =
      witness.toFocus.holeRels := by
  subst target
  rfl

theorem Region.ContextPath.castRelsEq_fill
    {source target : RelCtx} {region : Region signature wires source}
    {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath region path)
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness := witness.castRelsEq equality
    let holeWiresEq : targetWitness.toFocus.holeWires =
        witness.toFocus.holeWires :=
      witness.castRelsEq_toFocus_holeWires equality
    let holeRelsEq : targetWitness.toFocus.holeRels =
        witness.toFocus.holeRels :=
      witness.castRelsEq_toFocus_holeRels equality
    let targetReplacement : Region signature
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
    {items : ItemSeq signature (sourceOuter + sourceLocal) rels}
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

/-- Rebuilding after an outer-wire cast is the cast of the rebuilt region;
the focused replacement is transported by the induced hole equalities. -/
theorem Region.ContextPath.castWiresEq_fill
    {source target : Nat} {region : Region signature source rels}
    {path : List Nat}
    (equality : source = target)
    (witness : Region.ContextPath region path)
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    let targetWitness := witness.castWiresEq equality
    let holeWiresEq : targetWitness.toFocus.holeWires =
      witness.toFocus.holeWires :=
        witness.castWiresEq_toFocus_holeWires equality
    let holeRelsEq : targetWitness.toFocus.holeRels =
      witness.toFocus.holeRels :=
        witness.castWiresEq_toFocus_holeRels equality
    let targetReplacement : Region signature
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    DiagramContext.fill (signature := signature)
        targetWitness.toFocus.context targetReplacement =
      (DiagramContext.fill (signature := signature)
        witness.toFocus.context replacement).castWiresEq equality := by
  subst target
  rfl

theorem Region.ContextPath.relocal_toFocus_holeWires_of_nonempty
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {items : ItemSeq signature (sourceOuter + sourceLocal) rels}
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
    {items : ItemSeq signature (sourceOuter + sourceLocal) rels}
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
    {items : ItemSeq signature sourceOuter rels}
    {path : List Nat}
    (equality : sourceOuter = targetOuter + targetLocal)
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (nonempty : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
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
    let targetReplacement : Region signature
        targetWitness.toFocus.holeWires targetWitness.toFocus.holeRels :=
      (holeRelsEq.symm ▸ replacement).castWiresEq holeWiresEq.symm
    DiagramContext.fill (signature := signature)
        targetWitness.toFocus.context targetReplacement =
      Region.adjoinAt targetLocal .nil
        ((DiagramContext.fill (signature := signature)
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
        ItemSeq.renameWires, ItemSeq.renameWires_id,
        Region.ContextPath.castWiresEq_fill]
      congr 3
  | bubble focus atIndex isBubble nested =>
      have hmaterial :
          Region.adjoinMaterialWire targetOuter targetLocal 0 = id := by
        funext wire
        apply Fin.ext
        rfl
      simp [Region.ContextPath.relocal, Region.ContextPath.toFocus,
        DiagramContext.fill, Region.adjoinAt, hmaterial,
        ItemSeq.renameWires, ItemSeq.renameWires_id,
        Region.ContextPath.castWiresEq_fill]
      congr 3

/-- Follow an intrinsic child-item path and return the unique typed context and
focused region together with a reconstruction equation.  A path step must name
a cut or bubble item; equations and atoms cannot contain a region. -/
def Region.contextAtPath? :
    (region : Region signature wires rels) →
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
      | .equation .. | .atom .. | .named .. => none

theorem Region.contextAtPath?_castWiresEq
    (equality : source = target)
    (region : Region signature source rels) (path : List Nat)
    (focus : Region.ContextFocus region)
    (hfocus : region.contextAtPath? path = some focus) :
    ∃ transported,
      (region.castWiresEq equality).contextAtPath? path = some transported := by
  subst target
  exact ⟨focus, hfocus⟩

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

private theorem extendWireEnv_adjoinHost
    (outerEnv : Fin outer → D)
    (localEnv : Fin (hostLocal + addedLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.adjoinHostWire outer hostLocal addedLocal =
      extendWireEnv outerEnv
        (fun wire => localEnv (Fin.castAdd addedLocal wire)) := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · simp only [Function.comp_apply]
    rw [Region.adjoinHostWire_inherited]
    simp [extendWireEnv]
  · simp only [Function.comp_apply]
    rw [Region.adjoinHostWire_local]
    simp [extendWireEnv]

private theorem extendWireEnv_adjoinMaterial
    (outerEnv : Fin outer → D)
    (localEnv : Fin (hostLocal + addedLocal) → D) :
    extendWireEnv outerEnv localEnv ∘
        Region.adjoinMaterialWire outer hostLocal addedLocal =
      extendWireEnv
        (extendWireEnv outerEnv
          (fun wire => localEnv (Fin.castAdd addedLocal wire)))
        (fun wire => localEnv (Fin.natAdd hostLocal wire)) := by
  funext wire
  refine Fin.addCases (fun prior => ?_) (fun added => ?_) wire
  · refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) prior
    · simp only [Function.comp_apply]
      rw [Region.adjoinMaterialWire_prior,
        Region.adjoinHostWire_inherited]
      simp [extendWireEnv]
    · simp only [Function.comp_apply]
      rw [Region.adjoinMaterialWire_prior,
        Region.adjoinHostWire_local]
      simp [extendWireEnv]
  · simp only [Function.comp_apply]
    rw [Region.adjoinMaterialWire_added]
    simp [extendWireEnv]

theorem Region.denote_adjoinAt
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) rels)
    (material : Region signature (outer + hostLocal) rels) :
    denoteRegion model named env relEnv
        (Region.adjoinAt hostLocal hostItems material) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model named (extendWireEnv env hostEnv) relEnv hostItems ∧
          denoteRegion model named (extendWireEnv env hostEnv) relEnv material := by
  cases material with
  | mk addedLocal addedItems =>
      simp only [Region.adjoinAt, denoteRegion_mk, denoteItemSeq_append]
      constructor
      · rintro ⟨localEnv, hhost, hmaterial⟩
        let hostEnv : Fin hostLocal → model.Carrier :=
          fun wire => localEnv (Fin.castAdd addedLocal wire)
        let addedEnv : Fin addedLocal → model.Carrier :=
          fun wire => localEnv (Fin.natAdd hostLocal wire)
        refine ⟨hostEnv, ?_, ⟨addedEnv, ?_⟩⟩
        · have renamed := (denoteItemSeq_renameWires model named
            (Region.adjoinHostWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv hostItems).mp hhost
          simpa [hostEnv, extendWireEnv_adjoinHost] using renamed
        · have renamed := (denoteItemSeq_renameWires model named
            (Region.adjoinMaterialWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv addedItems).mp hmaterial
          simpa [hostEnv, addedEnv, extendWireEnv_adjoinMaterial] using renamed
      · rintro ⟨hostEnv, hhost, addedEnv, hmaterial⟩
        let localEnv : Fin (hostLocal + addedLocal) → model.Carrier :=
          Fin.addCases hostEnv addedEnv
        refine ⟨localEnv, ?_, ?_⟩
        · apply (denoteItemSeq_renameWires model named
            (Region.adjoinHostWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv hostItems).mpr
          simpa [localEnv, extendWireEnv_adjoinHost] using hhost
        · apply (denoteItemSeq_renameWires model named
            (Region.adjoinMaterialWire outer hostLocal addedLocal)
            (extendWireEnv env localEnv) relEnv addedItems).mpr
          simpa [localEnv, extendWireEnv_adjoinMaterial] using hmaterial

theorem Region.adjoinAt_mono
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostItems : ItemSeq signature (outer + hostLocal) rels)
    (before after : Region signature (outer + hostLocal) rels)
    (entails : ∀ siteEnv,
      denoteRegion model named siteEnv relEnv before →
        denoteRegion model named siteEnv relEnv after) :
    denoteRegion model named env relEnv
        (Region.adjoinAt hostLocal hostItems before) →
      denoteRegion model named env relEnv
        (Region.adjoinAt hostLocal hostItems after) := by
  intro hbefore
  rw [Region.denote_adjoinAt] at hbefore ⊢
  obtain ⟨hostEnv, hitems, hmaterial⟩ := hbefore
  exact ⟨hostEnv, hitems, entails _ hmaterial⟩

theorem Region.adjoinAt_equiv
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hostItems : ItemSeq signature (outer + hostLocal) rels)
    (before after : Region signature (outer + hostLocal) rels)
    (equivalent : ∀ siteEnv,
      denoteRegion model named siteEnv relEnv before ↔
        denoteRegion model named siteEnv relEnv after) :
    denoteRegion model named env relEnv
        (Region.adjoinAt hostLocal hostItems before) ↔
      denoteRegion model named env relEnv
        (Region.adjoinAt hostLocal hostItems after) := by
  constructor
  · exact Region.adjoinAt_mono model named env relEnv hostItems before after
      (fun siteEnv => (equivalent siteEnv).mp)
  · exact Region.adjoinAt_mono model named env relEnv hostItems after before
      (fun siteEnv => (equivalent siteEnv).mpr)

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

/-- Local semantic equivalence is substitutive through a context at either polarity. -/
theorem DiagramContext.fill_equiv
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (first second : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hequiv : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv first ↔
        denoteRegion model named holeEnv holeRelEnv second) :
    denoteRegion model named env rels (ctx.fill first) ↔
      denoteRegion model named env rels (ctx.fill second) := by
  constructor
  · by_cases heven : ctx.cutDepth % 2 = 0
    · exact context_mono model named env rels heven
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mp)
    · have hodd : ctx.cutDepth % 2 = 1 := by omega
      exact context_anti (ctx := ctx) (a := second) (b := first)
        model named env rels hodd
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mpr)
  · by_cases heven : ctx.cutDepth % 2 = 0
    · exact context_mono (ctx := ctx) (a := second) (b := first)
        model named env rels heven
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mpr)
    · have hodd : ctx.cutDepth % 2 = 1 := by omega
      exact context_anti model named env rels hodd
        (fun holeEnv holeRelEnv => (hequiv holeEnv holeRelEnv).mp)

/-- A boundary assignment is determined by its ordered arguments because every
external class is represented by at least one boundary position. -/
theorem BoundaryAssignment.classes_eq_of_args_eq
    {diagram : OpenDiagram signature arity}
    (first second : BoundaryAssignment diagram D)
    (hargs : first.args = second.args) :
    first.classes = second.classes := by
  funext external
  obtain ⟨position, rfl⟩ := diagram.boundary_surjective external
  calc
    first.classes (diagram.boundary position) = first.args position :=
      first.agrees position
    _ = second.args position := congrFun hargs position
    _ = second.classes (diagram.boundary position) :=
      (second.agrees position).symm

/-- Intrinsic open-diagram substitution: supplying host wire variables for the
boundary classes has exactly the open denotation at the corresponding host
values.  Aliased positions are handled by `BoundaryAssignment`, not by an
independent equality convention. -/
theorem OpenDiagram.denote_substituteBoundary
    (diagram : OpenDiagram signature arity)
    (assignment : BoundaryAssignment diagram (Fin wires))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier) :
    denoteRegion (relCtx := []) model named env PUnit.unit
        (diagram.substituteBoundary assignment) ↔
      denoteOpen model named diagram (env ∘ assignment.args) := by
  rw [OpenDiagram.substituteBoundary, denoteRegion_renameWires]
  constructor
  · intro hbody
    refine ⟨assignment.map env, rfl, ?_⟩
    exact hbody
  · rintro ⟨actual, hargs, hbody⟩
    have hclasses : actual.classes = (assignment.map env).classes :=
      BoundaryAssignment.classes_eq_of_args_eq actual (assignment.map env)
        hargs
    rw [hclasses] at hbody
    exact hbody

def RelEnv.Agrees (rho : RelationRenaming source target)
    (sourceEnv : RelEnv D source) (targetEnv : RelEnv D target) : Prop :=
  ∀ arity (relation : RelVar source arity),
    sourceEnv.lookup relation = targetEnv.lookup (rho relation)

/-- Restrict a lexical relation environment along a relation renaming. -/
def RelEnv.pullback : {source : RelCtx} →
    RelationRenaming source target → RelEnv D target → RelEnv D source
  | [], _, _ => PUnit.unit
  | arity :: rest, rho, targetEnv =>
      (targetEnv.lookup (rho ⟨0, rfl⟩),
        RelEnv.pullback
          (fun {arity} relation => rho ⟨relation.index.succ, relation.hasArity⟩)
          targetEnv)

theorem RelEnv.pullback_agrees
    (rho : RelationRenaming source target) (targetEnv : RelEnv D target) :
    RelEnv.Agrees rho (RelEnv.pullback rho targetEnv) targetEnv := by
  intro arity relation
  induction source with
  | nil => exact Fin.elim0 relation.index
  | cons head rest ih =>
      rcases relation with ⟨index, hasArity⟩
      revert hasArity
      refine Fin.cases ?_ (fun tail => ?_) index
      · intro hasArity
        subst arity
        rfl
      · intro hasArity
        simpa [RelEnv.pullback, RelEnv.lookup] using
          ih (fun {arity} relation =>
            rho ⟨relation.index.succ, relation.hasArity⟩)
            ⟨tail, hasArity⟩

theorem RelEnv.Agrees.lift
    (rho : RelationRenaming source target)
    (sourceEnv : RelEnv D source) (targetEnv : RelEnv D target)
    (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
    (headRelation : Relation D head) :
    RelEnv.Agrees (RelationRenaming.lift rho head)
      (headRelation, sourceEnv) (headRelation, targetEnv) := by
  intro arity relation
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun index => ?_) index
  · intro hasArity
    rfl
  · intro hasArity
    exact agrees arity ⟨index, hasArity⟩

mutual
  theorem denoteRegion_renameRelations
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (region : Region signature wires source) :
      denoteRegion model named env targetEnv (region.renameRelations rho) ↔
        denoteRegion model named env sourceEnv region := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameRelations, denoteRegion_mk]
        constructor
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameRelations model named rho sourceEnv targetEnv
              agrees (extendWireEnv env localEnv) items).mp hitems⟩
        · rintro ⟨localEnv, hitems⟩
          exact ⟨localEnv,
            (denoteItemSeq_renameRelations model named rho sourceEnv targetEnv
              agrees (extendWireEnv env localEnv) items).mpr hitems⟩

  theorem denoteItem_renameRelations
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (item : Item signature wires source) :
      denoteItem model named env targetEnv (item.renameRelations rho) ↔
        denoteItem model named env sourceEnv item := by
    cases item with
    | equation output term => rfl
    | atom relation arguments =>
        simp only [Item.renameRelations, denoteItem_atom]
        rw [← agrees _ relation]
    | named relation arguments => rfl
    | cut body =>
        simp only [Item.renameRelations, cut_denotes_negation]
        rw [denoteRegion_renameRelations model named rho sourceEnv targetEnv
          agrees env body]
    | bubble arity body =>
        simp only [Item.renameRelations, bubble_denotes_exists]
        constructor
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameRelations model named
              (RelationRenaming.lift rho arity)
              (relation, sourceEnv) (relation, targetEnv)
              (RelEnv.Agrees.lift rho sourceEnv targetEnv agrees relation)
              env body).mp hbody⟩
        · rintro ⟨relation, hbody⟩
          exact ⟨relation,
            (denoteRegion_renameRelations model named
              (RelationRenaming.lift rho arity)
              (relation, sourceEnv) (relation, targetEnv)
              (RelEnv.Agrees.lift rho sourceEnv targetEnv agrees relation)
              env body).mpr hbody⟩

  theorem denoteItemSeq_renameRelations
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (rho : RelationRenaming source target)
      (sourceEnv : RelEnv model.Carrier source)
      (targetEnv : RelEnv model.Carrier target)
      (agrees : RelEnv.Agrees rho sourceEnv targetEnv)
      (env : Fin wires → model.Carrier)
      (items : ItemSeq signature wires source) :
      denoteItemSeq model named env targetEnv (items.renameRelations rho) ↔
        denoteItemSeq model named env sourceEnv items := by
    cases items with
    | nil => rfl
    | cons item tail =>
        simp only [ItemSeq.renameRelations, denoteItemSeq_cons]
        rw [denoteItem_renameRelations model named rho sourceEnv targetEnv
          agrees env item,
          denoteItemSeq_renameRelations model named rho sourceEnv targetEnv
            agrees env tail]
end

/-- Exact semantics of the intrinsic insertion kernel.  It exposes the two
conjuncts used by every splice-backed rule: the unchanged host items and the
pattern material evaluated after wire and lexical-relation substitution. -/
theorem Region.denote_spliceAt
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (patternRelEnv : RelEnv model.Carrier patternRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (relationsAgree : RelEnv.Agrees relationMap patternRelEnv hostRelEnv) :
    denoteRegion model named env hostRelEnv
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) ↔
      ∃ hostEnv : Fin hostLocal → model.Carrier,
        denoteItemSeq model named (extendWireEnv env hostEnv) hostRelEnv
            hostItems ∧
          denoteRegion model named
            (extendWireEnv env hostEnv ∘ wireMap) patternRelEnv material := by
  rw [Region.spliceAt, Region.denote_adjoinAt]
  apply exists_congr
  intro hostEnv
  apply and_congr Iff.rfl
  rw [denoteRegion_renameRelations model named relationMap patternRelEnv
      hostRelEnv relationsAgree (extendWireEnv env hostEnv)
      (material.renameWires wireMap),
    denoteRegion_renameWires]

/-- A pointwise implication between two replacement materials lifts through
the intrinsic splice kernel while preserving the same host witness, wire
substitution, and lexical-relation substitution. This is the shared local
semantic core for replacement rules whose concrete carrier is compiled by the
splice subsystem. -/
theorem Region.denote_spliceAt_mono
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (source target : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (entails : ∀ patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap hostRelEnv) source →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap hostRelEnv) target) :
    denoteRegion model named env hostRelEnv
        (Region.spliceAt hostLocal hostItems source wireMap relationMap) →
      denoteRegion model named env hostRelEnv
        (Region.spliceAt hostLocal hostItems target wireMap relationMap) := by
  rw [Region.denote_spliceAt model named env hostRelEnv
      (RelEnv.pullback relationMap hostRelEnv) hostLocal hostItems source wireMap
      relationMap (RelEnv.pullback_agrees relationMap hostRelEnv),
    Region.denote_spliceAt model named env hostRelEnv
      (RelEnv.pullback relationMap hostRelEnv) hostLocal hostItems target wireMap
      relationMap (RelEnv.pullback_agrees relationMap hostRelEnv)]
  rintro ⟨hostEnv, hhost, hsource⟩
  exact ⟨hostEnv, hhost, entails _ hsource⟩

/-- `denote_spliceAt_mono` after the outer-wire and lexical-relation
transports used by the concrete compiler. -/
theorem Region.denote_spliceAt_mono_renamed
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin targetOuter → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (source target : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (outerMap : Fin outer → Fin targetOuter)
    (hostRelationMap : RelationRenaming hostRels targetRels)
    (entails : ∀ patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap targetRelEnv)) source →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap
            (RelEnv.pullback hostRelationMap targetRelEnv)) target) :
    denoteRegion model named env targetRelEnv
        (((Region.spliceAt hostLocal hostItems source wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) →
      denoteRegion model named env targetRelEnv
        (((Region.spliceAt hostLocal hostItems target wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameWires,
    denoteRegion_renameRelations model named hostRelationMap
      (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
      (RelEnv.pullback_agrees hostRelationMap targetRelEnv)
      (env ∘ outerMap)
      (Region.spliceAt hostLocal hostItems source wireMap relationMap),
    denoteRegion_renameRelations model named hostRelationMap
      (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
      (RelEnv.pullback_agrees hostRelationMap targetRelEnv)
      (env ∘ outerMap)
      (Region.spliceAt hostLocal hostItems target wireMap relationMap)]
  exact Region.denote_spliceAt_mono model named (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap targetRelEnv) hostLocal hostItems source
    target wireMap relationMap entails

/-- Splicing material only strengthens the unchanged host at the splice site. -/
theorem Region.denote_spliceAt_host
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (hostRelEnv : RelEnv model.Carrier hostRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels) :
    denoteRegion model named env hostRelEnv
        (Region.spliceAt hostLocal hostItems material wireMap relationMap) →
      denoteRegion model named env hostRelEnv (.mk hostLocal hostItems) := by
  intro hsplice
  rw [Region.spliceAt, Region.denote_adjoinAt] at hsplice
  obtain ⟨hostEnv, hhost, _⟩ := hsplice
  exact ⟨hostEnv, hhost⟩

/-- Host projection is stable under the relation and outer-wire transports
used by the concrete splice compiler. -/
theorem Region.denote_spliceAt_host_renamed
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin targetOuter → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (outerMap : Fin outer → Fin targetOuter)
    (hostRelationMap : RelationRenaming hostRels targetRels) :
    denoteRegion model named env targetRelEnv
        (((Region.spliceAt hostLocal hostItems material wireMap relationMap)
          |>.renameRelations hostRelationMap).renameWires outerMap) →
      denoteRegion model named env targetRelEnv
        (((Region.mk hostLocal hostItems).renameRelations hostRelationMap)
          |>.renameWires outerMap) := by
  rw [denoteRegion_renameWires, denoteRegion_renameRelations model named
    hostRelationMap (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees hostRelationMap targetRelEnv)]
  rw [denoteRegion_renameWires, denoteRegion_renameRelations model named
    hostRelationMap (RelEnv.pullback hostRelationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees hostRelationMap targetRelEnv)]
  exact Region.denote_spliceAt_host model named (env ∘ outerMap)
    (RelEnv.pullback hostRelationMap targetRelEnv) hostLocal hostItems material
    wireMap relationMap

/-- Adding a block of semantically unused local wires does not change a
region's denotation. -/
theorem Region.denote_addUnusedLocals_iff
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (items : ItemSeq signature (outer + hostLocal) relCtx)
    (extra : Nat) :
    denoteRegion model named env rels
        (Region.mk (hostLocal + extra)
          (items.renameWires
            (Region.conjoinLeftWire outer hostLocal extra))) ↔
      denoteRegion model named env rels (Region.mk hostLocal items) := by
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨expanded, hitems⟩
    let original : Fin hostLocal → model.Carrier :=
      fun index => expanded (Fin.castAdd extra index)
    refine ⟨original, ?_⟩
    rw [denoteItemSeq_renameWires] at hitems
    have henv :
        extendWireEnv env expanded ∘
            Region.conjoinLeftWire outer hostLocal extra =
          extendWireEnv env original := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [Region.conjoinLeftWire, extendWireEnv]
      · simp [original, Region.conjoinLeftWire, extendWireEnv]
    rw [henv] at hitems
    exact hitems
  · rintro ⟨original, hitems⟩
    let fallback : model.Carrier :=
      model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
        Lambda.Term 0 (Fin 0)) Fin.elim0
    let expanded : Fin (hostLocal + extra) → model.Carrier :=
      Fin.addCases original (fun _ => fallback)
    refine ⟨expanded, ?_⟩
    apply (denoteItemSeq_renameWires model named
      (Region.conjoinLeftWire outer hostLocal extra)
      (extendWireEnv env expanded) rels items).2
    have henv :
        extendWireEnv env expanded ∘
            Region.conjoinLeftWire outer hostLocal extra =
          extendWireEnv env original := by
      funext index
      refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) index
      · simp [Region.conjoinLeftWire, extendWireEnv]
      · simp [expanded, Region.conjoinLeftWire, extendWireEnv]
    rw [henv]
    exact hitems

/-- Dropping a suffix of constraints from a region with the same local-wire
block is semantically covariant.  This is the normalized root counterpart of
`denote_spliceAt_host`. -/
theorem Region.denote_mk_append_left
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outer → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (localWires : Nat)
    (first second : ItemSeq signature (outer + localWires) rels) :
    denoteRegion model named env relEnv
        (Region.mk localWires (first.append second)) →
      denoteRegion model named env relEnv (Region.mk localWires first) := by
  rw [denoteRegion_mk, denoteRegion_mk]
  rintro ⟨localEnv, hitems⟩
  rw [denoteItemSeq_append] at hitems
  exact ⟨localEnv, hitems.1⟩

/-- At even cut depth, host projection remains covariant through the context. -/
theorem DiagramContext.fill_spliceAt_host_even
    (ctx : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hEven : ctx.cutDepth % 2 = 0) :
    denoteRegion model named env rels
        (ctx.fill (Region.spliceAt hostLocal hostItems material wireMap relationMap)) →
      denoteRegion model named env rels (ctx.fill (.mk hostLocal hostItems)) := by
  apply context_mono model named env rels hEven
  intro holeEnv holeRelEnv hsplice
  exact Region.denote_spliceAt_host model named holeEnv holeRelEnv hostLocal
    hostItems material wireMap relationMap hsplice

/-- At odd cut depth, host projection reverses through the context. -/
theorem DiagramContext.fill_spliceAt_host_odd
    (ctx : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hOdd : ctx.cutDepth % 2 = 1) :
    denoteRegion model named env rels (ctx.fill (.mk hostLocal hostItems)) →
      denoteRegion model named env rels
        (ctx.fill (Region.spliceAt hostLocal hostItems material wireMap relationMap)) := by
  apply context_anti model named env rels hOdd
  intro holeEnv holeRelEnv hsplice
  exact Region.denote_spliceAt_host model named holeEnv holeRelEnv hostLocal
    hostItems material wireMap relationMap hsplice

/-- At even depth, a pointwise implication between replacement materials is
covariant through both the splice site and its enclosing diagram context. -/
theorem DiagramContext.fill_spliceAt_mono_even
    (ctx : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (source target : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hEven : ctx.cutDepth % 2 = 0)
    (entails : ∀ holeRelEnv patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) source →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) target) :
    denoteRegion model named env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems source wireMap relationMap)) →
      denoteRegion model named env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems target wireMap relationMap)) := by
  apply context_mono model named env rels hEven
  intro holeEnv holeRelEnv hsource
  exact Region.denote_spliceAt_mono model named holeEnv holeRelEnv hostLocal
    hostItems source target wireMap relationMap (entails holeRelEnv) hsource

/-- At odd depth, the same local material implication is consumed
contravariantly by the enclosing diagram context. -/
theorem DiagramContext.fill_spliceAt_mono_odd
    (ctx : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (source target : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (hOdd : ctx.cutDepth % 2 = 1)
    (entails : ∀ holeRelEnv patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) source →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) target) :
    denoteRegion model named env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems target wireMap relationMap)) →
      denoteRegion model named env rels
        (ctx.fill
          (Region.spliceAt hostLocal hostItems source wireMap relationMap)) := by
  apply context_anti model named env rels hOdd
  intro holeEnv holeRelEnv htarget
  exact Region.denote_spliceAt_mono model named holeEnv holeRelEnv hostLocal
    hostItems source target wireMap relationMap (entails holeRelEnv) htarget

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

@[simp] theorem ItemSeq.renameRelations_length :
    (items : ItemSeq signature wires source) →
    (rho : RelationRenaming source target) →
    (items.renameRelations rho).length = items.length
  | .nil, _ => rfl
  | .cons _ tail, rho =>
      congrArg Nat.succ (ItemSeq.renameRelations_length tail rho)

theorem ItemSeq.get_renameRelations
    : (items : ItemSeq signature wires source) →
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
    (items : ItemSeq signature source rels) :
    (items.castWiresEq equality).length = items.length := by
  subst target
  rfl

theorem ItemSeq.get_castWiresEq (equality : source = target)
    (items : ItemSeq signature source rels) (index : Fin items.length) :
    (items.castWiresEq equality).get
        (Fin.cast (ItemSeq.castWiresEq_length equality items).symm index) =
      (items.get index).castWiresEq equality := by
  subst target
  rfl

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

/-- Renaming the relation context uniformly on both sides preserves an
intrinsic region isomorphism. -/
theorem RegionIso.renameRelations
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region signature sourceWires sourceRels}
    {target : Region signature targetWires sourceRels}
    (iso : RegionIso signature wire sourceRels source target)
    (rho : RelationRenaming sourceRels targetRels) :
    RegionIso signature wire targetRels
      (source.renameRelations rho) (target.renameRelations rho) := by
  exact RegionIso.rec
    (motive_1 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        RegionIso signature wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (motive_2 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        ItemIso signature wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (motive_3 := fun wire sourceRels source target _ =>
      ∀ {targetRels}, (rho : RelationRenaming sourceRels targetRels) →
        ItemSeqIso signature wire targetRels
          (source.renameRelations rho) (target.renameRelations rho))
    (fun {_ _ _ _} {_} {_} {_} {_} localEquiv _ itemsIH {_} rho =>
      RegionIso.mk localEquiv (itemsIH rho))
    (fun {_ _} {_} {_} {_} {_} {_} {_} output_eq term_eq {_} _ =>
      ItemIso.equation output_eq term_eq)
    (fun {_ _ _} {_} {_} relation {_} {_} arguments_eq {_} rho =>
      ItemIso.atom (rho relation) arguments_eq)
    (fun {_ _ _} {_} {_} relation {_} {_} arguments_eq {_} _ =>
      ItemIso.named relation arguments_eq)
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

/-- Pull a focused-frame presentation back across an ambient wire renaming of
its source sequence. -/
def ItemSeqIso.Frame.prependRenameWires
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
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
    have hsecond' : ItemIso signature secondWire rels
        ((source.get index).renameWires firstWire)
        (target.get (frame.positions (firstPositions index))) := by
      simpa only [firstPositions, ItemSeq.get_renameWires] using hsecond
    exact hfirst.trans hsecond'

/-- Push a focused-frame presentation forward across an ambient wire
renaming of its target sequence. -/
def ItemSeqIso.Frame.appendRenameWires
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
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
  have hlast' : ItemIso signature lastWire rels
      (target.get (frame.positions index))
      ((target.renameWires lastWire).get
        (lastPositions (frame.positions index))) := by
    simpa only [lastPositions, ItemSeq.get_renameWires] using hlast
  exact hfirst.trans hlast'

/-- Transport a focused-frame presentation through canonical source and
target wire presentations, preserving the distinguished position values. -/
theorem ItemSeqIso.Frame.pullPush
    {sourceWires middleSourceWires middleTargetWires targetWires : Nat}
    {rels : Theory.RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {middleSource : ItemSeq signature middleSourceWires rels}
    {middleTarget : ItemSeq signature middleTargetWires rels}
    {target : ItemSeq signature targetWires rels}
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
    ∃ sourceIndex : Fin source.length,
      ∃ targetIndex : Fin target.length,
        sourceIndex.val = middleSourceIndex.val ∧
        targetIndex.val = middleTargetIndex.val ∧
        Nonempty (ItemSeqIso.Frame finalWire sourceIndex targetIndex) := by
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
  exact ⟨sourceIndex, targetIndex, rfl, rfl, ⟨finalFrame⟩⟩

/-- An alignment between two single-hole contexts. Each enclosing frame owns
its complete occurrence permutation; the recursively aligned child supplies
only the distinguished cut/bubble item. This permits siblings to move across
the focused position. -/
inductive DiagramContextIso (signature : List Nat) :
    {sourceOuter sourceHole targetOuter targetHole : Nat} →
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)) →
    (holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)) →
    (outerRels holeRels : Theory.RelCtx) →
    DiagramContext signature sourceOuter sourceHole outerRels holeRels →
    DiagramContext signature targetOuter targetHole outerRels holeRels → Prop
  | hole
      (wire : FiniteEquiv (Fin wires) (Fin targetWires)) :
      DiagramContextIso signature wire wire rels rels
        (.hole : DiagramContext signature wires wires rels rels)
        (.hole : DiagramContext signature targetWires targetWires rels rels)
  | cut
      {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
      {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
      (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
      (sourceBefore sourceAfter :
        ItemSeq signature (sourceOuter + sourceLocal) outerRels)
      (targetBefore targetAfter :
        ItemSeq signature (targetOuter + targetLocal) outerRels)
      (sourceChild : DiagramContext signature
        (sourceOuter + sourceLocal) sourceHole outerRels holeRels)
      (targetChild : DiagramContext signature
        (targetOuter + targetLocal) targetHole outerRels holeRels)
      (child : DiagramContextIso signature
        (extendWireEquiv outerWire localWire) holeWire outerRels holeRels
        sourceChild targetChild)
      (frame : ∀ {sourceBody : Region signature
          (sourceOuter + sourceLocal) outerRels}
          {targetBody : Region signature
            (targetOuter + targetLocal) outerRels},
        ItemIso signature (extendWireEquiv outerWire localWire) outerRels
            (.cut sourceBody) (.cut targetBody) →
          ItemSeqIso signature (extendWireEquiv outerWire localWire) outerRels
            (sourceBefore.append (.cons (.cut sourceBody) sourceAfter))
            (targetBefore.append (.cons (.cut targetBody) targetAfter))) :
      DiagramContextIso signature outerWire holeWire outerRels holeRels
        (.cut sourceLocal sourceBefore sourceAfter sourceChild)
        (.cut targetLocal targetBefore targetAfter targetChild)
  | bubble
      {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
      {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
      (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
      (sourceBefore sourceAfter :
        ItemSeq signature (sourceOuter + sourceLocal) outerRels)
      (targetBefore targetAfter :
        ItemSeq signature (targetOuter + targetLocal) outerRels)
      (sourceChild : DiagramContext signature
        (sourceOuter + sourceLocal) sourceHole (arity :: outerRels) holeRels)
      (targetChild : DiagramContext signature
        (targetOuter + targetLocal) targetHole (arity :: outerRels) holeRels)
      (child : DiagramContextIso signature
        (extendWireEquiv outerWire localWire) holeWire
        (arity :: outerRels) holeRels sourceChild targetChild)
      (frame : ∀ {sourceBody : Region signature
          (sourceOuter + sourceLocal) (arity :: outerRels)}
          {targetBody : Region signature
            (targetOuter + targetLocal) (arity :: outerRels)},
        ItemIso signature (extendWireEquiv outerWire localWire) outerRels
            (.bubble arity sourceBody) (.bubble arity targetBody) →
          ItemSeqIso signature (extendWireEquiv outerWire localWire) outerRels
            (sourceBefore.append
              (.cons (.bubble arity sourceBody) sourceAfter))
            (targetBefore.append
              (.cons (.bubble arity targetBody) targetAfter))) :
      DiagramContextIso signature outerWire holeWire outerRels holeRels
        (.bubble sourceLocal sourceBefore sourceAfter arity sourceChild)
        (.bubble targetLocal targetBefore targetAfter arity targetChild)

/-- Isomorphic single-hole contexts have the same number of enclosing cuts.
The occurrence permutations and wire transports carried by the isomorphism
do not affect polarity. -/
theorem DiagramContextIso.cutDepth_eq
    (iso : DiagramContextIso signature outerWire holeWire outerRels holeRels
      source target) :
    source.cutDepth = target.cutDepth := by
  induction iso <;> simp_all [DiagramContext.cutDepth]

/-- Transporting only the relation-context index leaves context polarity
unchanged. -/
theorem DiagramContext.cutDepth_castRels
    {sourceRels targetRels : Theory.RelCtx}
    {outerWires holeWires : Nat} {outerRels : Theory.RelCtx}
    (equality : sourceRels = targetRels)
    (context : DiagramContext signature outerWires holeWires outerRels
      sourceRels) :
    (equality ▸ context).cutDepth = context.cutDepth := by
  subst targetRels
  rfl

/-- Build one aligned cut-context layer from the recursively aligned child
and the compiler's permutation of every nonfocused sibling. -/
theorem DiagramContextIso.cutFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceItems : ItemSeq signature (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq signature (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (sourceFocus : ItemSeq.Focus sourceItems)
    (targetFocus : ItemSeq.Focus targetItems)
    (sourceAt : sourceItems.focusAt? sourceIndex.val = some sourceFocus)
    (targetAt : targetItems.focusAt? targetIndex.val = some targetFocus)
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    (sourceChild : DiagramContext signature
      (sourceOuter + sourceLocal) sourceHole outerRels holeRels)
    (targetChild : DiagramContext signature
      (targetOuter + targetLocal) targetHole outerRels holeRels)
    (child : DiagramContextIso signature
      (extendWireEquiv outerWire localWire) holeWire outerRels holeRels
      sourceChild targetChild) :
    DiagramContextIso signature outerWire holeWire outerRels holeRels
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
theorem DiagramContextIso.bubbleFrame
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    {sourceItems : ItemSeq signature (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq signature (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (sourceFocus : ItemSeq.Focus sourceItems)
    (targetFocus : ItemSeq.Focus targetItems)
    (sourceAt : sourceItems.focusAt? sourceIndex.val = some sourceFocus)
    (targetAt : targetItems.focusAt? targetIndex.val = some targetFocus)
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    (sourceChild : DiagramContext signature
      (sourceOuter + sourceLocal) sourceHole (arity :: outerRels) holeRels)
    (targetChild : DiagramContext signature
      (targetOuter + targetLocal) targetHole (arity :: outerRels) holeRels)
    (child : DiagramContextIso signature
      (extendWireEquiv outerWire localWire) holeWire
      (arity :: outerRels) holeRels sourceChild targetChild) :
    DiagramContextIso signature outerWire holeWire outerRels holeRels
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

/-- A site isomorphism lifts through every aligned compiler frame to the
complete root. -/
theorem DiagramContextIso.fill
    (alignment : DiagramContextIso signature outerWire holeWire
      outerRels holeRels sourceContext targetContext)
    (site : RegionIso signature holeWire holeRels sourceSite targetSite) :
    RegionIso signature outerWire outerRels
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
theorem DiagramContextIso.root
    {sourceRoot : Region signature sourceOuter outerRels}
    {targetRoot : Region signature targetOuter outerRels}
    {sourceContext : DiagramContext signature sourceOuter sourceHole
      outerRels holeRels}
    {targetContext : DiagramContext signature targetOuter targetHole
      outerRels holeRels}
    {sourceSite : Region signature sourceHole holeRels}
    {targetSite : Region signature targetHole holeRels}
    (alignment : DiagramContextIso signature outerWire holeWire
      outerRels holeRels sourceContext targetContext)
    (site : RegionIso signature holeWire holeRels sourceSite targetSite)
    (sourceRebuild : sourceContext.fill sourceSite = sourceRoot)
    (targetRebuild : targetContext.fill targetSite = targetRoot) :
    RegionIso signature outerWire outerRels sourceRoot targetRoot := by
  rw [← sourceRebuild, ← targetRebuild]
  exact alignment.fill site

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
