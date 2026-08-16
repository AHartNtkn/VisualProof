import VisualProof.Diagram.FocusIsomorphism

namespace VisualProof.Diagram

open VisualProof.Theory

private abbrev GetAppendMotive
    (wires : List Sig) (before : ItemSeq wires) :=
  ∀ (selected : Item wires) (after : ItemSeq wires),
    (before.append (.cons selected after)).get
      ⟨before.length, by simp [ItemSeq.length_append, ItemSeq.length]⟩ = selected

private theorem getAppendNil : GetAppendMotive wires .nil := by
  intro selected after
  simp [ItemSeq.length, ItemSeq.get]

private theorem getAppendCons
    (head : Item wires) (tail : ItemSeq wires)
    (_ : True) (induction : GetAppendMotive wires tail) :
    GetAppendMotive wires (.cons head tail) := by
  intro selected after
  simp only [ItemSeq.append, ItemSeq.length, ItemSeq.get]
  exact induction selected after

private theorem ItemSeq.get_append_cons_length
    (before : ItemSeq wires) (selected : Item wires)
    (after : ItemSeq wires) :
    (before.append (.cons selected after)).get
      ⟨before.length, by simp [ItemSeq.length_append, ItemSeq.length]⟩ =
      selected :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := GetAppendMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    getAppendNil getAppendCons before selected after

private theorem ItemSeq.Focus.item_eq_get
    {items : ItemSeq wires} (focus : ItemSeq.Focus items) :
    focus.item = items.get
      ⟨focus.before.length, by
        have length_eq := congrArg ItemSeq.length focus.rebuild
        simp only [ItemSeq.length_append, ItemSeq.length] at length_eq
        omega⟩ := by
  cases focus with
  | mk before selected after rebuild =>
      subst items
      exact (ItemSeq.get_append_cons_length before selected after).symm

private def ItemIso.target_of_cut
    {sourceBody : Region sourceWires} {targetItem : Item targetWires}
    (iso : ItemIso ambient (.cut sourceBody) targetItem) :
    Σ targetBody, PLift (targetItem = .cut targetBody) ×
      RegionIso ambient sourceBody targetBody := by
  cases iso with
  | cut body => exact ⟨_, ⟨rfl⟩, body⟩

/-- Transport an exact recursive hole through a region isomorphism. The
result follows the item permutation and returns the corresponding target
context together with the focused-body isomorphism. -/
structure RegionIso.ContextAlignment
    {sourceOuter targetOuter holeWires : List Sig}
    {ambient : WireEquiv sourceOuter targetOuter}
    {context : DiagramContext sourceOuter holeWires}
    {body : Region holeWires} {target : Region targetOuter}
    (iso : RegionIso ambient (context.fill body) target) where
  targetHoleWires : List Sig
  holeEquiv : WireEquiv holeWires targetHoleWires
  targetBody : Region targetHoleWires
  targetContext : DiagramContext targetOuter targetHoleWires
  target_eq : targetContext.fill targetBody = target
  bodyIso : RegionIso holeEquiv body targetBody

noncomputable def RegionIso.alignContext
    {sourceOuter targetOuter holeWires : List Sig}
    {ambient : WireEquiv sourceOuter targetOuter}
    (context : DiagramContext sourceOuter holeWires)
    (body : Region holeWires) {target : Region targetOuter}
    (iso : RegionIso ambient (context.fill body) target) :
    iso.ContextAlignment := by
  induction context generalizing targetOuter with
  | hole =>
      exact {
        targetHoleWires := targetOuter
        holeEquiv := ambient
        targetBody := target
        targetContext := .hole
        target_eq := rfl
        bodyIso := iso
      }
  | @cut currentOuter currentHole locals before after child induction =>
      cases iso with
      | @mk _ _ _ targetLocals _ targetItems _ localEquiv itemsIso =>
          cases itemsIso with
          | @permute sourceWires targetWires itemsAmbient sourceItems
              alignedItems positions itemIsos =>
              let sourceFocus : ItemSeq.Focus
                  (before.append (.cons (.cut (child.fill body)) after)) := {
                before := before
                item := .cut (child.fill body)
                after := after
                rebuild := rfl
              }
              let sourceIndex : Fin
                  (before.append (.cons (.cut (child.fill body)) after)).length :=
                ⟨before.length, by
                  simp [ItemSeq.length_append, ItemSeq.length]⟩
              let targetIndex := positions sourceIndex
              let targetFocus := ItemSeq.focusAt _ targetIndex
              have sourceItem := sourceFocus.item_eq_get
              have targetItem := ItemSeq.focusAt_item_eq_get _ targetIndex
              have distinguished := itemIsos sourceIndex targetIndex rfl
              rw [← sourceItem, ← targetItem] at distinguished
              obtain ⟨targetChild, ⟨targetIsCut⟩, childIso⟩ :=
                ItemIso.target_of_cut distinguished
              let aligned := induction body childIso
              exact {
                targetHoleWires := aligned.targetHoleWires
                holeEquiv := aligned.holeEquiv
                targetBody := aligned.targetBody
                targetContext :=
                  .cut targetLocals targetFocus.before targetFocus.after
                    aligned.targetContext
                target_eq := by
                  simp only [DiagramContext.fill]
                  rw [aligned.target_eq, ← targetIsCut,
                    targetFocus.rebuild]
                bodyIso := aligned.bodyIso
              }

end VisualProof.Diagram
