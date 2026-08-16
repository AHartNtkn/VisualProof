import VisualProof.Diagram.IdentityOwner

namespace VisualProof.Diagram

private abbrev AppendConsInjMotive
    (wires : List Theory.Sig) (beforeLeft : ItemSeq wires) :=
  ∀ {beforeRight : ItemSeq wires}
    {selectedLeft selectedRight : Item wires}
    {afterLeft afterRight : ItemSeq wires},
    beforeLeft.length = beforeRight.length →
    beforeLeft.append (.cons selectedLeft afterLeft) =
      beforeRight.append (.cons selectedRight afterRight) →
    beforeLeft = beforeRight ∧
      selectedLeft = selectedRight ∧ afterLeft = afterRight

private theorem appendConsInjNil : AppendConsInjMotive wires .nil := by
  intro beforeRight selectedLeft selectedRight afterLeft afterRight
    length_eq sequence_eq
  cases beforeRight with
  | nil =>
      simp only [ItemSeq.append] at sequence_eq
      cases sequence_eq
      exact ⟨rfl, rfl, rfl⟩
  | cons head tail => simp [ItemSeq.length] at length_eq

private theorem appendConsInjCons
    (head : Item wires) (tail : ItemSeq wires)
    (_ : True) (induction : AppendConsInjMotive wires tail) :
    AppendConsInjMotive wires (.cons head tail) := by
  intro beforeRight selectedLeft selectedRight afterLeft afterRight
    length_eq sequence_eq
  cases beforeRight with
  | nil => simp [ItemSeq.length] at length_eq
  | cons headRight tailRight =>
      have tail_length_eq : tail.length = tailRight.length :=
        Nat.succ.inj length_eq
      simp only [ItemSeq.append] at sequence_eq
      have head_eq := ItemSeq.cons.inj sequence_eq |>.1
      have tail_eq := ItemSeq.cons.inj sequence_eq |>.2
      subst headRight
      obtain ⟨before_eq, selected_eq, after_eq⟩ :=
        induction tail_length_eq tail_eq
      subst tailRight
      exact ⟨rfl, selected_eq, after_eq⟩

private theorem ItemSeq.append_cons_inj_of_length_eq
    {beforeLeft beforeRight : ItemSeq wires}
    {selectedLeft selectedRight : Item wires}
    {afterLeft afterRight : ItemSeq wires}
    (length_eq : beforeLeft.length = beforeRight.length)
    (sequence_eq :
      beforeLeft.append (.cons selectedLeft afterLeft) =
        beforeRight.append (.cons selectedRight afterRight)) :
    beforeLeft = beforeRight ∧
      selectedLeft = selectedRight ∧ afterLeft = afterRight :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := AppendConsInjMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    appendConsInjNil appendConsInjCons beforeLeft length_eq sequence_eq

/-- An exact factorization of one recursive context through another. -/
structure DiagramContext.Factor
    (ancestor : DiagramContext outer middle)
    (descendant : DiagramContext outer holeWires)
    (ancestorBody : Region middle) (descendantBody : Region holeWires) where
  suffix : DiagramContext middle holeWires
  comp_eq : ancestor.comp suffix = descendant
  fill_eq : suffix.fill descendantBody = ancestorBody

private theorem DiagramContext.factor_of_fill_eq
    (ancestor : DiagramContext outer middle)
    (descendant : DiagramContext outer holeWires)
    (ancestorBody : Region middle) (descendantBody : Region holeWires)
    (fill_eq : ancestor.fill ancestorBody =
      descendant.fill descendantBody)
    (path_prefix : ∃ suffix,
      descendant.path = ancestor.path ++ suffix) :
    Nonempty (ancestor.Factor descendant ancestorBody descendantBody) := by
  induction ancestor generalizing holeWires with
  | hole => exact ⟨{
      suffix := descendant
      comp_eq := rfl
      fill_eq := fill_eq.symm
    }⟩
  | @cut currentOuter currentMiddle ancestorLocals ancestorBefore
      ancestorAfter ancestorChild induction =>
      cases descendant with
      | hole =>
          obtain ⟨suffix, path_eq⟩ := path_prefix
          simp [DiagramContext.path] at path_eq
      | @cut _ descendantMiddle descendantLocals descendantBefore
          descendantAfter descendantChild =>
          simp only [DiagramContext.fill] at fill_eq
          have locals_eq := Region.mk.inj fill_eq |>.1
          subst descendantLocals
          have items_eq := Region.mk.inj fill_eq |>.2
          obtain ⟨pathSuffix, path_eq⟩ := path_prefix
          simp only [DiagramContext.path, List.cons_append] at path_eq
          have head_eq := List.cons.inj path_eq |>.1
          have tail_prefix := List.cons.inj path_eq |>.2
          obtain ⟨before_eq, selected_eq, after_eq⟩ :=
            ItemSeq.append_cons_inj_of_length_eq
              (beforeLeft := ancestorBefore)
              (beforeRight := descendantBefore)
              (selectedLeft := .cut (ancestorChild.fill ancestorBody))
              (selectedRight := .cut (descendantChild.fill descendantBody))
              (afterLeft := ancestorAfter) (afterRight := descendantAfter)
              head_eq.symm (eq_of_heq items_eq)
          subst descendantBefore
          subst descendantAfter
          have bodies_eq := Item.cut.inj selected_eq
          obtain ⟨childFactor⟩ := induction descendantChild
            ancestorBody descendantBody bodies_eq
            ⟨pathSuffix, tail_prefix⟩
          exact ⟨{
            suffix := childFactor.suffix
            comp_eq := by
              simp only [DiagramContext.comp]
              rw [childFactor.comp_eq]
            fill_eq := childFactor.fill_eq
          }⟩

theorem Region.IdentityOccurrence.Owner.factor
    {region : Region outer}
    (ancestor descendant : Region.IdentityOccurrence region)
    (path_prefix : ∃ suffix,
      descendant.path = ancestor.path ++ suffix) :
    Nonempty (ancestor.owner.context.Factor descendant.owner.context
      (.mk ancestor.owner.ownerLocals ancestor.owner.ownerItems)
      (.mk descendant.owner.ownerLocals descendant.owner.ownerItems)) := by
  apply DiagramContext.factor_of_fill_eq
    ancestor.owner.context descendant.owner.context
    (.mk ancestor.owner.ownerLocals ancestor.owner.ownerItems)
    (.mk descendant.owner.ownerLocals descendant.owner.ownerItems)
  · rw [ancestor.owner.source_eq, descendant.owner.source_eq]
  · rw [ancestor.owner.path_eq, descendant.owner.path_eq]
    exact path_prefix

end VisualProof.Diagram
