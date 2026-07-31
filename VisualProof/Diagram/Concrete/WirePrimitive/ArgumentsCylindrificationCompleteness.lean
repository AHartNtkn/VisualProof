import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationSemantics

namespace VisualProof.ConcreteWirePrimitive.ArgumentsSemantics

open WirePrimitive

private theorem wireRenaming_ext_local
    (left right : WireRenaming source target)
    (pointwise :
      ∀ {signature} (value : Var source signature),
        left value = right value) :
    (@left) = @right := by
  apply @funext Sig (fun signature =>
    Var source signature → Var target signature)
  intro signature
  funext value
  exact @pointwise signature value

private theorem list_snoc_induction
    {motive : List α → Prop}
    (nil : motive [])
    (snoc : ∀ values value, motive values → motive (values ++ [value])) :
    ∀ values, motive values := by
  intro values
  have reversed : ∀ reversed : List α, motive reversed.reverse := by
    intro reversed
    induction reversed with
    | nil => exact nil
    | cons value rest induction =>
        rw [List.reverse_cons]
        exact snoc rest.reverse value induction
  simpa using reversed values.reverse

private theorem peel_shape_base_smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (items : CylindricalShapeItemSeq definitions insertion context largerContext)
    (holes : List (Vars context smallerArguments)) :
    (peelArgumentShape
      (.mk items.smaller ⟨holes⟩ :
        UniformIntrinsicRegion definitions smallerArguments context)).bound = [] := by
  cases items with
  | nil embedding => rfl
  | cons head tail =>
      cases head <;> rfl

private theorem peel_shape_base_larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (items : CylindricalShapeItemSeq definitions insertion smallerContext context)
    (holes : List (Vars context largerArguments)) :
    (peelArgumentShape
      (.mk items.larger ⟨holes⟩ :
        UniformIntrinsicRegion definitions largerArguments context)).bound = [] := by
  cases items with
  | nil embedding => rfl
  | cons head tail =>
      cases head <;> rfl

private theorem transport_shape_body_smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (same : left = right)
    (items : CylindricalShapeItemSeq definitions insertion left largerContext)
    (holes : List (Vars left smallerArguments)) :
    same ▸
        (.mk items.smaller ⟨holes⟩ :
          UniformIntrinsicRegion definitions smallerArguments left) =
      (.mk (same ▸ items).smaller ⟨same ▸ holes⟩ :
        UniformIntrinsicRegion definitions smallerArguments right) := by
  cases same
  rfl

private theorem transport_uniform_shape
    (same : left = right)
    (items : UniformIntrinsicItemSeq definitions arguments left)
    (holes : List (Vars left arguments)) :
    same ▸
        (.mk items ⟨holes⟩ :
          UniformIntrinsicRegion definitions arguments left) =
      (.mk (same ▸ items) ⟨same ▸ holes⟩ :
        UniformIntrinsicRegion definitions arguments right) := by
  cases same
  rfl

private theorem uniform_shape_items_injective
    {left right : UniformIntrinsicItemSeq definitions arguments context}
    {leftHoles rightHoles : List (Vars context arguments)}
    (same :
      (.mk left ⟨leftHoles⟩ :
        UniformIntrinsicRegion definitions arguments context) =
      .mk right ⟨rightHoles⟩) :
    left = right := by
  cases same
  rfl

private theorem uniform_shape_holes_injective
    {left right : UniformIntrinsicItemSeq definitions arguments context}
    {leftHoles rightHoles : List (Vars context arguments)}
    (same :
      (.mk left ⟨leftHoles⟩ :
        UniformIntrinsicRegion definitions arguments context) =
      .mk right ⟨rightHoles⟩) :
    leftHoles = rightHoles := by
  cases same
  rfl

private theorem wrapArgumentBind_injective
    (signature : Sig) :
    Function.Injective
      (wrapArgumentBind (definitions := definitions)
        (arguments := arguments) (outer := outer) signature) := by
  intro left right same
  cases left with
  | mk leftItems leftHoles =>
      cases right with
      | mk rightItems rightHoles =>
          simp only [wrapArgumentBind] at same
          cases same
          rfl

private theorem wrapArgumentBinds_injective
    (bound : List Sig) :
    Function.Injective
      (wrapArgumentBinds (definitions := definitions)
        (arguments := arguments) (outer := outer) bound) := by
  induction bound generalizing outer with
  | nil =>
      intro left right same
      exact same
  | cons signature rest induction =>
      intro left right same
      apply wrapArgumentBind_injective signature
      exact induction same

private theorem peeled_body_exact
    {shape : UniformIntrinsicRegion definitions arguments outer}
    (peeled : PeeledArgumentShape shape)
    (bound : List Sig)
    (body : UniformIntrinsicRegion definitions arguments (bound ++ outer))
    (shapeExact : shape = wrapArgumentBinds bound body)
    (boundExact : peeled.bound = bound) :
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions arguments
            (peeled.bound ++ outer)) = body := by
  cases boundExact
  apply wrapArgumentBinds_injective peeled.bound
  exact peeled.exact.symm.trans shapeExact

private theorem PeeledArgumentShape.ext_local
    {shape : UniformIntrinsicRegion definitions arguments outer}
    (left right : PeeledArgumentShape shape)
    (boundExact : left.bound = right.bound)
    (itemsExact :
      congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
          left.items = right.items)
    (holesExact :
      congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
          left.holes = right.holes) :
    left = right := by
  cases left with
  | mk leftBound leftItems leftHoles leftExact =>
      cases right with
      | mk rightBound rightItems rightHoles rightExact =>
          cases boundExact
          cases itemsExact
          cases holesExact
          rfl

private theorem peel_wrap_shape_smaller_bound
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    (peelArgumentShape
        (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))).bound =
      bound := by
  let motive : List Sig → Prop := fun current =>
    ∀ (currentOuter : List Sig)
      (currentItems : CylindricalShapeItemSeq definitions insertion
        (current ++ currentOuter) largerContext)
      (currentHoles :
        List (Vars (current ++ currentOuter) smallerArguments)),
      (peelArgumentShape
          (wrapArgumentBinds current
            (.mk currentItems.smaller ⟨currentHoles⟩))).bound = current
  apply (list_snoc_induction (motive := motive) ?_ ?_ bound outer items holes)
  · intro currentOuter currentItems currentHoles
    cases currentItems with
    | nil embedding => rfl
    | cons head tail => cases head <;> rfl
  · intro xs sig hprev currentOuter currentItems currentHoles
    rw [wrapArgumentBinds_append]
    let associated := List.append_assoc xs [sig] currentOuter
    let transportedItems :
        CylindricalShapeItemSeq definitions insertion
          (xs ++ sig :: currentOuter) largerContext :=
      associated ▸ currentItems
    let transportedHoles :
        List (Vars (xs ++ sig :: currentOuter) smallerArguments) :=
      associated ▸ currentHoles
    have transportedBody :
        associated ▸
            (.mk currentItems.smaller ⟨currentHoles⟩ :
              UniformIntrinsicRegion definitions smallerArguments
                ((xs ++ [sig]) ++ currentOuter)) =
          (.mk transportedItems.smaller ⟨transportedHoles⟩ :
            UniformIntrinsicRegion definitions smallerArguments
              (xs ++ sig :: currentOuter)) :=
      transport_shape_body_smaller associated currentItems currentHoles
    have innerBound :=
      hprev (sig :: currentOuter) transportedItems transportedHoles
    have associatedExact :
        (List.append_assoc xs [sig] currentOuter) = associated :=
      Subsingleton.elim _ _
    rw [associatedExact, transportedBody]
    change
      (let peeled := peelArgumentShape
          (wrapArgumentBinds xs
            (.mk transportedItems.smaller ⟨transportedHoles⟩))
       peeled.bound ++ [sig]) = xs ++ [sig]
    dsimp only
    exact congrArg (fun values => values ++ [sig]) innerBound

private theorem peel_wrap_shape_smaller_body
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_smaller_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions smallerArguments
            (peeled.bound ++ outer)) =
      (.mk items.smaller ⟨holes⟩ :
        UniformIntrinsicRegion definitions smallerArguments
          (bound ++ outer)) := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
  have boundExact : peeled.bound = bound :=
    peel_wrap_shape_smaller_bound bound items holes
  exact peeled_body_exact peeled bound
    (.mk items.smaller ⟨holes⟩) rfl boundExact

private theorem peel_wrap_shape_smaller_items
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_smaller_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        peeled.items = items.smaller := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
  let boundExact : peeled.bound = bound :=
    peel_wrap_shape_smaller_bound bound items holes
  have bodyExact := peel_wrap_shape_smaller_body bound items holes
  change
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions smallerArguments
            (peeled.bound ++ outer)) =
      (.mk items.smaller ⟨holes⟩ :
        UniformIntrinsicRegion definitions smallerArguments
          (bound ++ outer)) at bodyExact
  have transported := transport_uniform_shape
    (congrArg (fun localSigs => localSigs ++ outer) boundExact)
    peeled.items peeled.holes
  rw [transported] at bodyExact
  exact uniform_shape_items_injective bodyExact

private theorem peel_wrap_shape_smaller_holes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_smaller_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        peeled.holes = holes := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩))
  let boundExact : peeled.bound = bound :=
    peel_wrap_shape_smaller_bound bound items holes
  have bodyExact := peel_wrap_shape_smaller_body bound items holes
  change
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions smallerArguments
            (peeled.bound ++ outer)) =
      (.mk items.smaller ⟨holes⟩ :
        UniformIntrinsicRegion definitions smallerArguments
          (bound ++ outer)) at bodyExact
  have transported := transport_uniform_shape
    (congrArg (fun localSigs => localSigs ++ outer) boundExact)
    peeled.items peeled.holes
  rw [transported] at bodyExact
  exact uniform_shape_holes_injective bodyExact

private theorem transport_shape_body_larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (same : left = right)
    (items : CylindricalShapeItemSeq definitions insertion smallerContext left)
    (holes : List (Vars left largerArguments)) :
    same ▸
        (.mk items.larger ⟨holes⟩ :
          UniformIntrinsicRegion definitions largerArguments left) =
      (.mk (same ▸ items).larger ⟨same ▸ holes⟩ :
        UniformIntrinsicRegion definitions largerArguments right) := by
  cases same
  rfl

private theorem peel_wrap_shape_larger_bound
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    (peelArgumentShape
        (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))).bound =
      bound := by
  let motive : List Sig → Prop := fun current =>
    ∀ (currentOuter : List Sig)
      (currentItems : CylindricalShapeItemSeq definitions insertion
        smallerContext (current ++ currentOuter))
      (currentHoles :
        List (Vars (current ++ currentOuter) largerArguments)),
      (peelArgumentShape
          (wrapArgumentBinds current
            (.mk currentItems.larger ⟨currentHoles⟩))).bound = current
  apply (list_snoc_induction (motive := motive) ?_ ?_ bound outer items holes)
  · intro currentOuter currentItems currentHoles
    cases currentItems with
    | nil embedding => rfl
    | cons head tail => cases head <;> rfl
  · intro xs sig hprev currentOuter currentItems currentHoles
    rw [wrapArgumentBinds_append]
    let associated := List.append_assoc xs [sig] currentOuter
    let transportedItems :
        CylindricalShapeItemSeq definitions insertion smallerContext
          (xs ++ sig :: currentOuter) :=
      associated ▸ currentItems
    let transportedHoles :
        List (Vars (xs ++ sig :: currentOuter) largerArguments) :=
      associated ▸ currentHoles
    have transportedBody :
        associated ▸
            (.mk currentItems.larger ⟨currentHoles⟩ :
              UniformIntrinsicRegion definitions largerArguments
                ((xs ++ [sig]) ++ currentOuter)) =
          (.mk transportedItems.larger ⟨transportedHoles⟩ :
            UniformIntrinsicRegion definitions largerArguments
              (xs ++ sig :: currentOuter)) :=
      transport_shape_body_larger associated currentItems currentHoles
    have innerBound :=
      hprev (sig :: currentOuter) transportedItems transportedHoles
    have associatedExact :
        (List.append_assoc xs [sig] currentOuter) = associated :=
      Subsingleton.elim _ _
    rw [associatedExact, transportedBody]
    change
      (let peeled := peelArgumentShape
          (wrapArgumentBinds xs
            (.mk transportedItems.larger ⟨transportedHoles⟩))
       peeled.bound ++ [sig]) = xs ++ [sig]
    dsimp only
    exact congrArg (fun values => values ++ [sig]) innerBound

private theorem peel_wrap_shape_larger_body
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_larger_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions largerArguments
            (peeled.bound ++ outer)) =
      (.mk items.larger ⟨holes⟩ :
        UniformIntrinsicRegion definitions largerArguments
          (bound ++ outer)) := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
  have boundExact : peeled.bound = bound :=
    peel_wrap_shape_larger_bound bound items holes
  exact peeled_body_exact peeled bound
    (.mk items.larger ⟨holes⟩) rfl boundExact

private theorem peel_wrap_shape_larger_items
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_larger_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        peeled.items = items.larger := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
  let boundExact : peeled.bound = bound :=
    peel_wrap_shape_larger_bound bound items holes
  have bodyExact := peel_wrap_shape_larger_body bound items holes
  change
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions largerArguments
            (peeled.bound ++ outer)) =
      (.mk items.larger ⟨holes⟩ :
        UniformIntrinsicRegion definitions largerArguments
          (bound ++ outer)) at bodyExact
  have transported := transport_uniform_shape
    (congrArg (fun localSigs => localSigs ++ outer) boundExact)
    peeled.items peeled.holes
  rw [transported] at bodyExact
  exact uniform_shape_items_injective bodyExact

private theorem peel_wrap_shape_larger_holes
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    let peeled := peelArgumentShape
      (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
    let boundExact : peeled.bound = bound :=
      peel_wrap_shape_larger_bound bound items holes
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        peeled.holes = holes := by
  dsimp only
  let peeled := peelArgumentShape
    (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩))
  let boundExact : peeled.bound = bound :=
    peel_wrap_shape_larger_bound bound items holes
  have bodyExact := peel_wrap_shape_larger_body bound items holes
  change
    congrArg (fun localSigs => localSigs ++ outer) boundExact ▸
        (.mk peeled.items ⟨peeled.holes⟩ :
          UniformIntrinsicRegion definitions largerArguments
            (peeled.bound ++ outer)) =
      (.mk items.larger ⟨holes⟩ :
        UniformIntrinsicRegion definitions largerArguments
          (bound ++ outer)) at bodyExact
  have transported := transport_uniform_shape
    (congrArg (fun localSigs => localSigs ++ outer) boundExact)
    peeled.items peeled.holes
  rw [transported] at bodyExact
  exact uniform_shape_holes_injective bodyExact

private def expectedPeeledSmaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    PeeledArgumentShape
      (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩)) :=
  { bound := bound
    items := items.smaller
    holes := holes
    exact := rfl }

private theorem peel_wrap_shape_smaller
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      (bound ++ outer) largerContext)
    (holes : List (Vars (bound ++ outer) smallerArguments)) :
    peelArgumentShape
        (wrapArgumentBinds bound (.mk items.smaller ⟨holes⟩)) =
      expectedPeeledSmaller bound items holes := by
  let boundExact := peel_wrap_shape_smaller_bound bound items holes
  exact PeeledArgumentShape.ext_local _ _ boundExact
    (peel_wrap_shape_smaller_items bound items holes)
    (peel_wrap_shape_smaller_holes bound items holes)

private def expectedPeeledLarger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    PeeledArgumentShape
      (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩)) :=
  { bound := bound
    items := items.larger
    holes := holes
    exact := rfl }

private theorem peel_wrap_shape_larger
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (bound : List Sig)
    (items : CylindricalShapeItemSeq definitions insertion
      smallerContext (bound ++ outer))
    (holes : List (Vars (bound ++ outer) largerArguments)) :
    peelArgumentShape
        (wrapArgumentBinds bound (.mk items.larger ⟨holes⟩)) =
      expectedPeeledLarger bound items holes := by
  let boundExact := peel_wrap_shape_larger_bound bound items holes
  exact PeeledArgumentShape.ext_local _ _ boundExact
    (peel_wrap_shape_larger_items bound items holes)
    (peel_wrap_shape_larger_holes bound items holes)

private theorem findSome?_complete
    {values : List α}
    {selected : α}
    (member : selected ∈ values)
    {choose : α → Option β}
    {result : β}
    (accepted : choose selected = some result) :
    ∃ found, values.findSome? choose = some found := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      unfold List.findSome?
      cases chosen : choose head with
      | some found => exact ⟨found, rfl⟩
      | none =>
          rcases member with same | member
          · subst selected
            rw [chosen] at accepted
            contradiction
          · exact induction member

private theorem checkCylindricalShapeFuel_block_complete
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (outer : WireRenaming smallerOuter largerOuter)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (items : CylindricalShapeItemSeq definitions insertion
      (smallerBound ++ smallerOuter) (largerBound ++ largerOuter))
    (holes : CylindricalHoles insertion bounds outer smallerHoles largerHoles)
    (fuel : Nat)
    (itemsAccepted :
      ∃ checked,
        checkCylindricalShapeItemSeqFuel fuel insertion
            (bounds.embed outer) items.smaller items.larger = some checked) :
    ∃ checked,
      checkCylindricalShapeFuel (fuel + 1) insertion outer
          (CylindricalShape.block outer bounds items holes).smaller
          (CylindricalShape.block outer bounds items holes).larger =
        some checked := by
  obtain ⟨checkedItems, itemsEquation⟩ := itemsAccepted
  change ∃ checked,
    checkCylindricalShapeFromPeeled insertion outer
        (CylindricalShape.block outer bounds items holes).smaller
        (CylindricalShape.block outer bounds items holes).larger
        (peelArgumentShape
          (CylindricalShape.block outer bounds items holes).smaller)
        (peelArgumentShape
          (CylindricalShape.block outer bounds items holes).larger)
        (fun inner =>
          checkCylindricalShapeItemSeqFuel fuel insertion inner) =
      some checked
  simp only [CylindricalShape.smaller, CylindricalShape.larger]
  rw [peel_wrap_shape_smaller, peel_wrap_shape_larger]
  unfold checkCylindricalShapeFromPeeled
  apply findSome?_complete (BoundCylindrification.mem_candidates bounds)
  simp only [expectedPeeledSmaller, expectedPeeledLarger]
  simp [itemsEquation, checkCylindricalHoles_complete holes]
  rfl

mutual

private def shapeReceiptFuel :
    CylindricalShape definitions insertion smallerContext largerContext → Nat
  | .block _ _ items _ => shapeItemSeqReceiptFuel items + 1

private def shapeItemReceiptFuel :
    CylindricalShapeItem definitions insertion smallerContext largerContext → Nat
  | .leaf _ _ _ _ => 1
  | .cut body => shapeReceiptFuel body + 1

private def shapeItemSeqReceiptFuel :
    CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext → Nat
  | .nil _ => 1
  | .cons head tail =>
      shapeItemReceiptFuel head + shapeItemSeqReceiptFuel tail + 1

end

private theorem argumentShapeDepth_wrapArgumentBinds_le
    (bound : List Sig)
    (body : UniformIntrinsicRegion definitions arguments (bound ++ outer)) :
    argumentShapeDepth body ≤
      argumentShapeDepth (wrapArgumentBinds bound body) := by
  induction bound generalizing outer with
  | nil => exact Nat.le_refl _
  | cons signature rest induction =>
      have first : argumentShapeDepth body ≤
          argumentShapeDepth (wrapArgumentBind signature body) := by
        simp [wrapArgumentBind, argumentShapeDepth,
          argumentShapeItemSeqDepth, argumentShapeItemDepth]
        omega
      exact Nat.le_trans first
        (induction (wrapArgumentBind signature body))

private def ShapeDepthMotive
    (shape : CylindricalShape definitions insertion
      smallerContext largerContext) : Prop :=
  shapeReceiptFuel shape ≤
    argumentShapeDepth shape.smaller + argumentShapeDepth shape.larger

private def ShapeItemDepthMotive
    (shape : CylindricalShapeItem definitions insertion
      smallerContext largerContext) : Prop :=
  shapeItemReceiptFuel shape ≤
    argumentShapeItemDepth shape.smaller +
      argumentShapeItemDepth shape.larger

private def ShapeItemSeqDepthMotive
    (shape : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) : Prop :=
  shapeItemSeqReceiptFuel shape ≤
    argumentShapeItemSeqDepth shape.smaller +
      argumentShapeItemSeqDepth shape.larger

private theorem shapeDepth_block
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (outer : WireRenaming smallerOuter largerOuter)
    {smallerBound largerBound : List Sig}
    {freshCount : Nat}
    (bounds : BoundCylindrification fixedSignature
      smallerBound largerBound freshCount)
    {smallerHoles :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {largerHoles :
      List (Vars (largerBound ++ largerOuter) largerArguments)}
    (items : CylindricalShapeItemSeq definitions insertion
      (smallerBound ++ smallerOuter) (largerBound ++ largerOuter))
    (holes : CylindricalHoles insertion bounds (fun {_signature} => outer)
      smallerHoles largerHoles)
    (itemsBound : ShapeItemSeqDepthMotive items) :
    ShapeDepthMotive
      (CylindricalShape.block (insertion := insertion) (@outer)
        bounds items holes) := by
  have smallerWrapped := argumentShapeDepth_wrapArgumentBinds_le
    _ (.mk items.smaller ⟨smallerHoles⟩)
  have largerWrapped := argumentShapeDepth_wrapArgumentBinds_le
    _ (.mk items.larger ⟨largerHoles⟩)
  simp only [argumentShapeDepth] at smallerWrapped largerWrapped
  simp only [ShapeDepthMotive, ShapeItemSeqDepthMotive,
    shapeReceiptFuel, CylindricalShape.smaller,
    CylindricalShape.larger] at itemsBound ⊢
  omega

private theorem shapeDepth_leaf
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (embedding : WireRenaming smallerContext largerContext)
    (smaller : Item definitions smallerContext)
    (larger : Item definitions largerContext)
    (exact : smaller.renameWires embedding = larger) :
    ShapeItemDepthMotive
      (CylindricalShapeItem.leaf (insertion := insertion) embedding
        smaller larger exact) := by
  simp [ShapeItemDepthMotive, shapeItemReceiptFuel,
    CylindricalShapeItem.smaller, CylindricalShapeItem.larger,
    argumentShapeItemDepth]

private theorem shapeDepth_cut
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (body : CylindricalShape definitions insertion
      smallerContext largerContext)
    (bodyBound : ShapeDepthMotive body) :
    ShapeItemDepthMotive (CylindricalShapeItem.cut body) := by
  simp only [ShapeDepthMotive, ShapeItemDepthMotive,
    shapeItemReceiptFuel, CylindricalShapeItem.smaller,
    CylindricalShapeItem.larger, argumentShapeItemDepth] at bodyBound ⊢
  omega

private theorem shapeDepth_nil
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (embedding : WireRenaming smallerContext largerContext) :
    ShapeItemSeqDepthMotive
      (CylindricalShapeItemSeq.nil (definitions := definitions)
        (insertion := insertion) embedding) := by
  simp [ShapeItemSeqDepthMotive, shapeItemSeqReceiptFuel,
    CylindricalShapeItemSeq.smaller, CylindricalShapeItemSeq.larger,
    argumentShapeItemSeqDepth]

private theorem shapeDepth_cons
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (head : CylindricalShapeItem definitions insertion
      smallerContext largerContext)
    (tail : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext)
    (headBound : ShapeItemDepthMotive head)
    (tailBound : ShapeItemSeqDepthMotive tail) :
    ShapeItemSeqDepthMotive (CylindricalShapeItemSeq.cons head tail) := by
  simp only [ShapeItemDepthMotive, ShapeItemSeqDepthMotive,
    shapeItemSeqReceiptFuel, CylindricalShapeItemSeq.smaller,
    CylindricalShapeItemSeq.larger, argumentShapeItemSeqDepth]
    at headBound tailBound ⊢
  omega

private theorem shapeReceiptFuel_le_argumentDepth
    {largerArguments smallerArguments : List Sig}
    {fixedSignature : Sig}
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShape definitions insertion
      smallerContext largerContext) : ShapeDepthMotive shape :=
  CylindricalShape.rec
    (insertion := insertion)
    (motive_1 := fun _ _ value => ShapeDepthMotive value)
    (motive_2 := fun _ _ value => ShapeItemDepthMotive value)
    (motive_3 := fun _ _ value => ShapeItemSeqDepthMotive value)
    (shapeDepth_block (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_leaf (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cut (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_nil (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cons (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion)) shape

private theorem shapeItemReceiptFuel_le_argumentDepth
    {largerArguments smallerArguments : List Sig}
    {fixedSignature : Sig}
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShapeItem definitions insertion
      smallerContext largerContext) : ShapeItemDepthMotive shape :=
  CylindricalShapeItem.rec
    (insertion := insertion)
    (motive_1 := fun _ _ value => ShapeDepthMotive value)
    (motive_2 := fun _ _ value => ShapeItemDepthMotive value)
    (motive_3 := fun _ _ value => ShapeItemSeqDepthMotive value)
    (shapeDepth_block (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_leaf (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cut (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_nil (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cons (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion)) shape

private theorem shapeItemSeqReceiptFuel_le_argumentDepth
    {largerArguments smallerArguments : List Sig}
    {fixedSignature : Sig}
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) : ShapeItemSeqDepthMotive shape :=
  CylindricalShapeItemSeq.rec
    (insertion := insertion)
    (motive_1 := fun _ _ value => ShapeDepthMotive value)
    (motive_2 := fun _ _ value => ShapeItemDepthMotive value)
    (motive_3 := fun _ _ value => ShapeItemSeqDepthMotive value)
    (shapeDepth_block (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_leaf (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cut (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_nil (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion))
    (shapeDepth_cons (largerArguments := largerArguments)
      (smallerArguments := smallerArguments)
      (fixedSignature := fixedSignature) (definitions := definitions)
      (insertion := insertion)) shape

mutual

private theorem checkCylindricalShapeFuel_complete_of_receipt
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShape definitions insertion
      smallerContext largerContext)
    (consistent : shape.consistent)
    (outer : WireRenaming smallerContext largerContext)
    (embeddingExact :
      ∀ {signature} (value : Var smallerContext signature),
        shape.embedding value = outer value)
    (fuel : Nat)
    (enough : shapeReceiptFuel shape ≤ fuel) :
    ∃ checked,
      checkCylindricalShapeFuel fuel insertion outer
          shape.smaller shape.larger = some checked := by
  cases shape with
  | block shapeOuter bounds items holes =>
      have outerExact :
          (@shapeOuter) = @outer := by
        exact wireRenaming_ext_local shapeOuter outer embeddingExact
      subst outer
      cases fuel with
      | zero => simp [shapeReceiptFuel] at enough
      | succ innerFuel =>
          apply checkCylindricalShapeFuel_block_complete
            shapeOuter bounds items holes innerFuel
          apply checkCylindricalShapeItemSeqFuel_complete_of_receipt
            items consistent.1 (bounds.embed shapeOuter)
          · intro signature value
            exact consistent.2 value
          · simp only [shapeReceiptFuel] at enough
            omega

private theorem checkCylindricalShapeItemFuel_complete_of_receipt
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShapeItem definitions insertion
      smallerContext largerContext)
    (consistent : shape.consistent)
    (outer : WireRenaming smallerContext largerContext)
    (embeddingExact :
      ∀ {signature} (value : Var smallerContext signature),
        shape.embedding value = outer value)
    (fuel : Nat)
    (enough : shapeItemReceiptFuel shape ≤ fuel) :
    ∃ checked,
      checkCylindricalShapeItemFuel fuel insertion outer
          shape.smaller shape.larger = some checked := by
  cases shape with
  | leaf embedding smaller larger exact =>
      cases fuel with
      | zero => simp [shapeItemReceiptFuel] at enough
      | succ innerFuel =>
          have outerExact : (@embedding) = @outer :=
            wireRenaming_ext_local embedding outer embeddingExact
          subst outer
          simp only [CylindricalShapeItem.smaller,
            CylindricalShapeItem.larger]
          simp [checkCylindricalShapeItemFuel, exact]
  | cut body =>
      cases fuel with
      | zero => simp [shapeItemReceiptFuel] at enough
      | succ innerFuel =>
          obtain ⟨checked, accepted⟩ :=
            checkCylindricalShapeFuel_complete_of_receipt body consistent
              outer embeddingExact innerFuel (by
                simp only [shapeItemReceiptFuel] at enough
                omega)
          let checkedItem : CheckedCylindricalShapeItem insertion outer
              (.cut body.smaller) (.cut body.larger) :=
            { receipt := .cut checked.receipt
              embedding_exact := checked.embedding_exact
              smaller_exact := congrArg UniformIntrinsicItem.cut
                checked.smaller_exact
              larger_exact := congrArg UniformIntrinsicItem.cut
                checked.larger_exact
              consistent := checked.consistent }
          refine ⟨checkedItem, ?_⟩
          change
            (do
              let checkedBody ←
                checkCylindricalShapeFuel innerFuel insertion outer
                  body.smaller body.larger
              pure
                { receipt := CylindricalShapeItem.cut checkedBody.receipt
                  embedding_exact := checkedBody.embedding_exact
                  smaller_exact := congrArg UniformIntrinsicItem.cut
                    checkedBody.smaller_exact
                  larger_exact := congrArg UniformIntrinsicItem.cut
                    checkedBody.larger_exact
                  consistent := checkedBody.consistent }) = some checkedItem
          rw [accepted]
          rfl

private theorem checkCylindricalShapeItemSeqFuel_complete_of_receipt
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    (shape : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext)
    (consistent : shape.consistent)
    (outer : WireRenaming smallerContext largerContext)
    (embeddingExact :
      ∀ {signature} (value : Var smallerContext signature),
        shape.embedding value = outer value)
    (fuel : Nat)
    (enough : shapeItemSeqReceiptFuel shape ≤ fuel) :
    ∃ checked,
      checkCylindricalShapeItemSeqFuel fuel insertion outer
          shape.smaller shape.larger = some checked := by
  cases shape with
  | nil embedding =>
      cases fuel with
      | zero => simp [shapeItemSeqReceiptFuel] at enough
      | succ innerFuel =>
          let checkedNil : CheckedCylindricalShapeItemSeq insertion outer
              (.nil : UniformIntrinsicItemSeq definitions smallerArguments
                smallerContext)
              (.nil : UniformIntrinsicItemSeq definitions largerArguments
                largerContext) :=
            { receipt := .nil outer
              embedding_exact := by
                intro signature value
                simp [CylindricalShapeItemSeq.embedding]
              smaller_exact := by
                simp [CylindricalShapeItemSeq.smaller]
              larger_exact := by
                simp [CylindricalShapeItemSeq.larger]
              consistent := by
                simp [CylindricalShapeItemSeq.consistent] }
          refine ⟨checkedNil, ?_⟩
          change some checkedNil = some checkedNil
          rfl
  | cons head tail =>
      cases fuel with
      | zero => simp [shapeItemSeqReceiptFuel] at enough
      | succ innerFuel =>
          obtain ⟨checkedHead, headAccepted⟩ :=
            checkCylindricalShapeItemFuel_complete_of_receipt head
              consistent.1 outer embeddingExact innerFuel (by
                simp only [shapeItemSeqReceiptFuel] at enough
                omega)
          have tailEmbedding :
              ∀ {signature} (value : Var smallerContext signature),
                tail.embedding value = outer value := by
            intro signature value
            rw [consistent.2.2 value]
            exact embeddingExact value
          obtain ⟨checkedTail, tailAccepted⟩ :=
            checkCylindricalShapeItemSeqFuel_complete_of_receipt tail
              consistent.2.1 outer tailEmbedding innerFuel (by
                simp only [shapeItemSeqReceiptFuel] at enough
                omega)
          let checkedSeq : CheckedCylindricalShapeItemSeq insertion outer
              (.cons head.smaller tail.smaller)
              (.cons head.larger tail.larger) :=
            { receipt := .cons checkedHead.receipt checkedTail.receipt
              embedding_exact := checkedHead.embedding_exact
              smaller_exact := by
                change
                  UniformIntrinsicItemSeq.cons
                      checkedHead.receipt.smaller
                      checkedTail.receipt.smaller =
                    UniformIntrinsicItemSeq.cons
                      head.smaller tail.smaller
                rw [checkedHead.smaller_exact, checkedTail.smaller_exact]
              larger_exact := by
                change
                  UniformIntrinsicItemSeq.cons
                      checkedHead.receipt.larger
                      checkedTail.receipt.larger =
                    UniformIntrinsicItemSeq.cons
                      head.larger tail.larger
                rw [checkedHead.larger_exact, checkedTail.larger_exact]
              consistent := by
                exact
                  ⟨checkedHead.consistent, checkedTail.consistent,
                    fun value => by
                      rw [checkedTail.embedding_exact value,
                        checkedHead.embedding_exact value]⟩ }
          refine ⟨checkedSeq, ?_⟩
          change
            (do
              let checkedHead' ←
                checkCylindricalShapeItemFuel innerFuel insertion outer
                  head.smaller head.larger
              let checkedTail' ←
                checkCylindricalShapeItemSeqFuel innerFuel insertion outer
                  tail.smaller tail.larger
              let receipt : CylindricalShapeItemSeq definitions insertion
                  smallerContext largerContext :=
                .cons checkedHead'.receipt checkedTail'.receipt
              pure
                { receipt := receipt
                  embedding_exact := checkedHead'.embedding_exact
                  smaller_exact := by
                    change
                      UniformIntrinsicItemSeq.cons
                          checkedHead'.receipt.smaller
                          checkedTail'.receipt.smaller =
                        UniformIntrinsicItemSeq.cons
                          head.smaller tail.smaller
                    rw [checkedHead'.smaller_exact,
                      checkedTail'.smaller_exact]
                  larger_exact := by
                    change
                      UniformIntrinsicItemSeq.cons
                          checkedHead'.receipt.larger
                          checkedTail'.receipt.larger =
                        UniformIntrinsicItemSeq.cons
                          head.larger tail.larger
                    rw [checkedHead'.larger_exact,
                      checkedTail'.larger_exact]
                  consistent := by
                    exact
                      ⟨checkedHead'.consistent, checkedTail'.consistent,
                        fun value => by
                          rw [checkedTail'.embedding_exact value,
                            checkedHead'.embedding_exact value]⟩ }) =
                some checkedSeq
          rw [headAccepted, tailAccepted]
          rfl

end

theorem checkCylindricalShape_complete
    {insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature}
    {outer : WireRenaming smallerContext largerContext}
    {smaller :
      UniformIntrinsicRegion definitions smallerArguments smallerContext}
    {larger :
      UniformIntrinsicRegion definitions largerArguments largerContext}
    (receipt :
      CheckedCylindricalShape insertion outer smaller larger) :
    (checkCylindricalShape insertion outer smaller larger).isSome = true := by
  rcases receipt with
    ⟨shape, embeddingExact, smallerExact, largerExact, consistent⟩
  have enough := shapeReceiptFuel_le_argumentDepth shape
  simp only [ShapeDepthMotive] at enough
  obtain ⟨checked, accepted⟩ :=
    checkCylindricalShapeFuel_complete_of_receipt
      shape consistent outer embeddingExact
      (argumentShapeDepth shape.smaller +
        argumentShapeDepth shape.larger + 1) (by omega)
  have internal :
      (checkCylindricalShape insertion outer shape.smaller
          shape.larger).isSome = true := by
    unfold checkCylindricalShape
    rw [accepted]
    rfl
  rw [← smallerExact, ← largerExact]
  exact internal

end VisualProof.ConcreteWirePrimitive.ArgumentsSemantics
