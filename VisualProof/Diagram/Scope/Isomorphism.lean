import VisualProof.Diagram.Scope.Rename

namespace VisualProof.Diagram

open VisualProof.Data.Finite
open VisualProof.Theory

private theorem Var.signature_eq_get_index
    (wire : Var context signature) :
    signature = context.get wire.index := by
  induction wire with
  | here => rfl
  | there tail induction => simpa [Var.index] using induction

private theorem Var.signature_eq_of_index_val_eq
    (left : Var context leftSignature)
    (right : Var context rightSignature)
    (indexEq : left.index.val = right.index.val) :
    leftSignature = rightSignature := by
  have finEq : left.index = right.index := Fin.ext indexEq
  calc
    leftSignature = context.get left.index :=
      Var.signature_eq_get_index left
    _ = context.get right.index := congrArg context.get finEq
    _ = rightSignature := (Var.signature_eq_get_index right).symm

private theorem WireEquiv.index_val_eq_iff
    (equivalence : WireEquiv source target)
    (left : Var source leftSignature)
    (right : Var source rightSignature) :
    (equivalence left).index.val = (equivalence right).index.val ↔
      left.index.val = right.index.val := by
  constructor
  · intro indexEq
    have signatureEq := Var.signature_eq_of_index_val_eq
      (equivalence left) (equivalence right) indexEq
    subst rightSignature
    have mappedEq : equivalence left = equivalence right :=
      Var.eq_of_index_eq _ _ (Fin.ext indexEq)
    have sourceEq : left = right := by
      calc
        left = equivalence.symm (equivalence left) :=
          (equivalence.left_inv left).symm
        _ = equivalence.symm (equivalence right) :=
          congrArg (fun mapped : Var target leftSignature =>
            equivalence.symm mapped) mappedEq
        _ = right := equivalence.left_inv right
    exact congrArg (fun wire => wire.index.val) sourceEq
  · intro indexEq
    have signatureEq := Var.signature_eq_of_index_val_eq left right indexEq
    subst rightSignature
    have sourceEq : left = right :=
      Var.eq_of_index_eq _ _ (Fin.ext indexEq)
    exact congrArg (fun wire => wire.index.val)
      (congrArg (fun sourceWire : Var source leftSignature =>
        equivalence sourceWire) sourceEq)

private theorem Vars.countIndex_map_equiv
    (variables : Vars source signatures)
    (equivalence : WireEquiv source target)
    (wire : Var source signature) :
    (variables.map (fun sourceWire => equivalence sourceWire)).countIndex
        (equivalence wire).index.val =
      variables.countIndex wire.index.val := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      change
        (if (equivalence head).index.val = (equivalence wire).index.val
          then 1 else 0) +
            (tail.map (fun sourceWire => equivalence sourceWire)).countIndex
              (equivalence wire).index.val =
          (if head.index.val = wire.index.val then 1 else 0) +
            tail.countIndex wire.index.val
      rw [induction]
      by_cases sourceEq : head.index.val = wire.index.val
      · have targetEq :=
          (WireEquiv.index_val_eq_iff equivalence head wire).mpr sourceEq
        simp only [sourceEq, targetEq, if_true]
      · have targetNe :=
          not_congr (WireEquiv.index_val_eq_iff equivalence head wire) |>.mpr
            sourceEq
        simp only [sourceEq, targetNe, if_false]

private theorem countPorts_map_equiv
    (arity : Nat) (ports : Fin arity → Var source portSignature)
    (equivalence : WireEquiv source target)
    (wire : Var source signature) :
    (List.ofFn fun index : Fin arity =>
      (equivalence (ports index)).index.val).count
        (equivalence wire).index.val =
      (List.ofFn fun index : Fin arity =>
        (ports index).index.val).count wire.index.val := by
  induction arity with
  | zero => simp
  | succ arity induction =>
      rw [List.ofFn_succ, List.ofFn_succ, List.count_cons,
        List.count_cons, induction (fun index => ports index.succ)]
      by_cases sourceEq : (ports 0).index.val = wire.index.val
      · have targetEq :=
          (WireEquiv.index_val_eq_iff equivalence (ports 0) wire).mpr
            sourceEq
        simp [sourceEq, targetEq]
      · have targetNe :=
          not_congr
            (WireEquiv.index_val_eq_iff equivalence (ports 0) wire) |>.mpr
              sourceEq
        simp [sourceEq, targetNe]

private theorem List.Perm.of_nodup_mem_iff [BEq α] [LawfulBEq α]
    {left right : List α} (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      have rightEmpty : right = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value member
        simpa using (sameMembers value).mpr member
      subst right
      exact .refl []
  | cons head tail induction =>
      have headMember : head ∈ right :=
        (sameMembers head).mp (by simp)
      have rightPerm : right.Perm (head :: right.erase head) :=
        List.perm_cons_erase headMember
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have headNotTail := (List.nodup_cons.mp leftNodup).1
      have erasedNodup := rightNodup.erase head
      have tailMembers : ∀ value,
          value ∈ tail ↔ value ∈ right.erase head := by
        intro value
        rw [rightNodup.mem_erase_iff]
        constructor
        · intro member
          refine ⟨?_, (sameMembers value).mp (by simp [member])⟩
          intro valueEq
          subst value
          exact headNotTail member
        · rintro ⟨valueNe, member⟩
          have sourceMember := (sameMembers value).mpr member
          simpa [valueNe] using sourceMember
      exact (List.Perm.cons head
        (induction tailNodup erasedNodup tailMembers)).trans rightPerm.symm

private theorem allFin_map_equiv_perm
    (equivalence : FiniteEquiv (Fin source) (Fin target)) :
    ((allFin source).map equivalence).Perm (allFin target) := by
  apply List.Perm.of_nodup_mem_iff
  · exact (allFin_nodup source).map equivalence
      (fun _ _ different equal => different (equivalence.injective equal))
  · exact allFin_nodup target
  · intro targetIndex
    constructor
    · intro member
      exact mem_allFin targetIndex
    · intro _
      exact List.mem_map.mpr
        ⟨equivalence.symm targetIndex, mem_allFin _,
          equivalence.right_inv targetIndex⟩

private theorem List.ofFn_eq_allFin_map (values : Fin size → α) :
    List.ofFn values = (allFin size).map values := by
  induction size with
  | zero => rfl
  | succ size induction =>
      simp only [List.ofFn_succ, allFin, List.map_cons, List.map_map]
      rw [induction (fun position => values position.succ)]
      rfl

private theorem Item.incidencePaths_length_index
    (item : Item wires) (wireIndex firstIndex secondIndex : Nat) :
    (item.incidencePaths wireIndex firstIndex).length =
      (item.incidencePaths wireIndex secondIndex).length := by
  cases item <;> simp [Item.incidencePaths]

private def ItemSeq.incidenceLengths
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) : List Nat :=
  (allFin items.length).map fun position =>
    ((items.get position).incidencePaths wireIndex
      (itemIndex + position.val)).length

private theorem ItemSeq.incidencePaths_length_eq_sum
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) :
    (items.incidencePaths wireIndex itemIndex).length =
      (items.incidenceLengths wireIndex itemIndex).sum := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ wireIndex itemIndex,
      (items.incidencePaths wireIndex itemIndex).length =
        (items.incidenceLengths wireIndex itemIndex).sum
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro _ _ _; rfl)
    (by
      intro context head tail _ induction wireIndex itemIndex
      simp only [ItemSeq.incidencePaths, List.length_append,
        ItemSeq.incidenceLengths, ItemSeq.length, allFin,
        List.map_cons, List.sum_cons, Fin.val_zero, Nat.add_zero,
        ItemSeq.get]
      rw [induction wireIndex (itemIndex + 1)]
      congr 1
      apply congrArg List.sum
      simp only [List.map_map]
      apply List.map_congr_left
      intro position member
      change
        ((tail.get position).incidencePaths wireIndex
            (itemIndex + 1 + position.val)).length =
          ((tail.get position).incidencePaths wireIndex
            (itemIndex + (Fin.succ position).val)).length
      exact (Item.incidencePaths_length_index
        (tail.get position) wireIndex
        (itemIndex + (Fin.succ position).val)
        (itemIndex + 1 + position.val)).symm)
    items wireIndex itemIndex

private def RegionIncidenceLengthMotive
    {sourceOuter targetOuter : List Sig}
    (ambient : WireEquiv sourceOuter targetOuter)
    (source : Region sourceOuter) (target : Region targetOuter)
    (_ : RegionIso ambient source target) : Prop :=
  ∀ {signature} (wire : Var sourceOuter signature),
    (source.incidencePaths wire.index.val).length =
      (target.incidencePaths (ambient wire).index.val).length

private def ItemIncidenceLengthMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : Item sourceWires) (target : Item targetWires)
    (_ : ItemIso ambient source target) : Prop :=
  ∀ {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat),
    (source.incidencePaths wire.index.val sourceIndex).length =
      (target.incidencePaths (ambient wire).index.val targetIndex).length

private def ItemsIncidenceLengthMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : ItemSeq sourceWires) (target : ItemSeq targetWires)
    (_ : ItemSeqIso ambient source target) : Prop :=
  ∀ {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat),
    (source.incidencePaths wire.index.val sourceIndex).length =
      (target.incidencePaths (ambient wire).index.val targetIndex).length

private theorem regionIncidenceLengthCase
    {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
    {ambient : WireEquiv sourceOuter targetOuter}
    {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
    {targetItems : ItemSeq (targetOuter ++ targetLocals)}
    (locals : WireEquiv sourceLocals targetLocals)
    (items : ItemSeqIso (ambient.append locals) sourceItems targetItems)
    (itemsIH : ItemsIncidenceLengthMotive
      (ambient.append locals) sourceItems targetItems items) :
    RegionIncidenceLengthMotive ambient (.mk sourceLocals sourceItems)
      (.mk targetLocals targetItems) (.mk locals items) := by
  intro signature wire
  simp only [Region.incidencePaths]
  simpa only [WireEquiv.append_apply_left, Var.index_appendLeft] using
    itemsIH (wire.appendLeft sourceLocals) 0 0

private theorem atomIncidenceLengthCase
    {sourceWires targetWires arguments : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceHead : Var sourceWires (.rel arguments)}
    {targetHead : Var targetWires (.rel arguments)}
    {sourcePorts : Vars sourceWires arguments}
    {targetPorts : Vars targetWires arguments}
    (headEq : ambient sourceHead = targetHead)
    (portsEq : sourcePorts.map (fun wire => ambient wire) = targetPorts) :
    ItemIncidenceLengthMotive ambient (.atom sourceHead sourcePorts)
      (.atom targetHead targetPorts) (.atom headEq portsEq) := by
  intro signature wire sourceIndex targetIndex
  subst targetHead
  subst targetPorts
  simp only [Item.incidencePaths, List.length_replicate]
  rw [Vars.countIndex_map_equiv sourcePorts ambient wire]
  by_cases sourceEq : sourceHead.index.val = wire.index.val
  · have targetEq :=
      (WireEquiv.index_val_eq_iff ambient sourceHead wire).mpr sourceEq
    simp only [sourceEq, targetEq, if_true]
  · have targetNe :=
      not_congr (WireEquiv.index_val_eq_iff ambient sourceHead wire) |>.mpr
        sourceEq
    simp only [sourceEq, targetNe, if_false]

private theorem identityIncidenceLengthCase
    {sourceWires targetWires : List Sig} {portSignature : Sig}
    {arity : Nat} {ambient : WireEquiv sourceWires targetWires}
    {sourcePorts : Fin arity → Var sourceWires portSignature}
    {targetPorts : Fin arity → Var targetWires portSignature}
    (positions : FiniteEquiv (Fin arity) (Fin arity))
    (portsEq : ∀ sourceIndex,
      ambient (sourcePorts sourceIndex) = targetPorts (positions sourceIndex)) :
    ItemIncidenceLengthMotive ambient
      (.identity portSignature arity sourcePorts)
      (.identity portSignature arity targetPorts)
      (.identity positions portsEq) := by
  intro signature wire sourceIndex targetIndex
  simp only [Item.incidencePaths, List.length_replicate]
  let sourceValues := List.ofFn fun position : Fin arity =>
    (ambient (sourcePorts position)).index.val
  let targetValues := List.ofFn fun position : Fin arity =>
    (targetPorts position).index.val
  have valuesPerm : sourceValues.Perm targetValues := by
    dsimp only [sourceValues, targetValues]
    rw [List.ofFn_eq_allFin_map, List.ofFn_eq_allFin_map]
    have permuted := (allFin_map_equiv_perm positions).map
      (fun targetPosition => (targetPorts targetPosition).index.val)
    have sourceEq :
        (allFin arity).map
            (fun sourcePosition =>
              (ambient (sourcePorts sourcePosition)).index.val) =
          ((allFin arity).map positions).map
            (fun targetPosition => (targetPorts targetPosition).index.val) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro position member
      simpa only [Function.comp_apply] using
        congrArg (fun port => port.index.val) (portsEq position)
    rw [sourceEq]
    exact permuted
  rw [← valuesPerm.count (ambient wire).index.val,
    countPorts_map_equiv arity sourcePorts ambient wire]

private theorem cutIncidenceLengthCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceBody : Region sourceWires} {targetBody : Region targetWires}
    (body : RegionIso ambient sourceBody targetBody)
    (bodyIH : RegionIncidenceLengthMotive ambient sourceBody targetBody body) :
    ItemIncidenceLengthMotive ambient (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro signature wire sourceIndex targetIndex
  simp only [Item.incidencePaths, List.length_map]
  exact bodyIH wire

private theorem permuteIncidenceLengthCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length), positions sourceIndex = targetIndex →
      ItemIso ambient (source.get sourceIndex) (target.get targetIndex))
    (itemsIH : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length)
      (equality : positions sourceIndex = targetIndex),
      ItemIncidenceLengthMotive ambient (source.get sourceIndex)
        (target.get targetIndex) (items sourceIndex targetIndex equality)) :
    ItemsIncidenceLengthMotive ambient source target
      (.permute positions items) := by
  intro signature wire sourceIndex targetIndex
  rw [ItemSeq.incidencePaths_length_eq_sum,
    ItemSeq.incidencePaths_length_eq_sum]
  apply List.Perm.sum_nat
  have permuted := (allFin_map_equiv_perm positions).map
    (fun targetPosition =>
      ((target.get targetPosition).incidencePaths
        (ambient wire).index.val (targetIndex + targetPosition.val)).length)
  have sourceEq : source.incidenceLengths wire.index.val sourceIndex =
      ((allFin source.length).map positions).map
        (fun targetPosition =>
          ((target.get targetPosition).incidencePaths
            (ambient wire).index.val
            (targetIndex + targetPosition.val)).length) := by
    simp only [ItemSeq.incidenceLengths, List.map_map]
    apply List.map_congr_left
    intro position member
    exact itemsIH position (positions position) rfl wire
      (sourceIndex + position.val)
      (targetIndex + (positions position).val)
  rw [sourceEq]
  exact permuted

private theorem RegionIso.incidencePaths_length_eq_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target) :
    RegionIncidenceLengthMotive ambient source target iso := by
  unfold RegionIncidenceLengthMotive
  intro signature wire
  exact (RegionIso.rec
    (motive_1 := RegionIncidenceLengthMotive)
    (motive_2 := ItemIncidenceLengthMotive)
    (motive_3 := ItemsIncidenceLengthMotive)
    regionIncidenceLengthCase atomIncidenceLengthCase
    identityIncidenceLengthCase cutIncidenceLengthCase
    permuteIncidenceLengthCase iso) wire

private theorem ItemIso.incidencePaths_length_eq_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : Item sourceWires} {target : Item targetWires}
    (iso : ItemIso ambient source target) :
    ItemIncidenceLengthMotive ambient source target iso := by
  unfold ItemIncidenceLengthMotive
  intro signature wire sourceIndex targetIndex
  exact (ItemIso.rec
    (motive_1 := RegionIncidenceLengthMotive)
    (motive_2 := ItemIncidenceLengthMotive)
    (motive_3 := ItemsIncidenceLengthMotive)
    regionIncidenceLengthCase atomIncidenceLengthCase
    identityIncidenceLengthCase cutIncidenceLengthCase
    permuteIncidenceLengthCase iso) wire sourceIndex targetIndex

private theorem ItemSeqIso.incidencePaths_length_eq_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target) :
    ItemsIncidenceLengthMotive ambient source target iso := by
  unfold ItemsIncidenceLengthMotive
  intro signature wire sourceIndex targetIndex
  exact (ItemSeqIso.rec
    (motive_1 := RegionIncidenceLengthMotive)
    (motive_2 := ItemIncidenceLengthMotive)
    (motive_3 := ItemsIncidenceLengthMotive)
    regionIncidenceLengthCase atomIncidenceLengthCase
    identityIncidenceLengthCase cutIncidenceLengthCase
    permuteIncidenceLengthCase iso) wire sourceIndex targetIndex

private theorem ItemSeq.mem_incidencePaths_iff_get
    (items : ItemSeq wires) (wireIndex itemIndex : Nat)
    (path : RegionPath) :
    path ∈ items.incidencePaths wireIndex itemIndex ↔
      ∃ position : Fin items.length,
        path ∈ (items.get position).incidencePaths wireIndex
          (itemIndex + position.val) := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ wireIndex itemIndex path,
      path ∈ items.incidencePaths wireIndex itemIndex ↔
        ∃ position : Fin items.length,
          path ∈ (items.get position).incidencePaths wireIndex
            (itemIndex + position.val)
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro context wireIndex itemIndex path; constructor
        <;> intro impossible
        · simp only [ItemSeq.incidencePaths, List.not_mem_nil] at impossible
        · obtain ⟨position, _⟩ := impossible
          exact Fin.elim0 position)
    (by
      intro context head tail _ induction wireIndex itemIndex path
      simp only [ItemSeq.incidencePaths, List.mem_append]
      constructor
      · rintro (headMember | tailMember)
        · exact ⟨⟨0, by simp [ItemSeq.length]⟩,
            by simpa using headMember⟩
        · obtain ⟨position, member⟩ :=
            (induction wireIndex (itemIndex + 1) path).mp tailMember
          refine ⟨position.succ, ?_⟩
          have indexEq : itemIndex + position.succ.val =
              itemIndex + 1 + position.val := by
            change itemIndex + (position.val + 1) =
              itemIndex + 1 + position.val
            omega
          simpa only [ItemSeq.length, ItemSeq.get, indexEq] using member
      · rintro ⟨position, member⟩
        refine Fin.cases (motive := fun position =>
          path ∈ (ItemSeq.get (.cons head tail) position).incidencePaths
              wireIndex (itemIndex + position.val) →
            path ∈ head.incidencePaths wireIndex itemIndex ∨
              path ∈ tail.incidencePaths wireIndex (itemIndex + 1))
          ?_ (fun tailPosition tailMember => ?_) position member
        · intro headMember
          exact Or.inl (by simpa using headMember)
        · apply Or.inr
          apply (induction wireIndex (itemIndex + 1) path).mpr
          refine ⟨tailPosition, ?_⟩
          simpa only [ItemSeq.length, ItemSeq.get, Fin.val_succ,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailMember)
    items wireIndex itemIndex path

private theorem Item.nil_or_starts_of_mem_incidencePaths
    (item : Item wires) (wireIndex itemIndex : Nat)
    {path : RegionPath}
    (member : path ∈ item.incidencePaths wireIndex itemIndex) :
    path = [] ∨ RegionPath.StartsWith itemIndex path := by
  cases item with
  | atom head ports =>
      exact Or.inl (List.eq_of_mem_replicate member)
  | identity signature arity ports =>
      exact Or.inl (List.eq_of_mem_replicate member)
  | cut body =>
      simp only [Item.incidencePaths, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact Or.inr ⟨inner, rfl⟩

private theorem RegionPath.startsWith_index_unique
    {path : RegionPath} (first second : Nat)
    (firstStarts : RegionPath.StartsWith first path)
    (secondStarts : RegionPath.StartsWith second path) :
    first = second := by
  obtain ⟨firstTail, rfl⟩ := firstStarts
  obtain ⟨secondTail, equality⟩ := secondStarts
  injection equality

private def ItemSeq.NoDirectIncidence
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) : Prop :=
  ∀ position : Fin items.length,
    [] ∉ (items.get position).incidencePaths wireIndex
      (itemIndex + position.val)

private def ItemSeq.AtMostOneIncidenceItem
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) : Prop :=
  ∀ first second : Fin items.length,
    (items.get first).incidencePaths wireIndex
        (itemIndex + first.val) ≠ [] →
      (items.get second).incidencePaths wireIndex
        (itemIndex + second.val) ≠ [] →
      first = second

private theorem ItemSeq.commonHead_incidencePaths_iff
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) :
    RegionPath.CommonHead (items.incidencePaths wireIndex itemIndex) ↔
      items.NoDirectIncidence wireIndex itemIndex ∧
        items.AtMostOneIncidenceItem wireIndex itemIndex := by
  constructor
  · rintro ⟨commonIndex, allStart⟩
    constructor
    · intro position nilMember
      have totalMember := (ItemSeq.mem_incidencePaths_iff_get
        items wireIndex itemIndex []).mpr ⟨position, nilMember⟩
      simpa [RegionPath.StartsWith] using allStart [] totalMember
    · intro first second firstNonempty secondNonempty
      obtain ⟨firstPath, firstMember⟩ :=
        List.exists_mem_of_ne_nil _ firstNonempty
      obtain ⟨secondPath, secondMember⟩ :=
        List.exists_mem_of_ne_nil _ secondNonempty
      have firstTotal := (ItemSeq.mem_incidencePaths_iff_get
        items wireIndex itemIndex firstPath).mpr ⟨first, firstMember⟩
      have secondTotal := (ItemSeq.mem_incidencePaths_iff_get
        items wireIndex itemIndex secondPath).mpr ⟨second, secondMember⟩
      have firstNotNil : firstPath ≠ [] := by
        intro firstNil
        subst firstPath
        exact (by
          have := allStart [] firstTotal
          simp [RegionPath.StartsWith] at this)
      have secondNotNil : secondPath ≠ [] := by
        intro secondNil
        subst secondPath
        exact (by
          have := allStart [] secondTotal
          simp [RegionPath.StartsWith] at this)
      have firstStarts :=
        (Item.nil_or_starts_of_mem_incidencePaths
          (items.get first) wireIndex (itemIndex + first.val)
          firstMember).resolve_left firstNotNil
      have secondStarts :=
        (Item.nil_or_starts_of_mem_incidencePaths
          (items.get second) wireIndex (itemIndex + second.val)
          secondMember).resolve_left secondNotNil
      have firstEq := RegionPath.startsWith_index_unique
        (itemIndex + first.val) commonIndex firstStarts
        (allStart firstPath firstTotal)
      have secondEq := RegionPath.startsWith_index_unique
        (itemIndex + second.val) commonIndex secondStarts
        (allStart secondPath secondTotal)
      apply Fin.ext
      omega
  · rintro ⟨noDirect, atMostOne⟩
    by_cases empty : items.incidencePaths wireIndex itemIndex = []
    · exact ⟨0, by simp [empty]⟩
    · obtain ⟨firstPath, firstMember⟩ :=
        List.exists_mem_of_ne_nil _ empty
      obtain ⟨firstPosition, firstItemMember⟩ :=
        (ItemSeq.mem_incidencePaths_iff_get
          items wireIndex itemIndex firstPath).mp firstMember
      refine ⟨itemIndex + firstPosition.val, ?_⟩
      intro path member
      obtain ⟨position, itemMember⟩ :=
        (ItemSeq.mem_incidencePaths_iff_get
          items wireIndex itemIndex path).mp member
      have firstNonempty :
          (items.get firstPosition).incidencePaths wireIndex
            (itemIndex + firstPosition.val) ≠ [] :=
        fun equal => by
          rw [equal] at firstItemMember
          exact nomatch firstItemMember
      have positionNonempty :
          (items.get position).incidencePaths wireIndex
            (itemIndex + position.val) ≠ [] :=
        fun equal => by
          rw [equal] at itemMember
          exact nomatch itemMember
      have positionEq := atMostOne firstPosition position
        firstNonempty positionNonempty
      subst position
      exact (Item.nil_or_starts_of_mem_incidencePaths
        (items.get firstPosition) wireIndex
        (itemIndex + firstPosition.val) itemMember).resolve_left
          (fun nilEq => noDirect firstPosition (nilEq ▸ itemMember))

private theorem ItemIso.incidencePaths_nonempty_iff_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : Item sourceWires} {target : Item targetWires}
    (iso : ItemIso ambient source target)
    {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat) :
    source.incidencePaths wire.index.val sourceIndex ≠ [] ↔
      target.incidencePaths (ambient wire).index.val targetIndex ≠ [] := by
  rw [← List.length_pos_iff, ← List.length_pos_iff,
    iso.incidencePaths_length_eq_core wire sourceIndex targetIndex]

private theorem List.nil_mem_iff_nonempty_of_all_nil
    (paths : List RegionPath)
    (allNil : ∀ path ∈ paths, path = []) :
    [] ∈ paths ↔ paths ≠ [] := by
  constructor
  · intro member empty
    rw [empty] at member
    exact nomatch member
  · intro nonempty
    obtain ⟨path, member⟩ := List.exists_mem_of_ne_nil paths nonempty
    rw [allNil path member] at member
    exact member

private theorem ItemIso.nil_mem_incidencePaths_iff_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : Item sourceWires} {target : Item targetWires}
    (iso : ItemIso ambient source target)
    {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat) :
    [] ∈ source.incidencePaths wire.index.val sourceIndex ↔
      [] ∈ target.incidencePaths (ambient wire).index.val targetIndex := by
  cases iso with
  | atom headEq portsEq =>
      exact (List.nil_mem_iff_nonempty_of_all_nil _
        (fun path member => List.eq_of_mem_replicate member)).trans
        ((ItemIso.incidencePaths_nonempty_iff_core
          (.atom headEq portsEq) wire sourceIndex targetIndex).trans
          (List.nil_mem_iff_nonempty_of_all_nil _
            (fun path member => List.eq_of_mem_replicate member)).symm)
  | identity positions portsEq =>
      exact (List.nil_mem_iff_nonempty_of_all_nil _
        (fun path member => List.eq_of_mem_replicate member)).trans
        ((ItemIso.incidencePaths_nonempty_iff_core
          (.identity positions portsEq) wire sourceIndex targetIndex).trans
          (List.nil_mem_iff_nonempty_of_all_nil _
            (fun path member => List.eq_of_mem_replicate member)).symm)
  | cut body =>
      simp [Item.incidencePaths]

private theorem ItemSeqIso.commonHead_incidencePaths_forward
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target)
    {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat)
    (sourceCommon : RegionPath.CommonHead
      (source.incidencePaths wire.index.val sourceIndex)) :
    RegionPath.CommonHead
      (target.incidencePaths (ambient wire).index.val targetIndex) := by
  cases iso with
  | permute positions items =>
      have sourceProperties :=
        (ItemSeq.commonHead_incidencePaths_iff source wire.index.val
          sourceIndex).mp sourceCommon
      apply (ItemSeq.commonHead_incidencePaths_iff target
        (ambient wire).index.val targetIndex).mpr
      constructor
      · intro targetPosition targetNil
        let sourcePosition := positions.symm targetPosition
        have positionEq : positions sourcePosition = targetPosition :=
          positions.right_inv targetPosition
        have itemIso := items sourcePosition targetPosition positionEq
        have sourceNil :=
          (itemIso.nil_mem_incidencePaths_iff_core wire
            (sourceIndex + sourcePosition.val)
            (targetIndex + targetPosition.val)).mpr targetNil
        exact sourceProperties.1 sourcePosition sourceNil
      · intro firstTarget secondTarget firstNonempty secondNonempty
        let firstSource := positions.symm firstTarget
        let secondSource := positions.symm secondTarget
        have firstPositionEq : positions firstSource = firstTarget :=
          positions.right_inv firstTarget
        have secondPositionEq : positions secondSource = secondTarget :=
          positions.right_inv secondTarget
        have firstIso := items firstSource firstTarget firstPositionEq
        have secondIso := items secondSource secondTarget secondPositionEq
        have firstSourceNonempty :=
          (firstIso.incidencePaths_nonempty_iff_core wire
            (sourceIndex + firstSource.val)
            (targetIndex + firstTarget.val)).mpr firstNonempty
        have secondSourceNonempty :=
          (secondIso.incidencePaths_nonempty_iff_core wire
            (sourceIndex + secondSource.val)
            (targetIndex + secondTarget.val)).mpr secondNonempty
        have sourceEq := sourceProperties.2 firstSource secondSource
          firstSourceNonempty secondSourceNonempty
        calc
          firstTarget = positions firstSource := firstPositionEq.symm
          _ = positions secondSource := congrArg positions sourceEq
          _ = secondTarget := secondPositionEq

private theorem ItemSeqIso.commonHead_incidencePaths_iff_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target)
    {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat) :
    RegionPath.CommonHead
        (source.incidencePaths wire.index.val sourceIndex) ↔
      RegionPath.CommonHead
        (target.incidencePaths (ambient wire).index.val targetIndex) := by
  constructor
  · exact iso.commonHead_incidencePaths_forward wire
      sourceIndex targetIndex
  · intro targetCommon
    have backward := iso.symm.commonHead_incidencePaths_forward
      (ambient wire) targetIndex sourceIndex targetCommon
    simpa only [WireEquiv.symm_apply_apply] using backward

private theorem ItemSeqIso.rootedTwo_incidencePaths_iff_core
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (iso : ItemSeqIso ambient source target)
    {signature} (wire : Var sourceWires signature)
    (sourceIndex targetIndex : Nat) :
    RegionPath.RootedTwo
        (source.incidencePaths wire.index.val sourceIndex) ↔
      RegionPath.RootedTwo
        (target.incidencePaths (ambient wire).index.val targetIndex) := by
  have lengthEq := iso.incidencePaths_length_eq_core wire
    sourceIndex targetIndex
  have commonIff := iso.commonHead_incidencePaths_iff_core wire
    sourceIndex targetIndex
  constructor
  · intro sourceRooted
    have sourceNonempty := sourceRooted.nonempty
    have sourceNoCommon :=
      (RegionPath.rooted_iff_not_commonHead _).mp
        ⟨sourceNonempty, sourceRooted.2⟩ |>.2
    have targetLength : 2 ≤
        (target.incidencePaths (ambient wire).index.val targetIndex).length := by
      rw [← lengthEq]
      exact sourceRooted.1
    have targetNonempty :
        target.incidencePaths (ambient wire).index.val targetIndex ≠ [] := by
      rw [← List.length_pos_iff]
      omega
    have targetNoCommon : ¬ RegionPath.CommonHead
        (target.incidencePaths (ambient wire).index.val targetIndex) :=
      fun targetCommon => sourceNoCommon (commonIff.mpr targetCommon)
    exact ⟨targetLength,
      ((RegionPath.rooted_iff_not_commonHead _).mpr
        ⟨targetNonempty, targetNoCommon⟩).2⟩
  · intro targetRooted
    have targetNonempty := targetRooted.nonempty
    have targetNoCommon :=
      (RegionPath.rooted_iff_not_commonHead _).mp
        ⟨targetNonempty, targetRooted.2⟩ |>.2
    have sourceLength : 2 ≤
        (source.incidencePaths wire.index.val sourceIndex).length := by
      rw [lengthEq]
      exact targetRooted.1
    have sourceNonempty :
        source.incidencePaths wire.index.val sourceIndex ≠ [] := by
      rw [← List.length_pos_iff]
      omega
    have sourceNoCommon : ¬ RegionPath.CommonHead
        (source.incidencePaths wire.index.val sourceIndex) :=
      fun sourceCommon => targetNoCommon (commonIff.mp sourceCommon)
    exact ⟨sourceLength,
      ((RegionPath.rooted_iff_not_commonHead _).mpr
        ⟨sourceNonempty, sourceNoCommon⟩).2⟩

/-- A region isomorphism preserves rooted two-endedness of corresponding
inherited wires. -/
theorem RegionIso.rootedTwo_incidencePaths_iff
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target)
    {signature} (wire : Var sourceWires signature) :
    RegionPath.RootedTwo (source.incidencePaths wire.index.val) ↔
      RegionPath.RootedTwo
        (target.incidencePaths (ambient wire).index.val) := by
  cases iso with
  | @mk _ _ sourceLocals targetLocals _ sourceItems targetItems
      locals items =>
      simpa only [Region.incidencePaths, WireEquiv.append_apply_left,
        Var.index_appendLeft] using
        items.rootedTwo_incidencePaths_iff_core
          (wire.appendLeft sourceLocals) 0 0

/-- A region isomorphism fixing the inherited interface preserves the exact
number of incidences of each inherited wire. -/
theorem RegionIso.incidencePaths_length_eq
    {source target : Region outer}
    (iso : RegionIso (WireEquiv.refl outer) source target)
    {signature} (wire : Var outer signature) :
    (source.incidencePaths wire.index.val).length =
      (target.incidencePaths wire.index.val).length := by
  simpa only [WireEquiv.refl_apply] using
    iso.incidencePaths_length_eq_core wire

private theorem ItemSeq.childrenCanonical_iff_get
    (items : ItemSeq wires) :
    items.ChildrenCanonical ↔
      ∀ position : Fin items.length,
        (items.get position).ChildrenCanonical := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    items.ChildrenCanonical ↔
      ∀ position : Fin items.length,
        (items.get position).ChildrenCanonical
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro context; constructor
        · intro _ position
          exact Fin.elim0 position
        · intro _
          trivial)
    (by
      intro context head tail _ tailIff
      constructor
      · rintro ⟨headCanonical, tailCanonical⟩ position
        exact Fin.cases headCanonical
          (fun tailPosition => tailIff.mp tailCanonical tailPosition)
          position
      · intro allCanonical
        constructor
        · exact allCanonical ⟨0, by simp [ItemSeq.length]⟩
        · apply tailIff.mpr
          intro position
          exact allCanonical position.succ)
    items

private def RegionCanonicalMotive
    {sourceOuter targetOuter : List Sig}
    (ambient : WireEquiv sourceOuter targetOuter)
    (source : Region sourceOuter) (target : Region targetOuter)
    (_ : RegionIso ambient source target) : Prop :=
  source.Canonical → target.Canonical

private def ItemChildrenCanonicalMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : Item sourceWires) (target : Item targetWires)
    (_ : ItemIso ambient source target) : Prop :=
  source.ChildrenCanonical → target.ChildrenCanonical

private def ItemsChildrenCanonicalMotive
    {sourceWires targetWires : List Sig}
    (ambient : WireEquiv sourceWires targetWires)
    (source : ItemSeq sourceWires) (target : ItemSeq targetWires)
    (_ : ItemSeqIso ambient source target) : Prop :=
  source.ChildrenCanonical → target.ChildrenCanonical

private theorem regionCanonicalCase
    {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
    {ambient : WireEquiv sourceOuter targetOuter}
    {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
    {targetItems : ItemSeq (targetOuter ++ targetLocals)}
    (locals : WireEquiv sourceLocals targetLocals)
    (items : ItemSeqIso (ambient.append locals) sourceItems targetItems)
    (itemsIH : ItemsChildrenCanonicalMotive
      (ambient.append locals) sourceItems targetItems items) :
    RegionCanonicalMotive ambient (.mk sourceLocals sourceItems)
      (.mk targetLocals targetItems) (.mk locals items) := by
  rintro ⟨sourceRoots, sourceChildren⟩
  constructor
  · intro targetLocalIndex
    let targetLocal := Var.ofIndex targetLocalIndex
    let sourceLocal := locals.symm targetLocal
    have sourceRoot : RegionPath.RootedTwo
        (sourceItems.incidencePaths
          (Var.appendRight sourceOuter sourceLocal).index.val 0) := by
      simpa only [Var.index_appendRight] using
        sourceRoots sourceLocal.index
    have transported :=
      (items.rootedTwo_incidencePaths_iff_core
        (Var.appendRight sourceOuter sourceLocal) 0 0).mp sourceRoot
    dsimp only [sourceLocal, targetLocal] at transported
    simpa only [WireEquiv.append_apply_right,
      WireEquiv.apply_symm_apply, Var.index_appendRight,
      Var.index_ofIndex] using transported
  · exact itemsIH sourceChildren

private theorem atomChildrenCanonicalCase
    {sourceWires targetWires arguments : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceHead : Var sourceWires (.rel arguments)}
    {targetHead : Var targetWires (.rel arguments)}
    {sourcePorts : Vars sourceWires arguments}
    {targetPorts : Vars targetWires arguments}
    (headEq : ambient sourceHead = targetHead)
    (portsEq : sourcePorts.map (fun wire => ambient wire) = targetPorts) :
    ItemChildrenCanonicalMotive ambient (.atom sourceHead sourcePorts)
      (.atom targetHead targetPorts) (.atom headEq portsEq) :=
  fun _ => True.intro

private theorem identityChildrenCanonicalCase
    {sourceWires targetWires : List Sig} {signature : Sig} {arity : Nat}
    {ambient : WireEquiv sourceWires targetWires}
    {sourcePorts : Fin arity → Var sourceWires signature}
    {targetPorts : Fin arity → Var targetWires signature}
    (positions : FiniteEquiv (Fin arity) (Fin arity))
    (portsEq : ∀ sourceIndex,
      ambient (sourcePorts sourceIndex) = targetPorts (positions sourceIndex)) :
    ItemChildrenCanonicalMotive ambient
      (.identity signature arity sourcePorts)
      (.identity signature arity targetPorts)
      (.identity positions portsEq) :=
  fun _ => True.intro

private theorem cutChildrenCanonicalCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {sourceBody : Region sourceWires} {targetBody : Region targetWires}
    (body : RegionIso ambient sourceBody targetBody)
    (bodyIH : RegionCanonicalMotive ambient sourceBody targetBody body) :
    ItemChildrenCanonicalMotive ambient (.cut sourceBody) (.cut targetBody)
      (.cut body) := bodyIH

private theorem permuteChildrenCanonicalCase
    {sourceWires targetWires : List Sig}
    {ambient : WireEquiv sourceWires targetWires}
    {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length), positions sourceIndex = targetIndex →
      ItemIso ambient (source.get sourceIndex) (target.get targetIndex))
    (itemsIH : ∀ (sourceIndex : Fin source.length)
      (targetIndex : Fin target.length)
      (equality : positions sourceIndex = targetIndex),
      ItemChildrenCanonicalMotive ambient (source.get sourceIndex)
        (target.get targetIndex) (items sourceIndex targetIndex equality)) :
    ItemsChildrenCanonicalMotive ambient source target
      (.permute positions items) := by
  intro sourceCanonical
  apply (ItemSeq.childrenCanonical_iff_get target).mpr
  have sourceAll := (ItemSeq.childrenCanonical_iff_get source).mp
    sourceCanonical
  intro targetPosition
  let sourcePosition := positions.symm targetPosition
  have positionEq : positions sourcePosition = targetPosition :=
    positions.right_inv targetPosition
  exact itemsIH sourcePosition targetPosition positionEq
    (sourceAll sourcePosition)

private theorem RegionIso.canonical_forward
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target) :
    source.Canonical → target.Canonical := by
  exact RegionIso.rec
    (motive_1 := RegionCanonicalMotive)
    (motive_2 := ItemChildrenCanonicalMotive)
    (motive_3 := ItemsChildrenCanonicalMotive)
    regionCanonicalCase atomChildrenCanonicalCase
    identityChildrenCanonicalCase cutChildrenCanonicalCase
    permuteChildrenCanonicalCase iso

/-- Region isomorphism preserves canonicality in both directions. -/
theorem RegionIso.canonical_iff
    {ambient : WireEquiv sourceWires targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (iso : RegionIso ambient source target) :
    source.Canonical ↔ target.Canonical := by
  exact ⟨iso.canonical_forward, iso.symm.canonical_forward⟩

/-- The structural scope properties preserved by a region transformation. -/
structure ScopePreservation
    (source target : Region wires) : Prop where
  canonical : source.Canonical → target.Canonical
  incidenceNonempty : ∀ {signature} (wire : Var wires signature),
    source.incidencePaths wire.index.val ≠ [] ↔
      target.incidencePaths wire.index.val ≠ []
  rootedTwo : ∀ {signature} (wire : Var wires signature),
    RegionPath.RootedTwo (source.incidencePaths wire.index.val) →
      RegionPath.RootedTwo (target.incidencePaths wire.index.val)

/-- Adjoining an empty host leaves each material incidence path unchanged. -/
theorem Region.incidencePaths_adjoinAt_nil
    (material : Region (outer ++ hostLocals))
    (wire : Var (outer ++ hostLocals) signature) :
    (Region.adjoinAt hostLocals .nil material).incidencePaths
        wire.index.val =
      material.incidencePaths wire.index.val := by
  cases material with
  | mk addedLocals addedItems =>
      let materialWire := wire.appendLeft addedLocals
      have renamed := ItemSeq.incidencePaths_renameWires_adjoinMaterial
        (outer := outer) (hostLocals := hostLocals)
        (addedLocals := addedLocals) addedItems materialWire 0
      simpa [Region.adjoinAt, Region.incidencePaths, materialWire] using renamed

/-- The empty-local presentation preserves every inherited incidence path. -/
theorem Region.incidencePaths_ofItems
    (items : ItemSeq wires) (wire : Var wires signature) :
    (Region.ofItems items).incidencePaths wire.index.val =
      items.incidencePaths wire.index.val 0 := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun inherited => inherited.appendLeft []⟩
  have renamed := ItemSeq.incidencePaths_renameWires_preservesIndex items
    appendNil (by simp) (by
      intro inheritedSignature inherited
      simp [appendNil]) wire 0
  simpa [Region.ofItems, Region.incidencePaths, appendNil] using renamed

/-- A singleton cut is canonical exactly when its body is canonical. -/
theorem Region.singleton_cut_canonical_iff
    (body : Region wires) :
    (Region.singleton (.cut body)).Canonical ↔ body.Canonical := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  change (Region.ofItems (.cons (.cut body) .nil)).Canonical ↔
    body.Canonical
  simp only [Region.ofItems, Region.Canonical, ItemSeq.ChildrenCanonical,
    ItemSeq.renameWires, Item.renameWires, Item.ChildrenCanonical, and_true]
  constructor
  · rintro ⟨_, childCanonical⟩
    exact (Region.Canonical.renameWires_iff body appendNil).mp childCanonical
  · intro childCanonical
    constructor
    · intro localIndex
      exact Fin.elim0 localIndex
    · exact (Region.Canonical.renameWires_iff body appendNil).mpr
        childCanonical

/-- The incidence paths of a singleton cut are its body's paths below index zero. -/
theorem Region.incidencePaths_singleton_cut
    (body : Region wires) (wire : Var wires signature) :
    (Region.singleton (.cut body)).incidencePaths wire.index.val =
      (body.incidencePaths wire.index.val).map (List.cons 0) := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun inherited => inherited.appendLeft []⟩
  have renamed := ItemSeq.incidencePaths_renameWires_preservesIndex
    (.cons (.cut body) .nil) appendNil (by simp)
    (by intro inheritedSignature inherited; simp [appendNil]) wire 0
  simpa [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.incidencePaths, Item.incidencePaths, appendNil] using renamed

/-- Canonical empty-host adjoining supplies rootedness for each host local. -/
theorem Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
    (material : Region (outer ++ hostLocals))
    (canonical : (Region.adjoinAt hostLocals .nil material).Canonical)
    (localIndex : Fin hostLocals.length) :
    RegionPath.RootedTwo
      (material.incidencePaths (outer.length + localIndex.val)) := by
  cases material with
  | mk addedLocals addedItems =>
      let localWire := Var.appendRight outer (Var.ofIndex localIndex)
      let combinedIndex : Fin (hostLocals ++ addedLocals).length :=
        ⟨localIndex.val, by
          simp only [List.length_append]
          exact Nat.lt_of_lt_of_le localIndex.isLt
            (Nat.le_add_right _ _)⟩
      have sourceRoot := canonical.1 combinedIndex
      have paths := Region.incidencePaths_adjoinAt_nil
        (Region.mk addedLocals addedItems) localWire
      rw [show localWire.index.val = outer.length + localIndex.val by
        simp [localWire]] at paths
      rw [← paths]
      simpa [Region.adjoinAt, Region.Canonical, localWire, combinedIndex] using
        sourceRoot

/-- Conjoin host items with material, retaining the material's inherited interface. -/
def hostedMaterial
    (hostItems : ItemSeq wires)
    (material : Region wires) : Region wires :=
  (Region.ofItems hostItems).conjoin material

/-- Hosting material preserves its structural scope invariant. -/
theorem hostedMaterial_scope
    (hostItems : ItemSeq wires)
    (sourceMaterial targetMaterial : Region wires)
    (materialScope : ScopePreservation sourceMaterial targetMaterial) :
    ScopePreservation
      (hostedMaterial hostItems sourceMaterial)
      (hostedMaterial hostItems targetMaterial) := by
  let host := Region.ofItems hostItems
  have combined := Region.conjoin_preserves_scope
    host sourceMaterial host targetMaterial
    (fun canonical => canonical) materialScope.canonical
    (fun _ => Iff.rfl) materialScope.incidenceNonempty
    (fun _ rooted => rooted) materialScope.rootedTwo
  exact {
    canonical := combined.1
    incidenceNonempty := fun wire => (combined.2 wire).1
    rootedTwo := fun wire => (combined.2 wire).2
  }

/-- Re-express adjoining a host as empty-host adjoining of hosted material. -/
theorem adjoinAt_hostedMaterial
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) :
    Region.adjoinAt hostLocals hostItems material =
      Region.adjoinAt hostLocals .nil
        (hostedMaterial hostItems material) := by
  cases material with
  | mk materialLocals materialItems =>
      let appendNil : WireRenaming (outer ++ hostLocals)
          ((outer ++ hostLocals) ++ []) :=
        ⟨fun wire => wire.appendLeft []⟩
      have hostMap : WireRenaming.comp
          (Region.adjoinMaterialWire outer hostLocals materialLocals)
          (WireRenaming.comp
            (Region.conjoinLeftWire (outer ++ hostLocals) [] materialLocals)
            appendNil) =
          Region.adjoinHostWire outer hostLocals materialLocals := by
        apply WireRenaming.ext
        intro signature wire
        apply Var.appendCases (left := outer) (right := hostLocals)
          (motive := fun wire =>
            WireRenaming.comp
                (Region.adjoinMaterialWire outer hostLocals materialLocals)
                (WireRenaming.comp
                  (Region.conjoinLeftWire (outer ++ hostLocals) []
                    materialLocals) appendNil) wire =
              Region.adjoinHostWire outer hostLocals materialLocals wire)
        · intro inheritedSignature inherited
          simp [WireRenaming.comp, appendNil, Region.conjoinLeftWire,
            Region.adjoinMaterialWire, Region.adjoinHostWire]
        · intro localSignature localWire
          simp [WireRenaming.comp, appendNil, Region.conjoinLeftWire,
            Region.adjoinMaterialWire, Region.adjoinHostWire]
      have materialMap : WireRenaming.comp
          (Region.adjoinMaterialWire outer hostLocals materialLocals)
          (Region.conjoinRightWire (outer ++ hostLocals) [] materialLocals) =
          Region.adjoinMaterialWire outer hostLocals materialLocals := by
        apply WireRenaming.ext
        intro signature wire
        apply Var.appendCases (left := outer ++ hostLocals)
          (right := materialLocals)
          (motive := fun wire =>
            WireRenaming.comp
                (Region.adjoinMaterialWire outer hostLocals materialLocals)
                (Region.conjoinRightWire (outer ++ hostLocals) []
                  materialLocals) wire =
              Region.adjoinMaterialWire outer hostLocals materialLocals wire)
        · intro inheritedSignature inherited
          simp [WireRenaming.comp, Region.conjoinRightWire,
            Region.adjoinMaterialWire]
        · intro localSignature localWire
          apply Var.eq_of_index_eq
          apply Fin.ext
          simp [WireRenaming.comp, Region.conjoinRightWire,
            Region.adjoinMaterialWire]
          simpa only [List.length_nil, Nat.zero_add] using
            (Var.index_appendRight ([] : List Sig) localWire)
      simp only [hostedMaterial, Region.ofItems, Region.conjoin,
        Region.adjoinAt, ItemSeq.renameWires_append,
        ItemSeq.renameWires_comp, ItemSeq.renameWires,
        ItemSeq.nil_append, List.nil_append]
      rw [hostMap, materialMap]

/-- Adjoining an unchanged host preserves material structural scope. -/
theorem adjoinAt_preserves_scope
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (sourceMaterial targetMaterial : Region (outer ++ hostLocals))
    (materialScope : ScopePreservation sourceMaterial targetMaterial) :
    ScopePreservation
      (Region.adjoinAt hostLocals hostItems sourceMaterial)
      (Region.adjoinAt hostLocals hostItems targetMaterial) := by
  let sourceHosted := hostedMaterial hostItems sourceMaterial
  let targetHosted := hostedMaterial hostItems targetMaterial
  have sourceEq : Region.adjoinAt hostLocals hostItems sourceMaterial =
      Region.adjoinAt hostLocals .nil sourceHosted := by
    simpa only [sourceHosted] using
      adjoinAt_hostedMaterial hostLocals hostItems sourceMaterial
  have targetEq : Region.adjoinAt hostLocals hostItems targetMaterial =
      Region.adjoinAt hostLocals .nil targetHosted := by
    simpa only [targetHosted] using
      adjoinAt_hostedMaterial hostLocals hostItems targetMaterial
  have hostedScope : ScopePreservation sourceHosted targetHosted := by
    exact hostedMaterial_scope hostItems sourceMaterial targetMaterial
      materialScope
  constructor
  · intro sourceCanonical
    have sourceAdjoinedCanonical :
        (Region.adjoinAt hostLocals .nil sourceHosted).Canonical := by
      rw [← sourceEq]
      exact sourceCanonical
    have sourceHostedCanonical : sourceHosted.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals .nil sourceHosted
        sourceAdjoinedCanonical
    have targetHostedCanonical : targetHosted.Canonical :=
      hostedScope.canonical sourceHostedCanonical
    rw [targetEq]
    apply Region.Canonical.adjoinAt_of_material_roots hostLocals .nil
      targetHosted True.intro targetHostedCanonical
    intro localIndex
    let localWire := Var.appendRight outer (Var.ofIndex localIndex)
    have sourceRoot : RegionPath.RootedTwo
        (sourceHosted.incidencePaths localWire.index.val) := by
      simpa [localWire] using
        Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
          sourceHosted sourceAdjoinedCanonical localIndex
    have targetRoot := hostedScope.rootedTwo localWire sourceRoot
    simpa [localWire] using targetRoot
  · intro signature wire
    let hostedWire := wire.appendLeft hostLocals
    have sourcePaths := Region.incidencePaths_adjoinAt_nil sourceHosted
      hostedWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil targetHosted
      hostedWire
    have wireIndex : hostedWire.index.val = wire.index.val := by
      simp [hostedWire]
    rw [wireIndex] at sourcePaths targetPaths
    rw [sourceEq, targetEq, sourcePaths, targetPaths]
    simpa only [hostedWire, Var.index_appendLeft] using
      hostedScope.incidenceNonempty hostedWire
  · intro signature wire sourceRoot
    let hostedWire := wire.appendLeft hostLocals
    have sourcePaths := Region.incidencePaths_adjoinAt_nil sourceHosted
      hostedWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil targetHosted
      hostedWire
    have wireIndex : hostedWire.index.val = wire.index.val := by
      simp [hostedWire]
    rw [wireIndex] at sourcePaths targetPaths
    rw [sourceEq, sourcePaths] at sourceRoot
    rw [targetEq, targetPaths]
    simpa only [hostedWire, Var.index_appendLeft] using
      hostedScope.rootedTwo hostedWire (by
        simpa only [hostedWire, Var.index_appendLeft] using sourceRoot)
