import VisualProof.Diagram.FocusIsomorphism
import VisualProof.Diagram.Scope.Context
import VisualProof.Diagram.Scope.Rename

namespace VisualProof.Diagram

private def RegionPath.reindexRoot (map : Nat → Nat) :
    RegionPath → RegionPath
  | [] => []
  | head :: tail => map head :: tail

private theorem RegionPath.commonHead_map_reindexRoot_iff
    (paths : List RegionPath) (map : Nat → Nat)
    (injective : Function.Injective map) :
    RegionPath.CommonHead (paths.map (RegionPath.reindexRoot map)) ↔
      RegionPath.CommonHead paths := by
  by_cases empty : paths = []
  · subst paths
    simp [RegionPath.CommonHead]
  constructor
  · rintro ⟨mappedHead, allMapped⟩
    obtain ⟨first, firstMember⟩ := List.exists_mem_of_ne_nil paths empty
    have mappedFirst := allMapped (RegionPath.reindexRoot map first)
      (List.mem_map.mpr ⟨first, firstMember, rfl⟩)
    cases first with
    | nil => simp [RegionPath.reindexRoot, RegionPath.StartsWith] at mappedFirst
    | cons firstHead firstTail =>
        rcases mappedFirst with ⟨_, mappedFirstEq⟩
        have mappedHeadEq : mappedHead = map firstHead := by
          injection mappedFirstEq with equality
          exact equality.symm
        refine ⟨firstHead, ?_⟩
        intro path member
        have mappedPath := allMapped (RegionPath.reindexRoot map path)
          (List.mem_map.mpr ⟨path, member, rfl⟩)
        cases path with
        | nil => simp [RegionPath.reindexRoot, RegionPath.StartsWith] at mappedPath
        | cons head tail =>
            rcases mappedPath with ⟨_, mappedEq⟩
            have headEq : head = firstHead := by
              apply injective
              injection mappedEq with equality
              exact equality.trans mappedHeadEq
            exact ⟨tail, by rw [headEq]⟩
  · rintro ⟨head, allPaths⟩
    refine ⟨map head, ?_⟩
    intro path member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨tail, sourceEq⟩ := allPaths source sourceMember
    subst source
    exact ⟨tail, rfl⟩

private theorem RegionPath.rootedTwo_map_reindexRoot_iff
    (paths : List RegionPath) (map : Nat → Nat)
    (injective : Function.Injective map) :
    RegionPath.RootedTwo (paths.map (RegionPath.reindexRoot map)) ↔
      RegionPath.RootedTwo paths := by
  constructor <;> intro rooted
  · refine ⟨by simpa using rooted.1, ?_⟩
    have mappedNonempty : paths.map (RegionPath.reindexRoot map) ≠ [] :=
      rooted.nonempty
    have sourceNonempty : paths ≠ [] := by simpa using mappedNonempty
    have mappedNoCommon :=
      ((RegionPath.rooted_iff_not_commonHead _).mp
        ⟨mappedNonempty, rooted.2⟩).2
    exact ((RegionPath.rooted_iff_not_commonHead paths).mpr
      ⟨sourceNonempty,
        fun common => mappedNoCommon
          ((RegionPath.commonHead_map_reindexRoot_iff paths map injective).mpr
            common)⟩).2
  · refine ⟨by simpa using rooted.1, ?_⟩
    have sourceNonempty : paths ≠ [] := rooted.nonempty
    have mappedNonempty : paths.map (RegionPath.reindexRoot map) ≠ [] := by
      simpa using sourceNonempty
    have sourceNoCommon :=
      ((RegionPath.rooted_iff_not_commonHead paths).mp
        ⟨sourceNonempty, rooted.2⟩).2
    exact ((RegionPath.rooted_iff_not_commonHead _).mpr
      ⟨mappedNonempty,
        fun common => sourceNoCommon
          ((RegionPath.commonHead_map_reindexRoot_iff paths map injective).mp
            common)⟩).2

private theorem RegionPath.rootedTwo_of_perm
    {source target : List RegionPath} (permutation : source.Perm target)
    (rooted : RegionPath.RootedTwo source) :
    RegionPath.RootedTwo target := by
    refine ⟨by simpa [permutation.length_eq] using rooted.1, ?_⟩
    have sourceNonempty := rooted.nonempty
    have targetNonempty : target ≠ [] := by
      intro empty
      have := permutation.length_eq
      simp [empty] at this
      exact sourceNonempty this
    have sourceNoCommon :=
      ((RegionPath.rooted_iff_not_commonHead source).mp
        ⟨sourceNonempty, rooted.2⟩).2
    apply ((RegionPath.rooted_iff_not_commonHead target).mpr
      ⟨targetNonempty, ?_⟩).2
    rintro ⟨index, allTarget⟩
    exact sourceNoCommon ⟨index, fun path member =>
      allTarget path (permutation.mem_iff.mp member)⟩

private theorem RegionPath.rootedTwo_perm
    {source target : List RegionPath} (permutation : source.Perm target) :
    RegionPath.RootedTwo source ↔ RegionPath.RootedTwo target :=
  ⟨RegionPath.rootedTwo_of_perm permutation,
    RegionPath.rootedTwo_of_perm permutation.symm⟩

private def moveIndex (selected : Nat) (index : Nat) : Nat :=
  if index = selected then 0 else if index < selected then index + 1 else index

private theorem moveIndex_injective (selected : Nat) :
    Function.Injective (moveIndex selected) := by
  intro left right equal
  by_cases leftSelected : left = selected
  · subst left
    by_cases rightSelected : right = selected
    · exact rightSelected.symm
    · simp only [moveIndex, if_pos, rightSelected, if_false] at equal
      split at equal <;> omega
  · by_cases rightSelected : right = selected
    · subst right
      simp only [moveIndex, leftSelected, if_false, if_pos] at equal
      split at equal <;> omega
    · simp only [moveIndex, leftSelected, rightSelected, if_false] at equal
      by_cases leftBefore : left < selected <;>
        by_cases rightBefore : right < selected <;>
          simp [leftBefore, rightBefore] at equal <;> omega

private abbrev ItemShiftMotive (wires : List Theory.Sig)
    (item : Item wires) :=
  ∀ wireIndex itemIndex,
    item.incidencePaths wireIndex (itemIndex + 1) =
      (item.incidencePaths wireIndex itemIndex).map
        (RegionPath.reindexRoot Nat.succ)

private abbrev ItemsShiftMotive (wires : List Theory.Sig)
    (items : ItemSeq wires) :=
  ∀ wireIndex itemIndex,
    items.incidencePaths wireIndex (itemIndex + 1) =
      (items.incidencePaths wireIndex itemIndex).map
        (RegionPath.reindexRoot Nat.succ)

private theorem ItemSeq.incidencePaths_succ
    (items : ItemSeq wires) (wireIndex itemIndex : Nat) :
    items.incidencePaths wireIndex (itemIndex + 1) =
      (items.incidencePaths wireIndex itemIndex).map
        (RegionPath.reindexRoot Nat.succ) :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := ItemShiftMotive)
    (motive_3 := ItemsShiftMotive)
    (fun _ _ _ => True.intro)
    (by
      intros
      simp [ItemShiftMotive, Item.incidencePaths, RegionPath.reindexRoot])
    (by
      intros
      simp [ItemShiftMotive, Item.incidencePaths, RegionPath.reindexRoot])
    (by
      intro _ body _ wireIndex itemIndex
      simp [Item.incidencePaths, RegionPath.reindexRoot, List.map_map,
        Function.comp_def])
    (by
      intros
      simp [ItemsShiftMotive, ItemSeq.incidencePaths])
    (by
      intro _ head tail headIH tailIH wireIndex itemIndex
      simp only [ItemSeq.incidencePaths, List.map_append]
      rw [headIH wireIndex itemIndex, tailIH wireIndex (itemIndex + 1)])
    items wireIndex itemIndex

private abbrev ItemBoundsMotive (wires : List Theory.Sig)
    (item : Item wires) :=
  ∀ wireIndex itemIndex path,
    path ∈ item.incidencePaths wireIndex itemIndex →
      path = [] ∨ ∃ tail, path = itemIndex :: tail

private abbrev ItemsBoundsMotive (wires : List Theory.Sig)
    (items : ItemSeq wires) :=
  ∀ wireIndex itemIndex path,
    path ∈ items.incidencePaths wireIndex itemIndex →
      path = [] ∨ ∃ head tail,
        path = head :: tail ∧ itemIndex ≤ head ∧
          head < itemIndex + items.length

private theorem ItemSeq.incidencePath_bounds
    (items : ItemSeq wires) (wireIndex itemIndex : Nat)
    (path : RegionPath)
    (member : path ∈ items.incidencePaths wireIndex itemIndex) :
    path = [] ∨ ∃ head tail,
      path = head :: tail ∧ itemIndex ≤ head ∧
        head < itemIndex + items.length :=
  ItemSeq.rec
    (motive_1 := fun _ _ => True)
    (motive_2 := ItemBoundsMotive)
    (motive_3 := ItemsBoundsMotive)
    (fun _ _ _ => True.intro)
    (by
      intro _ _ _ _ wireIndex itemIndex path member
      left
      simpa [Item.incidencePaths] using
        (List.eq_of_mem_replicate member))
    (by
      intro _ _ _ _ wireIndex itemIndex path member
      left
      simpa [Item.incidencePaths] using
        (List.eq_of_mem_replicate member))
    (by
      intro _ body _ wireIndex itemIndex path member
      right
      obtain ⟨tail, _, rfl⟩ := List.mem_map.mp
        (show path ∈ (body.incidencePaths wireIndex).map
          (List.cons itemIndex) from member)
      exact ⟨tail, rfl⟩)
    (by intros; simp [ItemsBoundsMotive, ItemSeq.incidencePaths] at *)
    (by
      intro _ head tail headIH tailIH wireIndex itemIndex path member
      simp only [ItemSeq.incidencePaths, List.mem_append] at member
      rcases member with headMember | tailMember
      · rcases headIH wireIndex itemIndex path headMember with
          empty | ⟨pathTail, pathEq⟩
        · exact Or.inl empty
        · exact Or.inr ⟨itemIndex, pathTail, pathEq,
            Nat.le_refl _, by simp [ItemSeq.length]⟩
      · rcases tailIH wireIndex (itemIndex + 1) path tailMember with
          empty | ⟨pathHead, pathTail, pathEq, lower, upper⟩
        · exact Or.inl empty
        · exact Or.inr ⟨pathHead, pathTail, pathEq,
            Nat.le_trans (Nat.le_succ itemIndex) lower, by
              simp only [ItemSeq.length]
              omega⟩)
    items wireIndex itemIndex path member

private theorem reindex_before
    (before : ItemSeq wires) (wireIndex : Nat) :
    (before.incidencePaths wireIndex 0).map
        (RegionPath.reindexRoot (moveIndex before.length)) =
      before.incidencePaths wireIndex 1 := by
  rw [ItemSeq.incidencePaths_succ before wireIndex 0]
  apply List.map_congr_left
  intro path member
  rcases ItemSeq.incidencePath_bounds before wireIndex 0 path member with
    rfl | ⟨head, tail, rfl, _, upper⟩
  · rfl
  · have headBefore : head < before.length := by omega
    simp [RegionPath.reindexRoot, moveIndex,
      Nat.ne_of_lt headBefore, headBefore]

private theorem reindex_after
    (after : ItemSeq wires) (wireIndex selected : Nat) :
    (after.incidencePaths wireIndex (selected + 1)).map
        (RegionPath.reindexRoot (moveIndex selected)) =
      after.incidencePaths wireIndex (selected + 1) := by
  calc
    _ = (after.incidencePaths wireIndex (selected + 1)).map id := by
      apply List.map_congr_left
      intro path member
      rcases ItemSeq.incidencePath_bounds after wireIndex (selected + 1)
          path member with rfl | ⟨head, tail, rfl, lower, _⟩
      · rfl
      · have headNe : head ≠ selected := by omega
        have headNotBefore : ¬head < selected := by omega
        simp [RegionPath.reindexRoot, moveIndex, headNe, headNotBefore]
    _ = _ := List.map_id _

private theorem move_identity_paths_perm
    (before after : ItemSeq wires) (signature : Theory.Sig)
    (arity : Nat) (ports : Fin arity → Theory.Var wires signature)
    (wireIndex : Nat) :
    let source : ItemSeq wires := before.append
      (ItemSeq.cons (.identity signature arity ports) after)
    let target : ItemSeq wires := ItemSeq.cons (.identity signature arity ports)
      (before.append after)
    (source.incidencePaths wireIndex 0).map
        (RegionPath.reindexRoot (moveIndex before.length)) |>.Perm
      (target.incidencePaths wireIndex 0) := by
  dsimp only
  rw [ItemSeq.incidencePaths_append]
  simp only [ItemSeq.incidencePaths, Item.incidencePaths,
    Nat.zero_add, List.map_append, List.map_replicate,
    RegionPath.reindexRoot]
  rw [reindex_before, reindex_after]
  simp only [ItemSeq.incidencePaths_append]
  rw [Nat.add_comm 1 before.length]
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.Perm.append_right _ List.perm_append_comm

private theorem WireEquiv.focusedAt_index
    (outer locals : List Theory.Sig)
    (wire : Theory.Var (outer ++ locals) signature) :
    (((WireEquiv.refl outer).append (WireEquiv.appendNil locals)) wire).index.val =
      wire.index.val := by
  apply Theory.Var.appendCases (left := outer) (right := locals)
    (motive := fun wire =>
      (((WireEquiv.refl outer).append
        (WireEquiv.appendNil locals)) wire).index.val = wire.index.val)
  · intro signature inherited
    simp [WireEquiv.append_apply_left]
  · intro signature localWire
    simp [WireEquiv.append_apply_right, WireEquiv.appendNil]

theorem Region.focusedAt_canonical_iff
    {outer locals : List Theory.Sig}
    {items : ItemSeq (outer ++ locals)}
    (focus : ItemSeq.Focus items) :
    (Region.focusedAt locals focus).Canonical ↔
      (Region.mk locals
        (.cons focus.item (focus.before.append focus.after))).Canonical := by
  rw [Region.focusedAt_eq focus]
  simp only [Region.Canonical]
  let equivalence :=
    (WireEquiv.refl outer).append (WireEquiv.appendNil locals)
  let sourceItems := ItemSeq.cons focus.item (focus.before.append focus.after)
  have lengthEq : (outer ++ locals).length =
      (outer ++ (locals ++ [])).length := by simp
  have preserves : ∀ {signature}
      (wire : Theory.Var (outer ++ locals) signature),
      (equivalence wire).index.val = wire.index.val :=
    fun wire => WireEquiv.focusedAt_index outer locals wire
  have childrenIff :=
    ItemSeq.ChildrenCanonical.renameWires_preservesIndex_iff
      sourceItems equivalence.toRenaming lengthEq preserves
  have pathsEq : ∀ {signature}
      (wire : Theory.Var (outer ++ locals) signature),
      (sourceItems.renameWires equivalence.toRenaming).incidencePaths
          wire.index.val 0 = sourceItems.incidencePaths wire.index.val 0 :=
    fun wire => ItemSeq.incidencePaths_renameWires_preservesIndex sourceItems
      equivalence.toRenaming lengthEq preserves wire 0
  constructor
  · rintro ⟨roots, children⟩
    constructor
    · intro localIndex
      let targetIndex : Fin (locals ++ []).length := Fin.cast (by simp) localIndex
      let sourceWire := Theory.Var.appendRight outer
        (Theory.Var.ofIndex localIndex)
      have path := pathsEq sourceWire
      have sourceIndex : sourceWire.index.val =
          outer.length + localIndex.val := by simp [sourceWire]
      rw [← sourceIndex, ← path, sourceIndex]
      simpa [targetIndex] using roots targetIndex
    · exact childrenIff.mp children
  · rintro ⟨roots, children⟩
    constructor
    · intro localIndex
      let sourceLocalIndex : Fin locals.length := Fin.cast (by simp) localIndex
      let sourceWire := Theory.Var.appendRight outer
        (Theory.Var.ofIndex sourceLocalIndex)
      have path := pathsEq sourceWire
      have sourceIndex : sourceWire.index.val =
          outer.length + sourceLocalIndex.val := by simp [sourceWire]
      have indexVal : localIndex.val = sourceLocalIndex.val := rfl
      rw [indexVal, ← sourceIndex, path, sourceIndex]
      exact roots sourceLocalIndex
    · exact childrenIff.mpr children

theorem Region.focusedAt_nonempty_iff
    {outer locals : List Theory.Sig}
    {items : ItemSeq (outer ++ locals)}
    (focus : ItemSeq.Focus items)
    (wire : Theory.Var outer signature) :
    (Region.focusedAt locals focus).incidencePaths wire.index.val ≠ [] ↔
      (Region.mk locals
        (.cons focus.item (focus.before.append focus.after))).incidencePaths
          wire.index.val ≠ [] := by
  rw [Region.focusedAt_eq focus]
  let equivalence :=
    (WireEquiv.refl outer).append (WireEquiv.appendNil locals)
  let sourceItems := ItemSeq.cons focus.item (focus.before.append focus.after)
  have lengthEq : (outer ++ locals).length =
      (outer ++ (locals ++ [])).length := by simp
  have preserves : ∀ {signature}
      (sourceWire : Theory.Var (outer ++ locals) signature),
      (equivalence sourceWire).index.val = sourceWire.index.val :=
    fun sourceWire => WireEquiv.focusedAt_index outer locals sourceWire
  have pathsEq := ItemSeq.incidencePaths_renameWires_preservesIndex
    sourceItems equivalence.toRenaming lengthEq preserves
      (wire.appendLeft locals) 0
  have regionPathsEq :
      (Region.mk (locals ++ [])
        (sourceItems.renameWires equivalence.toRenaming)).incidencePaths
          wire.index.val =
        (Region.mk locals sourceItems).incidencePaths wire.index.val := by
    simpa [Region.incidencePaths] using pathsEq
  rw [regionPathsEq]

theorem Region.moveIdentityFront_canonical_iff
    (locals : List Theory.Sig) (before after : ItemSeq (outer ++ locals))
    (signature : Theory.Sig) (arity : Nat)
    (ports : Fin arity → Theory.Var (outer ++ locals) signature) :
    (Region.mk locals
      (ItemSeq.cons (.identity signature arity ports)
        (before.append after))).Canonical ↔
    (Region.mk locals
      (before.append (.cons (.identity signature arity ports) after))).Canonical := by
  simp only [Region.Canonical]
  constructor <;> rintro ⟨roots, children⟩
  · constructor
    · intro localIndex
      let wireIndex := outer.length + localIndex.val
      have permutation := move_identity_paths_perm before after signature
        arity ports wireIndex
      exact (RegionPath.rootedTwo_map_reindexRoot_iff
        (ItemSeq.incidencePaths wireIndex 0
          (before.append (.cons (.identity signature arity ports) after)))
        (moveIndex before.length) (moveIndex_injective before.length)).mp
          ((RegionPath.rootedTwo_perm permutation).mpr (roots localIndex))
    · simpa [ItemSeq.ChildrenCanonical,
        ItemSeq.childrenCanonical_append, Item.ChildrenCanonical] using children
  · constructor
    · intro localIndex
      let wireIndex := outer.length + localIndex.val
      have permutation := move_identity_paths_perm before after signature
        arity ports wireIndex
      exact (RegionPath.rootedTwo_perm permutation).mp
        ((RegionPath.rootedTwo_map_reindexRoot_iff
          (ItemSeq.incidencePaths wireIndex 0
            (before.append (.cons (.identity signature arity ports) after)))
          (moveIndex before.length) (moveIndex_injective before.length)).mpr
            (roots localIndex))
    · simpa [ItemSeq.ChildrenCanonical,
        ItemSeq.childrenCanonical_append, Item.ChildrenCanonical] using children

theorem Region.moveIdentityFront_nonempty_iff
    (locals : List Theory.Sig) (before after : ItemSeq (outer ++ locals))
    (signature : Theory.Sig) (arity : Nat)
    (ports : Fin arity → Theory.Var (outer ++ locals) signature)
    (wireIndex : Nat) :
    Region.incidencePaths wireIndex (Region.mk locals
      (ItemSeq.cons (.identity signature arity ports)
        (before.append after))) ≠ [] ↔
    Region.incidencePaths wireIndex (Region.mk locals
      (before.append (.cons (.identity signature arity ports) after)))
        ≠ [] := by
  have permutation := move_identity_paths_perm before after signature
    arity ports wireIndex
  let sourcePaths := Region.incidencePaths wireIndex (Region.mk locals
    (before.append (.cons (.identity signature arity ports) after)))
  let targetPaths := Region.incidencePaths wireIndex (Region.mk locals
    (ItemSeq.cons (.identity signature arity ports) (before.append after)))
  have length_eq : sourcePaths.length = targetPaths.length := by
    simpa [sourcePaths, targetPaths] using permutation.length_eq
  constructor
  · intro targetNonempty sourceEmpty
    apply targetNonempty
    have sourceEmpty' : sourcePaths = [] := by
      simpa [sourcePaths] using sourceEmpty
    apply List.eq_nil_of_length_eq_zero
    rw [← length_eq]
    simp [sourceEmpty']
  · intro sourceNonempty targetEmpty
    apply sourceNonempty
    have targetEmpty' : targetPaths = [] := by
      simpa [targetPaths] using targetEmpty
    apply List.eq_nil_of_length_eq_zero
    rw [length_eq]
    simp [targetEmpty']

theorem DiagramContext.moveIdentityFrontValidity
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (locals : List Theory.Sig) (before after : ItemSeq (outer ++ locals))
    (signature : Theory.Sig) (arity : Nat)
    (ports : Fin arity → Theory.Var (outer ++ locals) signature)
    (sourceCanonical :
      Region.Canonical (context.fill (.mk locals
        (before.append (.cons (.identity signature arity ports) after)))))
    (sourceExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (.mk locals
        (before.append (.cons (.identity signature arity ports) after))))) :
    let target := Region.mk locals
      (ItemSeq.cons (.identity signature arity ports) (before.append after))
    (context.fill target).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill target) := by
  let source := Region.mk locals
    (before.append (.cons (.identity signature arity ports) after))
  let target := Region.mk locals
    (ItemSeq.cons (.identity signature arity ports) (before.append after))
  have localSource := context.holeCanonical source sourceCanonical
  have localTarget := (Region.moveIdentityFront_canonical_iff locals before
    after signature arity ports).mpr localSource
  have localNonempty := Region.moveIdentityFront_nonempty_iff locals before
    after signature arity ports
  have replaced := context.replaceCanonical source target sourceCanonical
    localTarget (fun wire => (localNonempty wire.index.val).symm)
  let sourceOpen := interface.withBody (context.fill source)
    sourceCanonical sourceExternal
  exact ⟨replaced.1,
    sourceOpen.externalTwoEnded_of_nonempty_iff
      (context.fill target) replaced.2⟩

/-- Presenting a selected identity as the zero-local leading block used by
`NestedOccurrence` preserves the complete endpoint validity. -/
theorem DiagramContext.focusIdentityValidity
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (locals : List Theory.Sig) (before after : ItemSeq (outer ++ locals))
    (signature : Theory.Sig) (arity : Nat)
    (ports : Fin arity → Theory.Var (outer ++ locals) signature)
    (sourceCanonical :
      Region.Canonical (context.fill (.mk locals
        (before.append (.cons (.identity signature arity ports) after)))))
    (sourceExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (.mk locals
        (before.append (.cons (.identity signature arity ports) after))))) :
    let focus : ItemSeq.Focus
        (before.append (.cons (.identity signature arity ports) after)) := {
      before := before
      item := .identity signature arity ports
      after := after
      rebuild := rfl
    }
    let target := Region.focusedAt locals focus
    (context.fill target).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill target) := by
  let focus : ItemSeq.Focus
      (before.append (.cons (.identity signature arity ports) after)) := {
    before := before
    item := .identity signature arity ports
    after := after
    rebuild := rfl
  }
  let front := Region.mk locals
    (.cons (.identity signature arity ports) (before.append after))
  let target := Region.focusedAt locals focus
  have frontValidity := context.moveIdentityFrontValidity interface locals
    before after signature arity ports sourceCanonical sourceExternal
  have targetCanonical : target.Canonical :=
    (Region.focusedAt_canonical_iff focus).mpr
      (context.holeCanonical front frontValidity.1)
  have sameNonempty := fun {wireSignature}
      (wire : Theory.Var outer wireSignature) =>
    Region.focusedAt_nonempty_iff focus wire
  have replaced := context.replaceCanonical front target frontValidity.1
    targetCanonical (fun wire => (sameNonempty wire).symm)
  let frontOpen := interface.withBody (context.fill front)
    frontValidity.1 frontValidity.2
  exact ⟨replaced.1,
    frontOpen.externalTwoEnded_of_nonempty_iff
      (context.fill target) replaced.2⟩

end VisualProof.Diagram
