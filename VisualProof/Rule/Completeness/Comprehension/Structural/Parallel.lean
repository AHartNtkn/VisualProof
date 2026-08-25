import VisualProof.Diagram.Scope.Isomorphism

namespace VisualProof.Rule.Completeness.Comprehension.Structural

open Diagram
open Theory

structure SupportParallelIncidenceScope
    (sourcePaths targetPaths : List RegionPath) : Prop where
  nonempty : sourcePaths ≠ [] ↔ targetPaths ≠ []
  rooted : RegionPath.RootedTwo sourcePaths →
    RegionPath.RootedTwo targetPaths

theorem SupportParallelIncidenceScope.refl
    (paths : List RegionPath) : SupportParallelIncidenceScope paths paths :=
  ⟨Iff.rfl, fun rooted => rooted⟩

theorem supportParallelStartsWithOfMemIncidencePathsLt
    (items : ItemSeq wires) (wireIndex itemIndex : Nat)
    {path : RegionPath} {index : Nat}
    (member : path ∈ items.incidencePaths wireIndex itemIndex)
    (starts : RegionPath.StartsWith index path) :
    index < itemIndex + items.length := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ (wireIndex itemIndex : Nat) {path : RegionPath} {index : Nat},
      path ∈ items.incidencePaths wireIndex itemIndex →
        RegionPath.StartsWith index path →
          index < itemIndex + items.length
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by
      intro _ wireIndex itemIndex path index member starts
      simp only [ItemSeq.incidencePaths, List.not_mem_nil] at member)
    (by
      intro _ head tail _ tailInduction wireIndex itemIndex path index
        member starts
      simp only [ItemSeq.incidencePaths, List.mem_append] at member
      rcases member with headMember | tailMember
      · cases head with
        | atom head ports =>
            have pathEq := List.eq_of_mem_replicate headMember
            subst path
            simp [RegionPath.StartsWith] at starts
        | identity signature arity ports =>
            have pathEq := List.eq_of_mem_replicate headMember
            subst path
            simp [RegionPath.StartsWith] at starts
        | cut body =>
            simp only [Item.incidencePaths, List.mem_map] at headMember
            obtain ⟨inner, _, rfl⟩ := headMember
            rcases starts with ⟨rest, equality⟩
            injection equality with indexEq
            subst index
            simp only [ItemSeq.length]
            omega
      · have bound := tailInduction wireIndex (itemIndex + 1)
          tailMember starts
        simp only [ItemSeq.length]
        omega)
    items wireIndex itemIndex member starts

theorem supportParallelRootedTwoConjoinOfBoth
    (first second : Region wires) (wire : Var wires signature)
    (firstNonempty : first.incidencePaths wire.index.val ≠ [])
    (secondNonempty : second.incidencePaths wire.index.val ≠ []) :
    RegionPath.RootedTwo
      ((first.conjoin second).incidencePaths wire.index.val) := by
  rw [Region.incidencePaths_conjoin]
  let firstPaths := first.incidencePaths wire.index.val
  let secondPaths := second.incidencePaths wire.index.val
  let shiftedSecond := secondPaths.map
    (RegionPath.shiftHead first.items.length)
  change RegionPath.RootedTwo (firstPaths ++ shiftedSecond)
  have shiftedSecondNonempty : shiftedSecond ≠ [] := by
    simpa [shiftedSecond, List.map_eq_nil_iff] using secondNonempty
  have combinedNonempty : firstPaths ++ shiftedSecond ≠ [] :=
    List.append_ne_nil_of_left_ne_nil firstNonempty _
  have noCommon : ¬RegionPath.CommonHead
      (firstPaths ++ shiftedSecond) := by
    rintro ⟨index, allStart⟩
    obtain ⟨firstPath, firstMember⟩ :=
      List.exists_mem_of_ne_nil firstPaths firstNonempty
    obtain ⟨secondPath, secondMember⟩ :=
      List.exists_mem_of_ne_nil secondPaths secondNonempty
    have firstStarts := allStart firstPath
      (List.mem_append_left _ firstMember)
    have firstMember' : firstPath ∈
        first.items.incidencePaths wire.index.val 0 := by
      simpa only [firstPaths, Region.incidencePaths_eq_items] using firstMember
    have firstBound := supportParallelStartsWithOfMemIncidencePathsLt
      first.items wire.index.val 0 firstMember' firstStarts
    have shiftedMember :
        RegionPath.shiftHead first.items.length secondPath ∈
          shiftedSecond :=
      List.mem_map.mpr ⟨secondPath, secondMember, rfl⟩
    have secondStarts := allStart
      (RegionPath.shiftHead first.items.length secondPath)
      (List.mem_append_right _ shiftedMember)
    cases secondPath with
    | nil =>
        simp [RegionPath.shiftHead, RegionPath.StartsWith] at secondStarts
    | cons secondIndex secondTail =>
        rcases secondStarts with ⟨rest, equality⟩
        injection equality with indexEq
        omega
  exact ⟨by
    have firstPositive := List.length_pos_iff.mpr firstNonempty
    have secondPositive := List.length_pos_iff.mpr shiftedSecondNonempty
    have firstPositive' : 0 < firstPaths.length := by
      simpa only [firstPaths] using firstPositive
    simp only [List.length_append]
    change 2 ≤ firstPaths.length + shiftedSecond.length
    omega,
    ((RegionPath.rooted_iff_not_commonHead
      (firstPaths ++ shiftedSecond)).mpr
        ⟨combinedNonempty, noCommon⟩).2⟩

theorem SupportParallelIncidenceScope.conjoin
    {sourceSignature targetSignature : Sig}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (sourceWire : Var sourceWires sourceSignature)
    (targetWire : Var targetWires targetSignature)
    (first : SupportParallelIncidenceScope
      (sourceFirst.incidencePaths sourceWire.index.val)
      (targetFirst.incidencePaths targetWire.index.val))
    (second : SupportParallelIncidenceScope
      (sourceSecond.incidencePaths sourceWire.index.val)
      (targetSecond.incidencePaths targetWire.index.val)) :
    SupportParallelIncidenceScope
      ((sourceFirst.conjoin sourceSecond).incidencePaths sourceWire.index.val)
      ((targetFirst.conjoin targetSecond).incidencePaths targetWire.index.val) := by
  constructor
  · rw [Region.incidencePaths_conjoin, Region.incidencePaths_conjoin]
    constructor
    · intro sourceNonempty
      by_cases firstEmpty :
          sourceFirst.incidencePaths sourceWire.index.val = []
      · have secondNonempty :
            sourceSecond.incidencePaths sourceWire.index.val ≠ [] := by
          intro secondEmpty
          exact sourceNonempty (by simp [firstEmpty, secondEmpty])
        have targetSecondNonempty := second.nonempty.mp secondNonempty
        intro targetEmpty
        have mappedEmpty := (List.append_eq_nil_iff.mp targetEmpty).2
        exact targetSecondNonempty ((List.map_eq_nil_iff).mp mappedEmpty)
      · have targetFirstNonempty := first.nonempty.mp firstEmpty
        intro targetEmpty
        exact targetFirstNonempty (List.append_eq_nil_iff.mp targetEmpty).1
    · intro targetNonempty
      by_cases firstEmpty :
          targetFirst.incidencePaths targetWire.index.val = []
      · have secondNonempty :
            targetSecond.incidencePaths targetWire.index.val ≠ [] := by
          intro secondEmpty
          exact targetNonempty (by simp [firstEmpty, secondEmpty])
        have sourceSecondNonempty := second.nonempty.mpr secondNonempty
        intro sourceEmpty
        have mappedEmpty := (List.append_eq_nil_iff.mp sourceEmpty).2
        exact sourceSecondNonempty ((List.map_eq_nil_iff).mp mappedEmpty)
      · have sourceFirstNonempty := first.nonempty.mpr firstEmpty
        intro sourceEmpty
        exact sourceFirstNonempty (List.append_eq_nil_iff.mp sourceEmpty).1
  · intro sourceRooted
    by_cases firstRooted : RegionPath.RootedTwo
        (sourceFirst.incidencePaths sourceWire.index.val)
    · have targetFirstRooted := first.rooted firstRooted
      rw [Region.incidencePaths_conjoin]
      exact RegionPath.RootedTwo.of_sublist
        (List.sublist_append_left _ _) targetFirstRooted
    · by_cases secondRooted : RegionPath.RootedTwo
          (sourceSecond.incidencePaths sourceWire.index.val)
      · have targetSecondRooted := second.rooted secondRooted
        rw [Region.incidencePaths_conjoin]
        exact RegionPath.RootedTwo.of_sublist
          (List.sublist_append_right _ _)
          ((RegionPath.RootedTwo.map_shiftHead_iff
            targetFirst.items.length _).mpr targetSecondRooted)
      · have sourceFirstNonempty :
            sourceFirst.incidencePaths sourceWire.index.val ≠ [] := by
          intro firstEmpty
          rw [Region.incidencePaths_conjoin, firstEmpty,
            List.nil_append] at sourceRooted
          exact secondRooted
            ((RegionPath.RootedTwo.map_shiftHead_iff _ _).mp sourceRooted)
        have sourceSecondNonempty :
            sourceSecond.incidencePaths sourceWire.index.val ≠ [] := by
          intro secondEmpty
          rw [Region.incidencePaths_conjoin, secondEmpty,
            List.map_nil, List.append_nil] at sourceRooted
          exact firstRooted sourceRooted
        exact supportParallelRootedTwoConjoinOfBoth targetFirst targetSecond
          targetWire (first.nonempty.mp sourceFirstNonempty)
          (second.nonempty.mp sourceSecondNonempty)

theorem SupportParallelIncidenceScope.cut
    {sourceSignature targetSignature : Sig}
    {source : Region sourceWires} {target : Region targetWires}
    (sourceWire : Var sourceWires sourceSignature)
    (targetWire : Var targetWires targetSignature)
    (scope : SupportParallelIncidenceScope
      (source.incidencePaths sourceWire.index.val)
      (target.incidencePaths targetWire.index.val)) :
    SupportParallelIncidenceScope
      ((Region.singleton (.cut source)).incidencePaths sourceWire.index.val)
      ((Region.singleton (.cut target)).incidencePaths targetWire.index.val) := by
  constructor
  · rw [Region.incidencePaths_singleton_cut,
      Region.incidencePaths_singleton_cut]
    constructor
    · intro sourceNonempty targetEmpty
      have targetChildEmpty := (List.map_eq_nil_iff).mp targetEmpty
      have sourceChildEmpty : source.incidencePaths sourceWire.index.val = [] := by
        exact Classical.byContradiction fun sourceChildNonempty =>
          (scope.nonempty.mp sourceChildNonempty) targetChildEmpty
      exact sourceNonempty ((List.map_eq_nil_iff).mpr sourceChildEmpty)
    · intro targetNonempty sourceEmpty
      have sourceChildEmpty := (List.map_eq_nil_iff).mp sourceEmpty
      have targetChildEmpty : target.incidencePaths targetWire.index.val = [] := by
        exact Classical.byContradiction fun targetChildNonempty =>
          (scope.nonempty.mpr targetChildNonempty) sourceChildEmpty
      exact targetNonempty ((List.map_eq_nil_iff).mpr targetChildEmpty)
  · intro sourceRooted
    have sameEmpty : source.incidencePaths sourceWire.index.val = [] ↔
        target.incidencePaths targetWire.index.val = [] := by
      constructor
      · intro sourceEmpty
        exact Classical.byContradiction fun targetNonempty =>
          (scope.nonempty.mpr targetNonempty) sourceEmpty
      · intro targetEmpty
        exact Classical.byContradiction fun sourceNonempty =>
          (scope.nonempty.mp sourceNonempty) targetEmpty
    rw [Region.incidencePaths_singleton_cut] at sourceRooted ⊢
    have replaced := RegionPath.rootedTwo_replace []
      (source.incidencePaths sourceWire.index.val)
      (target.incidencePaths targetWire.index.val) [] 0 sameEmpty
    simpa only [List.nil_append, List.append_nil] using
      replaced.mp (by simpa using sourceRooted)

theorem supportParallelNonemptyOfLengthEq
    {first second : List α} (lengthEq : first.length = second.length) :
    first ≠ [] ↔ second ≠ [] := by
  rw [← List.length_pos_iff, ← List.length_pos_iff, lengthEq]

theorem SupportParallelIncidenceScope.iso
    {sourceSignature targetSignature : Sig}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (sourceWire : Var sourceWires sourceSignature)
    (targetWire : Var targetWires targetSignature)
    (scope : SupportParallelIncidenceScope
      (sourceAfter.incidencePaths sourceWire.index.val)
      (targetBefore.incidencePaths targetWire.index.val)) :
    SupportParallelIncidenceScope
      (sourceBefore.incidencePaths sourceWire.index.val)
      (targetAfter.incidencePaths targetWire.index.val) := by
  constructor
  · exact (supportParallelNonemptyOfLengthEq
      (sourceIso.incidencePaths_length_eq sourceWire)).trans
      (scope.nonempty.trans
        (supportParallelNonemptyOfLengthEq
          (targetIso.incidencePaths_length_eq targetWire)))
  · intro sourceRooted
    exact (targetIso.rootedTwo_incidencePaths_iff targetWire).mp
      (scope.rooted
        ((sourceIso.rootedTwo_incidencePaths_iff sourceWire).mp sourceRooted))

end VisualProof.Rule.Completeness.Comprehension.Structural
