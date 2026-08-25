import VisualProof.Rule.Completeness.Comprehension.Structural.Hosted
import VisualProof.Rule.Completeness.Comprehension.Sites
import VisualProof.Rule.Completeness.Comprehension.Leaf.Forms

namespace VisualProof.Rule.Completeness.Comprehension.Structural

open Diagram
open Theory
open WirePrimitive

structure SupportParallelFrames
    {common sourceWires splitWires : List Sig}
    (parallel : Transform.Frame [] common sourceWires splitWires)
    (heads : Content.Parallel.Heads splitWires []) where
  parallelInvariant : Transform.RetainedIndexInvariant parallel
  firstFresh : ∀ {signature} (wire : Var common signature),
    heads.1.index.val ≠ (parallel.targetKeep wire).index.val
  secondFresh : ∀ {signature} (wire : Var common signature),
    heads.2.index.val ≠ (parallel.targetKeep wire).index.val
  head : Transform.Frame [] sourceWires splitWires sourceWires
  tail : Transform.Frame [] common sourceWires common
  head_keep : ∀ {signature} (wire : Var common signature),
    head.sourceKeep (parallel.sourceKeep wire) = parallel.targetKeep wire
  tail_keep : ∀ {signature} (wire : Var common signature),
    tail.sourceKeep wire = parallel.sourceKeep wire
  first_selected : head.selected = heads.1
  second_selected : head.sourceKeep tail.selected = heads.2
  tail_selected : tail.selected = parallel.selected

def SupportParallelFrames.append
    {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    (locals : List Sig) :
    SupportParallelFrames (parallel.append locals)
      ((Content.Parallel.operation []).appendData parallel heads locals) := by
  refine {
    parallelInvariant := frames.parallelInvariant.append locals
    firstFresh := ?_
    secondFresh := ?_
    head := frames.head.append locals
    tail := frames.tail.append locals
    head_keep := ?_
    tail_keep := ?_
    first_selected := ?_
    second_selected := ?_
    tail_selected := ?_
  }
  · intro signature wire
    refine Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (((Content.Parallel.operation []).appendData parallel heads locals).1
            ).index.val ≠
          ((parallel.append locals).targetKeep wire).index.val) ?_ ?_ wire
    · intro inheritedSignature inherited
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using frames.firstFresh inherited
    · intro localSignature localWire
      simp [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight]
      omega
  · intro signature wire
    refine Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (((Content.Parallel.operation []).appendData parallel heads locals).2
            ).index.val ≠
          ((parallel.append locals).targetKeep wire).index.val) ?_ ?_ wire
    · intro inheritedSignature inherited
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using frames.secondFresh inherited
    · intro localSignature localWire
      simp [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight]
      omega
  · intro signature wire
    refine Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (frames.head.append locals).sourceKeep
            ((parallel.append locals).sourceKeep wire) =
          (parallel.append locals).targetKeep wire) ?_ ?_ wire
    · intro inheritedSignature inherited
      simpa [Transform.Frame.append, WireRenaming.appendRight] using
        congrArg (fun mapped => mapped.appendLeft locals)
          (frames.head_keep inherited)
    · intro localSignature localWire
      simp [Transform.Frame.append, WireRenaming.appendRight]
  · intro signature wire
    refine Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (frames.tail.append locals).sourceKeep wire =
          (parallel.append locals).sourceKeep wire) ?_ ?_ wire
    · intro inheritedSignature inherited
      simpa [Transform.Frame.append, WireRenaming.appendRight] using
        congrArg (fun mapped => mapped.appendLeft locals)
          (frames.tail_keep inherited)
    · intro localSignature localWire
      simp [Transform.Frame.append, WireRenaming.appendRight]
  · simpa [Transform.Frame.append, Content.Parallel.operation] using
      congrArg (fun wire => wire.appendLeft locals) frames.first_selected
  · simpa [Transform.Frame.append, Content.Parallel.operation,
      WireRenaming.appendRight] using
      congrArg (fun wire => wire.appendLeft locals) frames.second_selected
  · simpa [Transform.Frame.append] using
      congrArg (fun wire => wire.appendLeft locals) frames.tail_selected

def supportParallelFirstFrame
    (outer before after : List Sig) :
    Transform.Frame []
      (outer ++ (before ++ .rel [] :: after))
      (outer ++ (before ++ .rel [] :: .rel [] :: after))
      (outer ++ (before ++ .rel [] :: after)) :=
  Transform.Frame.replace outer before (.rel [] :: after) [] []

def supportParallelSecondFrame
    (outer before after : List Sig) :
    Transform.Frame []
      (outer ++ (before ++ after))
      (outer ++ (before ++ .rel [] :: after))
      (outer ++ (before ++ after)) :=
  Transform.Frame.replace outer before after [] []

def supportParallelFramesRoot
    (outer before after : List Sig) :
    SupportParallelFrames
      (Content.Parallel.rootFrame outer before after [])
      (Content.Parallel.firstHead outer before after [],
        Content.Parallel.secondHead outer before after []) := by
  refine {
    parallelInvariant :=
      Transform.RetainedIndexInvariant.replace outer before after
        [.rel [], .rel []] []
    firstFresh := ?_
    secondFresh := ?_
    head := supportParallelFirstFrame outer before after
    tail := supportParallelSecondFrame outer before after
    head_keep := ?_
    tail_keep := ?_
    first_selected := rfl
    second_selected := ?_
    tail_selected := rfl
  }
  · intro signature wire
    refine Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun wire =>
        (Content.Parallel.firstHead outer before after []).index.val ≠
          ((Content.Parallel.rootFrame outer before after []).targetKeep
            wire).index.val) ?_ ?_ wire
    · intro inheritedSignature inherited
      have inheritedBound := inherited.index.isLt
      simp [Content.Parallel.firstHead, Content.Parallel.rootFrame,
        Transform.Frame.insertedHead, Transform.Frame.replace,
        Transform.Frame.keep] at *
      omega
    · intro localSignature localWire
      refine Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          (Content.Parallel.firstHead outer before after []).index.val ≠
            ((Content.Parallel.rootFrame outer before after []).targetKeep
              (Var.appendRight outer localWire)).index.val) ?_ ?_ localWire
      · intro beforeSignature beforeWire
        have beforeBound := beforeWire.index.isLt
        simp [Content.Parallel.firstHead, Content.Parallel.rootFrame,
          Transform.Frame.insertedHead, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep] at *
        omega
      · intro afterSignature afterWire
        have firstIndex :
            (Content.Parallel.firstHead outer before after []).index.val =
              outer.length + before.length := by
          simp only [Content.Parallel.firstHead,
            Transform.Frame.insertedHead, Var.index_appendRight,
            Var.index, Fin.val_zero]
          omega
        have keepIndex :
            ((Content.Parallel.rootFrame outer before after []).targetKeep
              (Var.appendRight outer (Var.appendRight before afterWire))).index.val =
              outer.length + before.length + 2 + afterWire.index.val := by
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Var.appendRight, Var.index]
          omega
        rw [firstIndex, keepIndex]
        omega
  · intro signature wire
    refine Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun wire =>
        (Content.Parallel.secondHead outer before after []).index.val ≠
          ((Content.Parallel.rootFrame outer before after []).targetKeep
            wire).index.val) ?_ ?_ wire
    · intro inheritedSignature inherited
      simp [Content.Parallel.secondHead, Content.Parallel.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep]
      omega
    · intro localSignature localWire
      refine Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          (Content.Parallel.secondHead outer before after []).index.val ≠
            ((Content.Parallel.rootFrame outer before after []).targetKeep
              (Var.appendRight outer localWire)).index.val) ?_ ?_ localWire
      · intro beforeSignature beforeWire
        simp [Content.Parallel.secondHead, Content.Parallel.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep]
        omega
      · intro afterSignature afterWire
        have secondIndex :
            (Content.Parallel.secondHead outer before after []).index.val =
              outer.length + before.length + 1 := by
          simp [Content.Parallel.secondHead, Var.index]
          omega
        have keepIndex :
            ((Content.Parallel.rootFrame outer before after []).targetKeep
              (Var.appendRight outer (Var.appendRight before afterWire))).index.val =
              outer.length + before.length + 2 + afterWire.index.val := by
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Var.appendRight, Var.index]
          omega
        rw [secondIndex, keepIndex]
        omega
  · intro signature wire
    refine Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun wire =>
        (supportParallelFirstFrame outer before after).sourceKeep
            ((Content.Parallel.rootFrame outer before after []).sourceKeep
              wire) =
          (Content.Parallel.rootFrame outer before after []).targetKeep wire)
      ?_ ?_ wire
    · intro inheritedSignature inherited
      simp [supportParallelFirstFrame, Content.Parallel.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep,
        Transform.Frame.localKeep]
    · intro localSignature localWire
      refine Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          (supportParallelFirstFrame outer before after).sourceKeep
              ((Content.Parallel.rootFrame outer before after []).sourceKeep
                (Var.appendRight outer localWire)) =
            (Content.Parallel.rootFrame outer before after []).targetKeep
              (Var.appendRight outer localWire)) ?_ ?_ localWire
      · intro beforeSignature beforeWire
        simp [supportParallelFirstFrame, Content.Parallel.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep]
      · intro afterSignature afterWire
        simp only [supportParallelFirstFrame, Content.Parallel.rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep]
        apply Var.eq_of_index_eq
        apply Fin.ext
        simp [Var.appendRight, Var.index]
  · intro signature wire
    rfl
  · apply Var.eq_of_index_eq
    apply Fin.ext
    simp [supportParallelFirstFrame, supportParallelSecondFrame,
      Content.Parallel.secondHead, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep,
      Transform.Frame.insertedHead, Var.appendRight, Var.index]

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

structure SupportParallelSplitScope
    {common sourceWires splitWires : List Sig}
    (parallel : Transform.Frame [] common sourceWires splitWires)
    (heads : Content.Parallel.Heads splitWires [])
    (source : Region sourceWires) (split : Region splitWires) : Prop where
  canonical : source.Canonical → split.Canonical
  retained : ∀ {signature} (wire : Var common signature),
    SupportParallelIncidenceScope
      (source.incidencePaths (parallel.sourceKeep wire).index.val)
      (split.incidencePaths (parallel.targetKeep wire).index.val)
  first : SupportParallelIncidenceScope
    (source.incidencePaths parallel.selected.index.val)
    (split.incidencePaths heads.1.index.val)
  second : SupportParallelIncidenceScope
    (source.incidencePaths parallel.selected.index.val)
    (split.incidencePaths heads.2.index.val)

theorem SupportParallelSplitScope.iso
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    {sourceBefore sourceAfter : Region sourceWires}
    {splitBefore splitAfter : Region splitWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (splitIso : RegionIso (WireEquiv.refl splitWires)
      splitBefore splitAfter)
    (scope : SupportParallelSplitScope parallel heads sourceAfter splitBefore) :
    SupportParallelSplitScope parallel heads sourceBefore splitAfter := by
  constructor
  · intro sourceCanonical
    exact splitIso.canonical_iff.mp
      (scope.canonical (sourceIso.canonical_iff.mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.iso sourceIso splitIso
      (parallel.sourceKeep wire) (parallel.targetKeep wire)
      (scope.retained wire)
  · exact SupportParallelIncidenceScope.iso sourceIso splitIso
      parallel.selected heads.1 scope.first
  · exact SupportParallelIncidenceScope.iso sourceIso splitIso
      parallel.selected heads.2 scope.second

theorem SupportParallelSplitScope.conjoin
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    {sourceFirst sourceSecond : Region sourceWires}
    {splitFirst splitSecond : Region splitWires}
    (first : SupportParallelSplitScope parallel heads sourceFirst splitFirst)
    (second : SupportParallelSplitScope parallel heads sourceSecond splitSecond) :
    SupportParallelSplitScope parallel heads
      (sourceFirst.conjoin sourceSecond) (splitFirst.conjoin splitSecond) := by
  constructor
  · intro sourceCanonical
    have pieces := (Region.Canonical.conjoin_iff _ _).mp sourceCanonical
    exact (Region.Canonical.conjoin_iff _ _).mpr
      ⟨first.canonical pieces.1, second.canonical pieces.2⟩
  · intro signature wire
    exact SupportParallelIncidenceScope.conjoin
      (parallel.sourceKeep wire) (parallel.targetKeep wire)
      (first.retained wire) (second.retained wire)
  · exact SupportParallelIncidenceScope.conjoin parallel.selected heads.1
      first.first second.first
  · exact SupportParallelIncidenceScope.conjoin parallel.selected heads.2
      first.second second.second

theorem SupportParallelSplitScope.cut
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    {source : Region sourceWires} {split : Region splitWires}
    (scope : SupportParallelSplitScope parallel heads source split) :
    SupportParallelSplitScope parallel heads
      (Region.singleton (.cut source)) (Region.singleton (.cut split)) := by
  constructor
  · intro sourceCanonical
    exact (Region.singleton_cut_canonical_iff split).mpr
      (scope.canonical
        ((Region.singleton_cut_canonical_iff source).mp sourceCanonical))
  · intro signature wire
    exact SupportParallelIncidenceScope.cut
      (parallel.sourceKeep wire) (parallel.targetKeep wire)
      (scope.retained wire)
  · exact SupportParallelIncidenceScope.cut parallel.selected heads.1
      scope.first
  · exact SupportParallelIncidenceScope.cut parallel.selected heads.2
      scope.second

theorem SupportParallelSplitScope.blank
    (parallel : Transform.Frame [] common sourceWires splitWires)
    (heads : Content.Parallel.Heads splitWires []) :
    SupportParallelSplitScope parallel heads
      (Region.blank sourceWires) (Region.blank splitWires) := by
  constructor
  · intro _
    simp [Region.blank, Region.Canonical, ItemSeq.ChildrenCanonical]
  · intro signature wire
    constructor <;>
      simp [Region.blank, Region.incidencePaths, ItemSeq.incidencePaths]
  · constructor <;>
      simp [Region.blank, Region.incidencePaths, ItemSeq.incidencePaths]
  · constructor <;>
      simp [Region.blank, Region.incidencePaths, ItemSeq.incidencePaths]

theorem SupportParallelSplitScope.adjoin
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {split : Region (splitWires ++ locals)}
    (scope : SupportParallelSplitScope (parallel.append locals)
      ((Content.Parallel.operation []).appendData parallel heads locals)
      source split) :
    SupportParallelSplitScope parallel heads
      (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil split) := by
  constructor
  · intro sourceCanonical
    have sourceMaterialCanonical : source.Canonical :=
      Region.Canonical.material_of_adjoinAt locals .nil source
        sourceCanonical
    have splitMaterialCanonical := scope.canonical sourceMaterialCanonical
    apply Region.Canonical.adjoinAt_of_material_roots locals .nil split
      True.intro splitMaterialCanonical
    intro localIndex
    let localWire : Var (common ++ locals) (locals.get localIndex) :=
      Var.appendRight common (Var.ofIndex localIndex)
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
        sourceCanonical localIndex
    have sourceRoot' : RegionPath.RootedTwo
        (source.incidencePaths
          ((parallel.append locals).sourceKeep localWire).index.val) := by
      simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
        using sourceRoot
    have splitRoot := (scope.retained localWire).rooted sourceRoot'
    simpa [localWire, Transform.Frame.append, WireRenaming.appendRight]
      using splitRoot
  · intro signature wire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      ((parallel.sourceKeep wire).appendLeft locals)
    have splitPaths := Region.incidencePaths_adjoinAt_nil split
      ((parallel.targetKeep wire).appendLeft locals)
    rw [show (parallel.sourceKeep wire).index.val =
        ((parallel.sourceKeep wire).appendLeft locals).index.val by simp,
      sourcePaths,
      show (parallel.targetKeep wire).index.val =
        ((parallel.targetKeep wire).appendLeft locals).index.val by simp,
      splitPaths]
    simpa [Transform.Frame.append, WireRenaming.appendRight] using
      scope.retained (wire.appendLeft locals)
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (parallel.selected.appendLeft locals)
    have splitPaths := Region.incidencePaths_adjoinAt_nil split
      (heads.1.appendLeft locals)
    rw [show parallel.selected.index.val =
        (parallel.selected.appendLeft locals).index.val by simp,
      sourcePaths,
      show heads.1.index.val = (heads.1.appendLeft locals).index.val by simp,
      splitPaths]
    simpa [Transform.Frame.append, Content.Parallel.operation] using scope.first
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (parallel.selected.appendLeft locals)
    have splitPaths := Region.incidencePaths_adjoinAt_nil split
      (heads.2.appendLeft locals)
    rw [show parallel.selected.index.val =
        (parallel.selected.appendLeft locals).index.val by simp,
      sourcePaths,
      show heads.2.index.val = (heads.2.appendLeft locals).index.val by simp,
      splitPaths]
    simpa [Transform.Frame.append, Content.Parallel.operation] using scope.second

theorem SupportParallelSplitScope.atom
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    (head : Var common (.rel arguments)) (ports : Vars common arguments) :
    SupportParallelSplitScope parallel heads
      (Region.singleton (.atom (parallel.sourceKeep head)
        (ports.map fun wire => parallel.sourceKeep wire)))
      (Region.singleton (.atom (parallel.targetKeep head)
        (ports.map fun wire => parallel.targetKeep wire))) := by
  constructor
  · intro _
    change (Region.ofItems (.cons
      (.atom (parallel.targetKeep head)
        (ports.map fun wire => parallel.targetKeep wire)) .nil)).Canonical
    constructor
    · intro localIndex
      exact Fin.elim0 localIndex
    · apply (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
      simp [ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
  · intro signature wire
    have headEq :
        (if (parallel.sourceKeep head).index.val =
            (parallel.sourceKeep wire).index.val then 1 else 0) =
          (if (parallel.targetKeep head).index.val =
            (parallel.targetKeep wire).index.val then 1 else 0) := by
      by_cases sourceEq : (parallel.sourceKeep head).index.val =
          (parallel.sourceKeep wire).index.val
      · have targetEq := (frames.parallelInvariant.reflects head wire).mp
          sourceEq
        simp [sourceEq, targetEq]
      · have targetNe :=
          not_congr (frames.parallelInvariant.reflects head wire) |>.mp sourceEq
        simp [sourceEq, targetNe]
    have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
      parallel.sourceKeep parallel.targetKeep
      frames.parallelInvariant.reflects wire
    have pathsEq :
        (Region.singleton (.atom (parallel.sourceKeep head)
          (ports.map fun wire => parallel.sourceKeep wire))).incidencePaths
            (parallel.sourceKeep wire).index.val =
        (Region.singleton (.atom (parallel.targetKeep head)
          (ports.map fun wire => parallel.targetKeep wire))).incidencePaths
            (parallel.targetKeep wire).index.val := by
      simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
        ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
        Item.incidencePaths, List.append_nil, Var.index_appendLeft,
        Vars.countIndex_map_appendLeft_nil]
      rw [headEq, portsEq]
    rw [pathsEq]
    exact SupportParallelIncidenceScope.refl _
  · have sourcePortsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports parallel.sourceKeep
          parallel.selected.index.val
          (fun wire => Ne.symm (frames.parallelInvariant.selectedFresh wire))
    have splitPortsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports parallel.targetKeep
          heads.1.index.val (fun wire => Ne.symm (frames.firstFresh wire))
    have sourceEmpty :
        (Region.singleton (.atom (parallel.sourceKeep head)
          (ports.map fun wire => parallel.sourceKeep wire))).incidencePaths
            parallel.selected.index.val = [] := by
      change (Region.ofItems (.cons
        (.atom (parallel.sourceKeep head)
          (ports.map fun wire => parallel.sourceKeep wire)) .nil)).incidencePaths
            parallel.selected.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths,
        Ne.symm (frames.parallelInvariant.selectedFresh head), sourcePortsZero]
    have splitEmpty :
        (Region.singleton (.atom (parallel.targetKeep head)
          (ports.map fun wire => parallel.targetKeep wire))).incidencePaths
            heads.1.index.val = [] := by
      change (Region.ofItems (.cons
        (.atom (parallel.targetKeep head)
          (ports.map fun wire => parallel.targetKeep wire)) .nil)).incidencePaths
            heads.1.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths,
        Ne.symm (frames.firstFresh head), splitPortsZero]
    rw [sourceEmpty, splitEmpty]
    exact SupportParallelIncidenceScope.refl _
  · have sourcePortsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports parallel.sourceKeep
          parallel.selected.index.val
          (fun wire => Ne.symm (frames.parallelInvariant.selectedFresh wire))
    have splitPortsZero :=
        Vars.countIndex_map_eq_zero_of_no_preimage ports parallel.targetKeep
          heads.2.index.val (fun wire => Ne.symm (frames.secondFresh wire))
    have sourceEmpty :
        (Region.singleton (.atom (parallel.sourceKeep head)
          (ports.map fun wire => parallel.sourceKeep wire))).incidencePaths
            parallel.selected.index.val = [] := by
      change (Region.ofItems (.cons
        (.atom (parallel.sourceKeep head)
          (ports.map fun wire => parallel.sourceKeep wire)) .nil)).incidencePaths
            parallel.selected.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths,
        Ne.symm (frames.parallelInvariant.selectedFresh head), sourcePortsZero]
    have splitEmpty :
        (Region.singleton (.atom (parallel.targetKeep head)
          (ports.map fun wire => parallel.targetKeep wire))).incidencePaths
            heads.2.index.val = [] := by
      change (Region.ofItems (.cons
        (.atom (parallel.targetKeep head)
          (ports.map fun wire => parallel.targetKeep wire)) .nil)).incidencePaths
            heads.2.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths,
        Ne.symm (frames.secondFresh head), splitPortsZero]
    rw [sourceEmpty, splitEmpty]
    exact SupportParallelIncidenceScope.refl _

theorem SupportParallelSplitScope.identity
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var common signature) :
    SupportParallelSplitScope parallel heads
      (Region.singleton (.identity signature arity
        (fun position => parallel.sourceKeep (ports position))))
      (Region.singleton (.identity signature arity
        (fun position => parallel.targetKeep (ports position)))) := by
  constructor
  · intro _
    change (Region.ofItems (.cons
      (.identity signature arity
        (fun position => parallel.targetKeep (ports position))) .nil)).Canonical
    constructor
    · intro localIndex
      exact Fin.elim0 localIndex
    · apply (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
      simp [ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
  · intro wireSignature wire
    have portsEq := Transform.countPorts_map_eq_of_reflection arity ports
      parallel.sourceKeep parallel.targetKeep
      frames.parallelInvariant.reflects wire
    have pathsEq :
        (Region.singleton (.identity signature arity
          (fun position => parallel.sourceKeep (ports position)))).incidencePaths
            (parallel.sourceKeep wire).index.val =
        (Region.singleton (.identity signature arity
          (fun position => parallel.targetKeep (ports position)))).incidencePaths
            (parallel.targetKeep wire).index.val := by
      simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
        ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
        Item.incidencePaths, List.append_nil, Var.index_appendLeft]
      rw [portsEq]
    rw [pathsEq]
    exact SupportParallelIncidenceScope.refl _
  · have sourcePortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
        parallel.sourceKeep parallel.selected.index.val
        (fun wire => Ne.symm (frames.parallelInvariant.selectedFresh wire))
    have splitPortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
        parallel.targetKeep heads.1.index.val
        (fun wire => Ne.symm (frames.firstFresh wire))
    have sourceEmpty :
        (Region.singleton (.identity signature arity
          (fun position => parallel.sourceKeep (ports position)))).incidencePaths
            parallel.selected.index.val = [] := by
      change (Region.ofItems (.cons
        (.identity signature arity
          (fun position => parallel.sourceKeep (ports position))) .nil)).incidencePaths
            parallel.selected.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths, sourcePortsZero]
    have splitEmpty :
        (Region.singleton (.identity signature arity
          (fun position => parallel.targetKeep (ports position)))).incidencePaths
            heads.1.index.val = [] := by
      change (Region.ofItems (.cons
        (.identity signature arity
          (fun position => parallel.targetKeep (ports position))) .nil)).incidencePaths
            heads.1.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths, splitPortsZero]
    rw [sourceEmpty, splitEmpty]
    exact SupportParallelIncidenceScope.refl _
  · have sourcePortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
        parallel.sourceKeep parallel.selected.index.val
        (fun wire => Ne.symm (frames.parallelInvariant.selectedFresh wire))
    have splitPortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
        parallel.targetKeep heads.2.index.val
        (fun wire => Ne.symm (frames.secondFresh wire))
    have sourceEmpty :
        (Region.singleton (.identity signature arity
          (fun position => parallel.sourceKeep (ports position)))).incidencePaths
            parallel.selected.index.val = [] := by
      change (Region.ofItems (.cons
        (.identity signature arity
          (fun position => parallel.sourceKeep (ports position))) .nil)).incidencePaths
            parallel.selected.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths, sourcePortsZero]
    have splitEmpty :
        (Region.singleton (.identity signature arity
          (fun position => parallel.targetKeep (ports position)))).incidencePaths
            heads.2.index.val = [] := by
      change (Region.ofItems (.cons
        (.identity signature arity
          (fun position => parallel.targetKeep (ports position))) .nil)).incidencePaths
            heads.2.index.val = []
      rw [Region.incidencePaths_ofItems]
      simp [ItemSeq.incidencePaths, Item.incidencePaths, splitPortsZero]
    rw [sourceEmpty, splitEmpty]
    exact SupportParallelIncidenceScope.refl _

theorem SupportParallelSplitScope.selected
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads) :
    SupportParallelSplitScope parallel heads
      (Region.singleton (.atom parallel.selected .nil))
      (Region.ofItems
        (.cons (.atom heads.1 .nil)
          (.cons (.atom heads.2 .nil) .nil))) := by
  constructor
  · intro _
    constructor
    · intro localIndex
      exact Fin.elim0 localIndex
    · exact ⟨True.intro, ⟨True.intro, True.intro⟩⟩
  · intro signature wire
    have sourceFresh := frames.parallelInvariant.selectedFresh wire
    have firstFresh := frames.firstFresh wire
    have secondFresh := frames.secondFresh wire
    simp only [Region.singleton, Region.incidencePaths_ofItems,
      ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex,
      List.append_nil]
    simp [sourceFresh, firstFresh, secondFresh]
    exact SupportParallelIncidenceScope.refl _
  · constructor
    · simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex]
    · intro rooted
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths,
        Vars.countIndex, RegionPath.RootedTwo] at rooted
  · constructor
    · simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths, Vars.countIndex]
    · intro rooted
      simp [Region.singleton, Region.incidencePaths_ofItems,
        ItemSeq.incidencePaths, Item.incidencePaths,
        Vars.countIndex, RegionPath.RootedTwo] at rooted

end VisualProof.Rule.Completeness.Comprehension.Structural
