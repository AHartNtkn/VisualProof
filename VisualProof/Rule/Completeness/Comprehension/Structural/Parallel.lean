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

structure SupportParallelRegionFactors
    (headPattern tailPattern fullPattern : OpenDiagram [])
    {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    {source : Region sourceWires} {originalResult : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.RegionResult
        fullPattern parallel.sourceKeep parallel.selected source originalResult)
    (sites : RegionSites (Content.Parallel.operation []) heads evidence) where
  splitSource : Region splitWires
  headResult : Region sourceWires
  headEvidence :
    VisualProof.Rule.Comprehension.Instantiation.RegionResult
      headPattern frames.head.sourceKeep frames.head.selected splitSource headResult
  headSites : RegionSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit headEvidence
  tailSource : Region sourceWires
  tailResult : Region common
  tailEvidence :
    VisualProof.Rule.Comprehension.Instantiation.RegionResult
      tailPattern frames.tail.sourceKeep frames.tail.selected tailSource tailResult
  tailSites : RegionSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit tailEvidence
  splitIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
    (regionEdit (operation := Content.Parallel.operation []) heads evidence
      sites).endpoint splitSource)
  splitScope : SupportParallelSplitScope parallel heads source splitSource
  tailSourceScope : ScopePreservation source tailSource
  headBridge : HostedStrict headResult tailSource
  headScope : ScopePreservation headResult tailSource
  headReverseScope : ScopePreservation tailSource headResult
  resultBridge : HostedStrict originalResult tailResult
  resultScope : ScopePreservation originalResult tailResult

structure SupportParallelItemsFactors
    (headPattern tailPattern fullPattern : OpenDiagram [])
    {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    {source : ItemSeq sourceWires} {originalResult : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        fullPattern parallel.sourceKeep parallel.selected source originalResult)
    (sites : ItemsSites (Content.Parallel.operation []) heads evidence) where
  splitSource : ItemSeq splitWires
  headResult : Region sourceWires
  headEvidence :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      headPattern frames.head.sourceKeep frames.head.selected splitSource headResult
  headSites : ItemsSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit headEvidence
  tailSource : ItemSeq sourceWires
  tailResult : Region common
  tailEvidence :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      tailPattern frames.tail.sourceKeep frames.tail.selected tailSource tailResult
  tailSites : ItemsSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit tailEvidence
  splitIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
    (itemsEdit (operation := Content.Parallel.operation []) heads evidence
      sites).endpoint (Region.ofItems splitSource))
  splitScope : SupportParallelSplitScope parallel heads
    (Region.ofItems source) (Region.ofItems splitSource)
  tailSourceScope : ScopePreservation (Region.ofItems source)
    (Region.ofItems tailSource)
  headBridge : HostedStrict headResult (Region.ofItems tailSource)
  headScope : ScopePreservation headResult (Region.ofItems tailSource)
  headReverseScope : ScopePreservation (Region.ofItems tailSource) headResult
  resultBridge : HostedStrict originalResult tailResult
  resultScope : ScopePreservation originalResult tailResult

structure SupportParallelItemFactors
    (headPattern tailPattern fullPattern : OpenDiagram [])
    {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    (frames : SupportParallelFrames parallel heads)
    {source : Item sourceWires} {originalResult : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemResult
        fullPattern parallel.sourceKeep parallel.selected source originalResult)
    (sites : ItemSites (Content.Parallel.operation []) heads evidence) where
  splitSource : ItemSeq splitWires
  headResult : Region sourceWires
  headEvidence :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      headPattern frames.head.sourceKeep frames.head.selected splitSource headResult
  headSites : ItemsSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit headEvidence
  tailSource : ItemSeq sourceWires
  tailResult : Region common
  tailEvidence :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      tailPattern frames.tail.sourceKeep frames.tail.selected tailSource tailResult
  tailSites : ItemsSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit tailEvidence
  splitIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
    (itemEdit (operation := Content.Parallel.operation []) heads evidence
      sites).endpoint (Region.ofItems splitSource))
  splitScope : SupportParallelSplitScope parallel heads
    (Region.singleton source) (Region.ofItems splitSource)
  tailSourceScope : ScopePreservation (Region.singleton source)
    (Region.ofItems tailSource)
  headBridge : HostedStrict headResult (Region.ofItems tailSource)
  headScope : ScopePreservation headResult (Region.ofItems tailSource)
  headReverseScope : ScopePreservation (Region.ofItems tailSource) headResult
  resultBridge : HostedStrict originalResult tailResult
  resultScope : ScopePreservation originalResult tailResult

abbrev SupportParallelSelectedCase
    (headPattern tailPattern fullPattern : OpenDiagram []) : Prop :=
  ∀ {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    {sitePattern : OpenDiagram []}
    (frames : SupportParallelFrames parallel heads)
    (application : Vars common [])
    (siteData :
      (Content.Parallel.operation []).SiteData parallel heads application),
    Nonempty (SupportParallelItemFactors headPattern tailPattern fullPattern
      frames
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) application)
      (@ItemSites.selectedAtom [] (Content.Parallel.operation []) fullPattern
        common sourceWires splitWires sitePattern parallel heads application
        siteData))

structure RecordingItemsAppend
    (pattern : OpenDiagram [])
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {firstSource secondSource : ItemSeq sourceWires}
    {firstResult secondResult : Region common}
    {firstEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected firstSource firstResult}
    (firstSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
      firstEvidence)
    {secondEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected secondSource secondResult}
    (secondSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
      secondEvidence) where
  result : Region common
  evidence :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      pattern frame.sourceKeep frame.selected
      (firstSource.append secondSource) result
  sites : ItemsSites
    (recordingOperation (normalizationOperation []) []) PUnit.unit evidence
  resultIso : RegionIso (WireEquiv.refl common)
    (firstResult.conjoin secondResult) result

noncomputable def recordingItemsAppend
    (pattern : OpenDiagram [])
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {firstSource secondSource : ItemSeq sourceWires}
    {firstResult secondResult : Region common}
    {firstEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected firstSource firstResult}
    (firstSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
      firstEvidence)
    {secondEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected secondSource secondResult}
    (secondSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
      secondEvidence) :
    RecordingItemsAppend pattern firstSites secondSites :=
  match firstSites with
  | .nil _ => {
      result := secondResult
      evidence := secondEvidence
      sites := secondSites
      resultIso := RegionIso.blankConjoin secondResult
    }
  | @ItemsSites.cons _ _ _ _ _ _ _ _ _ _ itemResult tailResult
      itemEvidence tailEvidence itemSites tailSites =>
      let tailAppend := recordingItemsAppend pattern
        (firstEvidence := tailEvidence) tailSites
        (secondEvidence := secondEvidence) secondSites
      {
        result := itemResult.conjoin tailAppend.result
        evidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemEvidence tailAppend.evidence
        sites := .cons itemSites tailAppend.sites
        resultIso := (RegionIso.conjoinAssoc itemResult tailResult
          secondResult).trans
          (RegionIso.conjoinCongr (RegionIso.refl itemResult)
            tailAppend.resultIso)
      }
  termination_by sizeOf firstSource

mutual
  theorem supportParallelRegionFactors_nonempty
      (headPattern tailPattern fullPattern : OpenDiagram [])
      (selectedCase :
        SupportParallelSelectedCase headPattern tailPattern fullPattern)
      {common sourceWires splitWires : List Sig}
      {parallel : Transform.Frame [] common sourceWires splitWires}
      {heads : Content.Parallel.Heads splitWires []}
      (frames : SupportParallelFrames parallel heads)
      {source : Region sourceWires} {originalResult : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          fullPattern parallel.sourceKeep parallel.selected source originalResult)
      (sites : RegionSites (Content.Parallel.operation []) heads evidence) :
      Nonempty (SupportParallelRegionFactors headPattern tailPattern fullPattern
        frames evidence sites) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        obtain ⟨child⟩ := supportParallelItemsFactors_nonempty headPattern
          tailPattern fullPattern selectedCase (frames.append locals)
          childEvidence childSites
        let headEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            child.headEvidence
        let tailEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            child.tailEvidence
        let headSites : RegionSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headEvidence := .mk child.headSites
        let tailSites : RegionSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailEvidence := .mk child.tailSites
        let splitSource := Region.mk locals child.splitSource
        let tailSource := Region.mk locals child.tailSource
        obtain ⟨childSplitIso⟩ := child.splitIso
        let splitIso := (RegionIso.adjoinAt locals .nil childSplitIso).trans
          (RegionIso.adjoinAtOfItems locals child.splitSource)
        let headResult := Region.adjoinAt locals .nil child.headResult
        let tailResult := Region.adjoinAt locals .nil child.tailResult
        have liftedHeadBridge : HostedStrict headResult
            (Region.adjoinAt locals .nil (Region.ofItems child.tailSource)) :=
          HostedStrict.adjoinAt locals child.headResult
            (Region.ofItems child.tailSource) child.headBridge
        have headBridge : HostedStrict headResult tailSource :=
          HostedStrict.iso (RegionIso.refl headResult)
            (RegionIso.adjoinAtOfItems locals child.tailSource)
            liftedHeadBridge
        have liftedHeadScope : ScopePreservation headResult
            (Region.adjoinAt locals .nil (Region.ofItems child.tailSource)) :=
          adjoinAt_preserves_scope locals .nil child.headResult
            (Region.ofItems child.tailSource) child.headScope
        have headScope : ScopePreservation headResult tailSource :=
          liftedHeadScope.trans
            (ScopePreservation.ofIso
              (RegionIso.adjoinAtOfItems locals child.tailSource))
        have liftedHeadReverseScope : ScopePreservation
            (Region.adjoinAt locals .nil (Region.ofItems child.tailSource))
            headResult :=
          adjoinAt_preserves_scope locals .nil
            (Region.ofItems child.tailSource) child.headResult
            child.headReverseScope
        have headReverseScope : ScopePreservation tailSource headResult :=
          (ScopePreservation.ofIso
            (RegionIso.adjoinAtOfItems locals child.tailSource).symm).trans
              liftedHeadReverseScope
        have liftedTailSourceScope : ScopePreservation
            (Region.adjoinAt locals .nil (Region.ofItems items))
            (Region.adjoinAt locals .nil (Region.ofItems child.tailSource)) :=
          adjoinAt_preserves_scope locals .nil (Region.ofItems items)
            (Region.ofItems child.tailSource) child.tailSourceScope
        have tailSourceScope : ScopePreservation
            (Region.mk locals items) tailSource :=
          (ScopePreservation.ofIso
            (RegionIso.adjoinAtOfItems locals items).symm).trans
              (liftedTailSourceScope.trans
                (ScopePreservation.ofIso
                  (RegionIso.adjoinAtOfItems locals child.tailSource)))
        have resultBridge : HostedStrict
            (Region.adjoinAt locals .nil childResult) tailResult :=
          HostedStrict.adjoinAt locals childResult child.tailResult
            child.resultBridge
        have resultScope : ScopePreservation
            (Region.adjoinAt locals .nil childResult) tailResult :=
          adjoinAt_preserves_scope locals .nil childResult
            child.tailResult child.resultScope
        exact ⟨{
          splitSource := splitSource
          headResult := headResult
          headEvidence := headEvidence
          headSites := headSites
          tailSource := tailSource
          tailResult := tailResult
          tailEvidence := tailEvidence
          tailSites := tailSites
          splitIso := ⟨splitIso⟩
          splitScope := SupportParallelSplitScope.iso
            (RegionIso.adjoinAtOfItems locals items).symm
            (RegionIso.adjoinAtOfItems locals child.splitSource)
            (SupportParallelSplitScope.adjoin locals child.splitScope)
          tailSourceScope := tailSourceScope
          headBridge := headBridge
          headScope := headScope
          headReverseScope := headReverseScope
          resultBridge := resultBridge
          resultScope := resultScope
        }⟩
    termination_by sizeOf source

  theorem supportParallelItemsFactors_nonempty
      (headPattern tailPattern fullPattern : OpenDiagram [])
      (selectedCase :
        SupportParallelSelectedCase headPattern tailPattern fullPattern)
      {common sourceWires splitWires : List Sig}
      {parallel : Transform.Frame [] common sourceWires splitWires}
      {heads : Content.Parallel.Heads splitWires []}
      (frames : SupportParallelFrames parallel heads)
      {source : ItemSeq sourceWires} {originalResult : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          fullPattern parallel.sourceKeep parallel.selected source originalResult)
      (sites : ItemsSites (Content.Parallel.operation []) heads evidence) :
      Nonempty (SupportParallelItemsFactors headPattern tailPattern fullPattern
        frames evidence sites) :=
    match sites with
    | .nil nilEvidence => by
        let headEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected)
        let tailEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected)
        let headSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headEvidence := .nil headEvidence
        let tailSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailEvidence := .nil tailEvidence
        exact ⟨{
          splitSource := .nil
          headResult := Region.blank sourceWires
          headEvidence := headEvidence
          headSites := headSites
          tailSource := .nil
          tailResult := Region.blank common
          tailEvidence := tailEvidence
          tailSites := tailSites
          splitIso := ⟨RegionIso.refl _⟩
          splitScope := SupportParallelSplitScope.blank parallel heads
          tailSourceScope := ScopePreservation.refl _
          headBridge := HostedStrict.refl _
          headScope := ScopePreservation.refl _
          headReverseScope := ScopePreservation.refl _
          resultBridge := HostedStrict.refl _
          resultScope := ScopePreservation.refl _
        }⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ sourceItem sourceTail _ _ _ _
        itemSites tailSites => by
        obtain ⟨item⟩ := supportParallelItemFactors_nonempty headPattern
          tailPattern fullPattern selectedCase frames _ itemSites
        obtain ⟨tail⟩ := supportParallelItemsFactors_nonempty headPattern
          tailPattern fullPattern selectedCase frames _ tailSites
        let headAppend := recordingItemsAppend headPattern
          (frame := frames.head) item.headSites tail.headSites
        let tailAppend := recordingItemsAppend tailPattern
          (frame := frames.tail) item.tailSites tail.tailSites
        let splitSource := item.splitSource.append tail.splitSource
        let tailSource := item.tailSource.append tail.tailSource
        obtain ⟨itemSplitIso⟩ := item.splitIso
        obtain ⟨tailSplitIso⟩ := tail.splitIso
        have splitIso : RegionIso (WireEquiv.refl splitWires)
            (itemsEdit (operation := Content.Parallel.operation []) heads
              evidence (.cons itemSites tailSites)).endpoint
            (Region.ofItems splitSource) := by
          let pieces := RegionIso.conjoinCongr itemSplitIso tailSplitIso
          let joined := RegionIso.ofEq
            (Region.ofItems_conjoin item.splitSource tail.splitSource)
          simpa only [itemsEdit, splitSource] using pieces.trans joined
        let headPiecesBridge := HostedStrict.conjoin item.headResult
          tail.headResult (Region.ofItems item.tailSource)
          (Region.ofItems tail.tailSource) item.headBridge tail.headBridge
        let headPiecesScope := ScopePreservation.conjoin item.headScope
          tail.headScope
        let tailPiecesBridge := HostedStrict.conjoin _ _ _ _
          item.resultBridge tail.resultBridge
        let tailPiecesScope := ScopePreservation.conjoin item.resultScope
          tail.resultScope
        let tailSourceIso := RegionIso.ofEq
          (Region.ofItems_conjoin item.tailSource tail.tailSource)
        have sourceScope : ScopePreservation
            (Region.ofItems (.cons sourceItem sourceTail))
            (Region.ofItems tailSource) := by
          let piecesScope := ScopePreservation.conjoin
            item.tailSourceScope tail.tailSourceScope
          let sourceIso : RegionIso (WireEquiv.refl sourceWires)
              _ (Region.ofItems (.cons sourceItem sourceTail)) :=
            RegionIso.ofEq
              (Region.singleton_conjoin_ofItems sourceItem sourceTail)
          exact (ScopePreservation.ofIso sourceIso.symm).trans
            (piecesScope.trans (ScopePreservation.ofIso tailSourceIso))
        let splitPiecesScope := SupportParallelSplitScope.conjoin
          item.splitScope tail.splitScope
        let sourceSplitIso : RegionIso (WireEquiv.refl sourceWires)
            _ (Region.ofItems (.cons sourceItem sourceTail)) :=
          RegionIso.ofEq
            (Region.singleton_conjoin_ofItems sourceItem sourceTail)
        let targetSplitIso : RegionIso (WireEquiv.refl splitWires)
            _ (Region.ofItems splitSource) :=
          RegionIso.ofEq
            (Region.ofItems_conjoin item.splitSource tail.splitSource)
        exact ⟨{
          splitSource := splitSource
          headResult := headAppend.result
          headEvidence := headAppend.evidence
          headSites := headAppend.sites
          tailSource := tailSource
          tailResult := tailAppend.result
          tailEvidence := tailAppend.evidence
          tailSites := tailAppend.sites
          splitIso := ⟨splitIso⟩
          splitScope := SupportParallelSplitScope.iso sourceSplitIso.symm
            targetSplitIso splitPiecesScope
          tailSourceScope := sourceScope
          headBridge := HostedStrict.iso headAppend.resultIso.symm
            tailSourceIso headPiecesBridge
          headScope :=
            (ScopePreservation.ofIso headAppend.resultIso.symm).trans
              (headPiecesScope.trans
                (ScopePreservation.ofIso tailSourceIso))
          headReverseScope :=
            (ScopePreservation.ofIso tailSourceIso.symm).trans
              ((ScopePreservation.conjoin item.headReverseScope
                tail.headReverseScope).trans
                (ScopePreservation.ofIso headAppend.resultIso))
          resultBridge := HostedStrict.iso (RegionIso.refl _)
            tailAppend.resultIso tailPiecesBridge
          resultScope := tailPiecesScope.trans
            (ScopePreservation.ofIso tailAppend.resultIso)
        }⟩
    termination_by sizeOf source

  theorem supportParallelItemFactors_nonempty
      (headPattern tailPattern fullPattern : OpenDiagram [])
      (selectedCase :
        SupportParallelSelectedCase headPattern tailPattern fullPattern)
      {common sourceWires splitWires : List Sig}
      {parallel : Transform.Frame [] common sourceWires splitWires}
      {heads : Content.Parallel.Heads splitWires []}
      (frames : SupportParallelFrames parallel heads)
      {source : Item sourceWires} {originalResult : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          fullPattern parallel.sourceKeep parallel.selected source originalResult)
      (sites : ItemSites (Content.Parallel.operation []) heads evidence) :
      Nonempty (SupportParallelItemFactors headPattern tailPattern fullPattern
        frames evidence sites) :=
    match sites with
    | .atom head ports => by
        let headCommon := parallel.sourceKeep head
        let headPorts := ports.map fun wire => parallel.sourceKeep wire
        let splitHead := parallel.targetKeep head
        let splitPorts := ports.map fun wire => parallel.targetKeep wire
        let splitItem := Item.atom splitHead splitPorts
        let tailItem := Item.atom headCommon headPorts
        have headMap : frames.head.sourceKeep headCommon = splitHead :=
          frames.head_keep head
        have portsMap : headPorts.map (fun wire => frames.head.sourceKeep wire) =
            splitPorts := by
          simp only [headPorts, splitPorts, Vars.map_map]
          apply Vars.map_congr ports
          intro signature wire
          exact frames.head_keep wire
        have tailHeadMap : frames.tail.sourceKeep head = headCommon :=
          frames.tail_keep head
        have tailPortsMap : ports.map (fun wire => frames.tail.sourceKeep wire) =
            headPorts := by
          simp only [headPorts]
          apply Vars.map_congr ports
          intro signature wire
          exact frames.tail_keep wire
        let rawHeadItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected) headCommon headPorts
        have headItemEvidence :
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
              headPattern frames.head.sourceKeep frames.head.selected splitItem
              (Region.singleton (.atom headCommon headPorts)) := by
          simpa [splitItem, headMap, portsMap] using rawHeadItemEvidence
        let rawTailItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected) head ports
        have tailItemEvidence :
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
              tailPattern frames.tail.sourceKeep frames.tail.selected tailItem
              (Region.singleton (.atom head ports)) := by
          simpa [tailItem, tailHeadMap, tailPortsMap] using rawTailItemEvidence
        have headItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headItemEvidence := by
          simpa [splitItem, headMap, portsMap] using
            (ItemSites.atom
              (operation := recordingOperation (normalizationOperation []) [])
              (pattern := headPattern) (frame := frames.head)
              (data := PUnit.unit) headCommon headPorts)
        have tailItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailItemEvidence := by
          simpa [tailItem, tailHeadMap, tailPortsMap] using
            (ItemSites.atom
              (operation := recordingOperation (normalizationOperation []) [])
              (pattern := tailPattern) (frame := frames.tail)
              (data := PUnit.unit) head ports)
        let headNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected)
        let tailNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected)
        let headEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            headItemEvidence headNil
        let tailEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            tailItemEvidence tailNil
        let headSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headEvidence := .cons headItemSites (.nil headNil)
        let tailSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailEvidence := .cons tailItemSites (.nil tailNil)
        let headRegion := Region.singleton (.atom headCommon headPorts)
        let tailRegion := Region.singleton (.atom head ports)
        let splitRegion := Region.singleton splitItem
        exact ⟨{
          splitSource := .cons splitItem .nil
          headResult := headRegion.conjoin (Region.blank sourceWires)
          headEvidence := headEvidence
          headSites := headSites
          tailSource := .cons tailItem .nil
          tailResult := tailRegion.conjoin (Region.blank common)
          tailEvidence := tailEvidence
          tailSites := tailSites
          splitIso := ⟨by
            simpa [splitRegion, splitItem, splitHead, splitPorts, itemEdit,
              ExactEdit.refl] using (RegionIso.refl splitRegion)⟩
          splitScope := by
            simpa [splitItem, splitHead, splitPorts] using
              SupportParallelSplitScope.atom frames head ports
          tailSourceScope := by
            simpa [tailItem, headCommon, headPorts] using
              ScopePreservation.refl (Region.singleton tailItem)
          headBridge := by
            simpa [headRegion, tailItem] using
              HostedStrict.ofIso (RegionIso.conjoinBlank headRegion)
          headScope := by
            simpa [headRegion, tailItem] using
              ScopePreservation.ofIso (RegionIso.conjoinBlank headRegion)
          headReverseScope := by
            simpa [headRegion, tailItem] using
              ScopePreservation.ofIso
                (RegionIso.conjoinBlank headRegion).symm
          resultBridge := HostedStrict.ofIso
            (RegionIso.conjoinBlank tailRegion).symm
          resultScope := ScopePreservation.ofIso
            (RegionIso.conjoinBlank tailRegion).symm
        }⟩
    | .selectedAtom application siteData => by
        exact selectedCase (frames := frames) application siteData
    | .identity signature arity ports => by
        let headPorts := fun position => parallel.sourceKeep (ports position)
        let splitPorts := fun position => parallel.targetKeep (ports position)
        let splitItem := Item.identity signature arity splitPorts
        let tailItem := Item.identity signature arity headPorts
        have headPortsMap :
            (fun position => frames.head.sourceKeep (headPorts position)) =
              splitPorts := by
          funext position
          exact frames.head_keep (ports position)
        have tailPortsMap :
            (fun position => frames.tail.sourceKeep (ports position)) =
              headPorts := by
          funext position
          exact frames.tail_keep (ports position)
        let rawHeadItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected) signature arity headPorts
        have headItemEvidence :
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
              headPattern frames.head.sourceKeep frames.head.selected splitItem
              (Region.singleton (.identity signature arity headPorts)) := by
          simpa [splitItem, headPortsMap] using rawHeadItemEvidence
        let rawTailItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected) signature arity ports
        have tailItemEvidence :
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
              tailPattern frames.tail.sourceKeep frames.tail.selected tailItem
              (Region.singleton (.identity signature arity ports)) := by
          simpa [tailItem, tailPortsMap] using rawTailItemEvidence
        have headItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headItemEvidence := by
          simpa [splitItem, headPortsMap] using
            (ItemSites.identity
              (operation := recordingOperation (normalizationOperation []) [])
              (pattern := headPattern) (frame := frames.head)
              (data := PUnit.unit) signature arity headPorts)
        have tailItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailItemEvidence := by
          simpa [tailItem, tailPortsMap] using
            (ItemSites.identity
              (operation := recordingOperation (normalizationOperation []) [])
              (pattern := tailPattern) (frame := frames.tail)
              (data := PUnit.unit) signature arity ports)
        let headNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected)
        let tailNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected)
        let headEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            headItemEvidence headNil
        let tailEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            tailItemEvidence tailNil
        let headSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headEvidence := .cons headItemSites (.nil headNil)
        let tailSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailEvidence := .cons tailItemSites (.nil tailNil)
        let headRegion := Region.singleton
          (.identity signature arity headPorts)
        let tailRegion := Region.singleton (.identity signature arity ports)
        let splitRegion := Region.singleton splitItem
        exact ⟨{
          splitSource := .cons splitItem .nil
          headResult := headRegion.conjoin (Region.blank sourceWires)
          headEvidence := headEvidence
          headSites := headSites
          tailSource := .cons tailItem .nil
          tailResult := tailRegion.conjoin (Region.blank common)
          tailEvidence := tailEvidence
          tailSites := tailSites
          splitIso := ⟨by
            simpa [splitRegion, splitItem, splitPorts, itemEdit,
              ExactEdit.refl] using (RegionIso.refl splitRegion)⟩
          splitScope := by
            simpa [splitItem, splitPorts] using
              SupportParallelSplitScope.identity frames signature arity ports
          tailSourceScope := by
            simpa [tailItem, headPorts] using
              ScopePreservation.refl (Region.singleton tailItem)
          headBridge := by
            simpa [headRegion, tailItem] using
              HostedStrict.ofIso (RegionIso.conjoinBlank headRegion)
          headScope := by
            simpa [headRegion, tailItem] using
              ScopePreservation.ofIso (RegionIso.conjoinBlank headRegion)
          headReverseScope := by
            simpa [headRegion, tailItem] using
              ScopePreservation.ofIso
                (RegionIso.conjoinBlank headRegion).symm
          resultBridge := HostedStrict.ofIso
            (RegionIso.conjoinBlank tailRegion).symm
          resultScope := ScopePreservation.ofIso
            (RegionIso.conjoinBlank tailRegion).symm
        }⟩
    | .cut childSites => by
        obtain ⟨child⟩ := supportParallelRegionFactors_nonempty
          headPattern tailPattern fullPattern selectedCase frames _ childSites
        let splitItem := Item.cut child.splitSource
        let headItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            child.headEvidence
        let tailItemEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            child.tailEvidence
        let headNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := headPattern) (retain := frames.head.sourceKeep)
            (selected := frames.head.selected)
        let tailNil :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := tailPattern) (retain := frames.tail.sourceKeep)
            (selected := frames.tail.selected)
        let headEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            headItemEvidence headNil
        let tailEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            tailItemEvidence tailNil
        let headItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headItemEvidence := .cut child.headSites
        let tailItemSites : ItemSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailItemEvidence := .cut child.tailSites
        let headSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            headEvidence := .cons headItemSites (.nil headNil)
        let tailSites : ItemsSites
            (recordingOperation (normalizationOperation []) []) PUnit.unit
            tailEvidence := .cons tailItemSites (.nil tailNil)
        let headSingleton := Region.singleton (.cut child.headResult)
        let tailSingleton := Region.singleton (.cut child.tailSource)
        let resultSingleton := Region.singleton (.cut child.tailResult)
        obtain ⟨childSplitIso⟩ := child.splitIso
        exact ⟨{
          splitSource := .cons splitItem .nil
          headResult := headSingleton.conjoin (Region.blank sourceWires)
          headEvidence := headEvidence
          headSites := headSites
          tailSource := .cons (.cut child.tailSource) .nil
          tailResult := resultSingleton.conjoin (Region.blank common)
          tailEvidence := tailEvidence
          tailSites := tailSites
          splitIso := ⟨by
            simpa [splitItem] using
              RegionIso.singletonCutCongr childSplitIso⟩
          splitScope := by
            simpa [splitItem] using
              SupportParallelSplitScope.cut child.splitScope
          tailSourceScope := by
            simpa using ScopePreservation.cut child.tailSourceScope
          headBridge := HostedStrict.iso
            (RegionIso.conjoinBlank headSingleton)
            (RegionIso.refl tailSingleton)
            (HostedStrict.cut _ _ child.headBridge)
          headScope :=
            (ScopePreservation.ofIso
              (RegionIso.conjoinBlank headSingleton)).trans
              (ScopePreservation.cut child.headScope)
          headReverseScope :=
            (ScopePreservation.cut child.headReverseScope).trans
              (ScopePreservation.ofIso
                (RegionIso.conjoinBlank headSingleton).symm)
          resultBridge := HostedStrict.iso
            (RegionIso.refl _)
            (RegionIso.conjoinBlank resultSingleton).symm
            (HostedStrict.cut _ _ child.resultBridge)
          resultScope :=
            (ScopePreservation.cut child.resultScope).trans
              (ScopePreservation.ofIso
                (RegionIso.conjoinBlank resultSingleton).symm)
        }⟩
    termination_by sizeOf source
end

theorem supportParallelRootTailScope
    (outer before after : List Sig)
    {source : ItemSeq
      (outer ++ (before ++ .rel [] :: after))}
    {originalResult : Region (outer ++ (before ++ after))}
    {evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        fullPattern
        (Content.Parallel.rootFrame outer before after []).sourceKeep
        (Content.Parallel.rootFrame outer before after []).selected source
        originalResult}
    {sites : ItemsSites (Content.Parallel.operation [])
      (Content.Parallel.firstHead outer before after [],
        Content.Parallel.secondHead outer before after []) evidence}
    (factors : SupportParallelItemsFactors headPattern tailPattern fullPattern
      (supportParallelFramesRoot outer before after) evidence sites) :
    ScopePreservation
      (.mk (before ++ .rel [] :: after) source)
      (.mk (before ++ .rel [] :: after) factors.tailSource) := by
  let locals := before ++ .rel [] :: after
  have lifted := adjoinAt_preserves_scope locals .nil
    (Region.ofItems source) (Region.ofItems factors.tailSource)
    factors.tailSourceScope
  exact (ScopePreservation.ofIso
      (RegionIso.adjoinAtOfItems locals source).symm).trans
    (lifted.trans
      (ScopePreservation.ofIso
        (RegionIso.adjoinAtOfItems locals factors.tailSource)))

theorem supportParallelRootSplitScope
    (outer before after : List Sig)
    {source : ItemSeq
      (outer ++ (before ++ .rel [] :: after))}
    {originalResult : Region (outer ++ (before ++ after))}
    {evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        fullPattern
        (Content.Parallel.rootFrame outer before after []).sourceKeep
        (Content.Parallel.rootFrame outer before after []).selected source
        originalResult}
    {sites : ItemsSites (Content.Parallel.operation [])
      (Content.Parallel.firstHead outer before after [],
        Content.Parallel.secondHead outer before after []) evidence}
    (factors : SupportParallelItemsFactors headPattern tailPattern fullPattern
      (supportParallelFramesRoot outer before after) evidence sites) :
    ScopePreservation
      (.mk (before ++ .rel [] :: after) source)
      (.mk (before ++ .rel [] :: .rel [] :: after)
        factors.splitSource) := by
  let sourceLocals := before ++ .rel [] :: after
  let splitLocals := before ++ .rel [] :: .rel [] :: after
  let parallel := Content.Parallel.rootFrame outer before after []
  let heads : Content.Parallel.Heads
      (outer ++ splitLocals) [] :=
    (Content.Parallel.firstHead outer before after [],
      Content.Parallel.secondHead outer before after [])
  have targetMaterialRoots :
      (.mk sourceLocals source : Region outer).Canonical →
        ∀ targetIndex : Fin splitLocals.length,
          RegionPath.RootedTwo
            ((Region.ofItems factors.splitSource).incidencePaths
              (outer.length + targetIndex.val)) := by
    intro sourceCanonical
    intro targetIndex
    let targetLocal := Var.ofIndex targetIndex
    have targetRoot : RegionPath.RootedTwo
        ((Region.ofItems factors.splitSource).incidencePaths
          (outer.length + targetLocal.index.val)) := by
      refine Var.appendCases (left := before)
        (right := .rel [] :: .rel [] :: after)
        (motive := fun targetLocal => RegionPath.RootedTwo
          ((Region.ofItems factors.splitSource).incidencePaths
            (outer.length + targetLocal.index.val))) ?_ ?_ targetLocal
      · intro signature beforeWire
        let sourceLocal : Var sourceLocals signature :=
          beforeWire.appendLeft (.rel [] :: after)
        let commonLocal : Var (before ++ after) signature :=
          beforeWire.appendLeft after
        let commonWire : Var (outer ++ (before ++ after)) signature :=
          Var.appendRight outer commonLocal
        have sourceRoot := sourceCanonical.1 sourceLocal.index
        have sourceMaterialRoot : RegionPath.RootedTwo
            ((Region.ofItems source).incidencePaths
              (parallel.sourceKeep commonWire).index.val) := by
          rw [Region.incidencePaths_ofItems]
          simpa [parallel, sourceLocals, sourceLocal, commonWire,
            commonLocal, Content.Parallel.rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight, Var.index]
            using sourceRoot
        have splitRoot :=
          (factors.splitScope.retained commonWire).rooted sourceMaterialRoot
        simpa [parallel, splitLocals, commonWire, commonLocal,
          Content.Parallel.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep,
          Var.appendRight, Var.index] using splitRoot
      · intro signature remaining
        cases remaining with
        | here =>
            let sourceLocal : Var sourceLocals (.rel []) :=
              Var.appendRight before .here
            let sourceWire : Var (outer ++ sourceLocals) (.rel []) :=
              Var.appendRight outer sourceLocal
            have sourceRoot := sourceCanonical.1 sourceLocal.index
            have sourceMaterialRoot : RegionPath.RootedTwo
                ((Region.ofItems source).incidencePaths sourceWire.index.val) := by
              rw [Region.incidencePaths_ofItems]
              simpa [sourceWire, sourceLocal] using sourceRoot
            have splitRoot := factors.splitScope.first.rooted (by
              simpa [parallel, sourceWire, sourceLocal,
                Content.Parallel.rootFrame, Transform.Frame.replace,
                Transform.Frame.insertedHead] using sourceMaterialRoot)
            simpa [heads, splitLocals, Content.Parallel.firstHead,
              Transform.Frame.insertedHead] using splitRoot
        | there remaining =>
            cases remaining with
            | here =>
                let sourceLocal : Var sourceLocals (.rel []) :=
                  Var.appendRight before .here
                let sourceWire : Var (outer ++ sourceLocals) (.rel []) :=
                  Var.appendRight outer sourceLocal
                have sourceRoot := sourceCanonical.1 sourceLocal.index
                have sourceMaterialRoot : RegionPath.RootedTwo
                    ((Region.ofItems source).incidencePaths
                      sourceWire.index.val) := by
                  rw [Region.incidencePaths_ofItems]
                  simpa [sourceWire, sourceLocal] using sourceRoot
                have splitRoot := factors.splitScope.second.rooted (by
                  simpa [parallel, sourceWire, sourceLocal,
                    Content.Parallel.rootFrame, Transform.Frame.replace,
                    Transform.Frame.insertedHead] using sourceMaterialRoot)
                simpa [heads, splitLocals, Content.Parallel.secondHead,
                  Var.appendRight, Var.index] using splitRoot
            | there afterWire =>
                let sourceLocal : Var sourceLocals signature :=
                  Var.appendRight before (Var.there afterWire)
                let commonLocal : Var (before ++ after) signature :=
                  Var.appendRight before afterWire
                let commonWire : Var (outer ++ (before ++ after)) signature :=
                  Var.appendRight outer commonLocal
                have sourceRoot := sourceCanonical.1 sourceLocal.index
                have sourceMaterialRoot : RegionPath.RootedTwo
                    ((Region.ofItems source).incidencePaths
                      (parallel.sourceKeep commonWire).index.val) := by
                  rw [Region.incidencePaths_ofItems]
                  simpa [parallel, sourceLocals, sourceLocal, commonWire,
                    commonLocal, Content.Parallel.rootFrame,
                    Transform.Frame.replace, Transform.Frame.keep,
                    Transform.Frame.localKeep, Var.appendRight, Var.index]
                    using sourceRoot
                have splitRoot :=
                  (factors.splitScope.retained commonWire).rooted
                    sourceMaterialRoot
                simpa [parallel, splitLocals, commonWire, commonLocal,
                  Content.Parallel.rootFrame, Transform.Frame.replace,
                  Transform.Frame.keep, Transform.Frame.localKeep,
                  Var.appendRight, Var.index] using splitRoot
    simpa only [targetLocal, Var.index_ofIndex] using targetRoot
  constructor
  · intro sourceCanonical
    have sourceAdjoinedCanonical :
        (Region.adjoinAt sourceLocals .nil
          (Region.ofItems source)).Canonical :=
      (RegionIso.adjoinAtOfItems sourceLocals source).canonical_iff.mpr
        (by simpa [sourceLocals] using sourceCanonical)
    have sourceMaterialCanonical : (Region.ofItems source).Canonical :=
      Region.Canonical.material_of_adjoinAt sourceLocals .nil
        (Region.ofItems source) sourceAdjoinedCanonical
    have splitMaterialCanonical :=
      factors.splitScope.canonical sourceMaterialCanonical
    have splitAdjoinedCanonical :
        (Region.adjoinAt splitLocals .nil
          (Region.ofItems factors.splitSource)).Canonical := by
      exact Region.Canonical.adjoinAt_of_material_roots splitLocals .nil
        (Region.ofItems factors.splitSource) True.intro
        splitMaterialCanonical
        (targetMaterialRoots (by simpa [sourceLocals] using sourceCanonical))
    exact (RegionIso.adjoinAtOfItems splitLocals
      factors.splitSource).canonical_iff.mp (by
        simpa [splitLocals] using splitAdjoinedCanonical)
  · intro signature wire
    let commonWire : Var (outer ++ (before ++ after)) signature :=
      wire.appendLeft (before ++ after)
    let sourceAdjoined := Region.adjoinAt sourceLocals .nil
      (Region.ofItems source)
    let splitAdjoined := Region.adjoinAt splitLocals .nil
      (Region.ofItems factors.splitSource)
    have materialScope := factors.splitScope.retained commonWire
    have materialScope' : SupportParallelIncidenceScope
        ((Region.ofItems source).incidencePaths wire.index.val)
        ((Region.ofItems factors.splitSource).incidencePaths wire.index.val) := by
      simpa [parallel, commonWire, Content.Parallel.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using materialScope
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems source) (wire.appendLeft sourceLocals)
    have splitPaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems factors.splitSource) (wire.appendLeft splitLocals)
    have adjoinedScope : SupportParallelIncidenceScope
        (sourceAdjoined.incidencePaths wire.index.val)
        (splitAdjoined.incidencePaths wire.index.val) := by
      change SupportParallelIncidenceScope
        ((Region.adjoinAt sourceLocals .nil
          (Region.ofItems source)).incidencePaths wire.index.val)
        ((Region.adjoinAt splitLocals .nil
          (Region.ofItems factors.splitSource)).incidencePaths wire.index.val)
      have sourceEq :
          (Region.adjoinAt sourceLocals .nil
            (Region.ofItems source)).incidencePaths wire.index.val =
            (Region.ofItems source).incidencePaths wire.index.val := by
        simpa using sourcePaths
      have splitEq :
          (Region.adjoinAt splitLocals .nil
            (Region.ofItems factors.splitSource)).incidencePaths
              wire.index.val =
            (Region.ofItems factors.splitSource).incidencePaths
              wire.index.val := by
        simpa using splitPaths
      rw [sourceEq, splitEq]
      exact materialScope'
    exact (SupportParallelIncidenceScope.iso
      (RegionIso.adjoinAtOfItems sourceLocals source).symm
      (RegionIso.adjoinAtOfItems splitLocals factors.splitSource)
      wire wire adjoinedScope).nonempty
  · intro signature wire rooted
    let commonWire : Var (outer ++ (before ++ after)) signature :=
      wire.appendLeft (before ++ after)
    let sourceAdjoined := Region.adjoinAt sourceLocals .nil
      (Region.ofItems source)
    let splitAdjoined := Region.adjoinAt splitLocals .nil
      (Region.ofItems factors.splitSource)
    have materialScope := factors.splitScope.retained commonWire
    have materialScope' : SupportParallelIncidenceScope
        ((Region.ofItems source).incidencePaths wire.index.val)
        ((Region.ofItems factors.splitSource).incidencePaths wire.index.val) := by
      simpa [parallel, commonWire, Content.Parallel.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using materialScope
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems source) (wire.appendLeft sourceLocals)
    have splitPaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems factors.splitSource) (wire.appendLeft splitLocals)
    have adjoinedScope : SupportParallelIncidenceScope
        (sourceAdjoined.incidencePaths wire.index.val)
        (splitAdjoined.incidencePaths wire.index.val) := by
      change SupportParallelIncidenceScope
        ((Region.adjoinAt sourceLocals .nil
          (Region.ofItems source)).incidencePaths wire.index.val)
        ((Region.adjoinAt splitLocals .nil
          (Region.ofItems factors.splitSource)).incidencePaths wire.index.val)
      have sourceEq :
          (Region.adjoinAt sourceLocals .nil
            (Region.ofItems source)).incidencePaths wire.index.val =
            (Region.ofItems source).incidencePaths wire.index.val := by
        simpa using sourcePaths
      have splitEq :
          (Region.adjoinAt splitLocals .nil
            (Region.ofItems factors.splitSource)).incidencePaths
              wire.index.val =
            (Region.ofItems factors.splitSource).incidencePaths
              wire.index.val := by
        simpa using splitPaths
      rw [sourceEq, splitEq]
      exact materialScope'
    exact (SupportParallelIncidenceScope.iso
      (RegionIso.adjoinAtOfItems sourceLocals source).symm
      (RegionIso.adjoinAtOfItems splitLocals factors.splitSource)
      wire wire adjoinedScope).rooted rooted


theorem supportParallelSelectedFactors_nonempty
    {common sourceWires splitWires : List Sig}
    {parallel : Transform.Frame [] common sourceWires splitWires}
    {heads : Content.Parallel.Heads splitWires []}
    {sitePattern : OpenDiagram []}
    (frames : SupportParallelFrames parallel heads)
    (materialHead : Item [])
    (materialTail : ItemSeq [])
    (headCanonical : (Region.singleton materialHead).Canonical)
    (tailCanonical : (Region.ofItems materialTail).Canonical)
    (fullCanonical : (Region.ofItems (.cons materialHead materialTail)).Canonical)
    (application : Vars common [])
    (siteData : (Content.Parallel.operation []).SiteData parallel heads application) :
    let headPattern := Erasure.Exposure.supportPattern
      (Region.singleton materialHead) headCanonical
    let tailPattern := Erasure.Exposure.supportPattern
      (Region.ofItems materialTail) tailCanonical
    let fullPattern := Erasure.Exposure.supportPattern
      (Region.ofItems (.cons materialHead materialTail)) fullCanonical
    Nonempty (SupportParallelItemFactors headPattern tailPattern fullPattern frames
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := fullPattern) application)
      (@ItemSites.selectedAtom [] (Content.Parallel.operation []) fullPattern
        common sourceWires splitWires sitePattern parallel heads application
        siteData)) := by
  dsimp only
  let headPattern := Erasure.Exposure.supportPattern
    (Region.singleton materialHead) headCanonical
  let tailPattern := Erasure.Exposure.supportPattern
    (Region.ofItems materialTail) tailCanonical
  let fullPattern := Erasure.Exposure.supportPattern
    (Region.ofItems (.cons materialHead materialTail)) fullCanonical
  let headApplication := application.map fun wire => frames.tail.sourceKeep wire
  let firstItem : Item splitWires := .atom frames.head.selected
    (headApplication.map fun wire => frames.head.sourceKeep wire)
  let secondItem : Item splitWires := .atom
    (frames.head.sourceKeep frames.tail.selected)
    (headApplication.map fun wire => frames.head.sourceKeep wire)
  let splitSource : ItemSeq splitWires := .cons firstItem (.cons secondItem .nil)
  let materialHeadAtCommon : Item common := materialHead.renameWires
    (EqualityNormalization.formalSubstitution application)
  let tailSource : ItemSeq sourceWires :=
    .cons (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
      (.cons (.atom frames.tail.selected headApplication) .nil)
  let headResult : Region sourceWires :=
    (VisualProof.Rule.Comprehension.Instantiation.instantiate
      headPattern headApplication).conjoin
      ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
        (Region.blank _))
  let tailResult : Region common :=
    (retainedItemPresentation materialHeadAtCommon).conjoin
      ((VisualProof.Rule.Comprehension.Instantiation.instantiate
        tailPattern application).conjoin (Region.blank _))
  let headEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        headPattern frames.head.sourceKeep frames.head.selected splitSource
          headResult := by
    exact .cons (.selectedAtom headApplication)
      (.cons (.atom frames.tail.selected headApplication) .nil)
  let headSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
        headEvidence := by
    let nilEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          headPattern frames.head.sourceKeep frames.head.selected .nil
            (Region.blank _) := .nil
    let nilSites : ItemsSites
        (recordingOperation (normalizationOperation []) []) PUnit.unit
          nilEvidence := .nil nilEvidence
    let atomEvidence :=
      VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
        (pattern := headPattern) (retain := frames.head.sourceKeep)
        (selected := frames.head.selected) frames.tail.selected headApplication
    let atomSites : ItemSites
        (recordingOperation (normalizationOperation []) []) PUnit.unit
          atomEvidence := .atom (pattern := headPattern) frames.tail.selected
            headApplication
    let selectedEvidence :=
      VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := headPattern) (retain := frames.head.sourceKeep)
        (selected := frames.head.selected) headApplication
    let selectedSites : ItemSites
        (recordingOperation (normalizationOperation []) []) PUnit.unit
          selectedEvidence := .selectedAtom (pattern := headPattern)
            headApplication (PUnit.unit, headApplication)
    exact .cons selectedSites (.cons atomSites nilSites)
  let tailEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        tailPattern frames.tail.sourceKeep frames.tail.selected tailSource
          tailResult := by
    exact .cons (retainedItemResult tailPattern frames.tail materialHeadAtCommon)
      (.cons (.selectedAtom application) .nil)
  let tailSites : ItemsSites
      (recordingOperation (normalizationOperation []) []) PUnit.unit
        tailEvidence := by
    let nilEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          tailPattern frames.tail.sourceKeep frames.tail.selected .nil
            (Region.blank _) := .nil
    let nilSites : ItemsSites
        (recordingOperation (normalizationOperation []) []) PUnit.unit
          nilEvidence := .nil nilEvidence
    let selectedEvidence :=
      VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := tailPattern) (retain := frames.tail.sourceKeep)
        (selected := frames.tail.selected) application
    let selectedSites : ItemSites
        (recordingOperation (normalizationOperation []) []) PUnit.unit
          selectedEvidence := .selectedAtom (pattern := tailPattern)
            application (PUnit.unit, application)
    exact .cons
      (retainedItemSites tailPattern
        (recordingOperation (normalizationOperation []) []) frames.tail
        PUnit.unit materialHeadAtCommon)
      (.cons selectedSites nilSites)
  have siteEq :
      (Content.Parallel.operation []).site parallel heads application siteData =
        (Region.singleton firstItem).conjoin (Region.singleton secondItem) := by
    simp only [Content.Parallel.operation]
    rcases application with ⟨⟩
    simp only [firstItem, secondItem, headApplication, Vars.map]
    rw [frames.first_selected, frames.second_selected]
  have splitEq :
      (Region.singleton firstItem).conjoin
          ((Region.singleton secondItem).conjoin (Region.blank _)) =
        Region.ofItems splitSource := by
    have secondEq :
        (Region.singleton secondItem).conjoin (Region.blank _) =
          Region.ofItems (.cons secondItem .nil) := by
      simpa only [Region.blank, Region.ofItems, ItemSeq.renameWires] using
        Region.singleton_conjoin_ofItems secondItem .nil
    rw [secondEq]
    exact Region.singleton_conjoin_ofItems firstItem (.cons secondItem .nil)
  let splitIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
      (itemEdit (operation := Content.Parallel.operation []) heads
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := fullPattern) application)
        (@ItemSites.selectedAtom [] (Content.Parallel.operation []) fullPattern
          common sourceWires splitWires sitePattern parallel heads application
          siteData)).endpoint
      (Region.ofItems splitSource)) := ⟨
    (RegionIso.ofEq siteEq).trans
      ((RegionIso.conjoinCongr
        (RegionIso.refl (Region.singleton firstItem))
        (RegionIso.conjoinBlank (Region.singleton secondItem)).symm).trans
          (RegionIso.ofEq splitEq))⟩
  refine ⟨{
    splitSource := splitSource
    headResult := headResult
    headEvidence := headEvidence
    headSites := headSites
    tailSource := tailSource
    tailResult := tailResult
    tailEvidence := tailEvidence
    tailSites := tailSites
    splitIso := splitIso
    splitScope := ?_
    tailSourceScope := ?_
    headBridge := ?_
    headScope := ?_
    headReverseScope := ?_
    resultBridge := ?_
    resultScope := ?_
  }⟩
  · rcases application with ⟨⟩
    simp only [splitSource, firstItem, secondItem, headApplication, Vars.map]
    simpa [frames.first_selected, frames.second_selected] using
      SupportParallelSplitScope.selected frames
  · let sourceAtom := Region.singleton (.atom parallel.selected
      (application.map fun wire => parallel.sourceKeep wire))
    let targetAtom := Region.singleton
      (.atom frames.tail.selected headApplication)
    let materialRegion := Region.singleton
      (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
    have materialHeadAtCommonCanonical :
        (Region.singleton materialHeadAtCommon).Canonical := by
      simpa only [materialHeadAtCommon, Region.singleton_renameWires] using
        (Region.Canonical.renameWires_iff (Region.singleton materialHead)
          (EqualityNormalization.formalSubstitution application)).mpr
            headCanonical
    have materialCanonical : materialRegion.Canonical := by
      simpa only [materialRegion, Region.singleton_renameWires] using
        (Region.Canonical.renameWires_iff
          (Region.singleton materialHeadAtCommon) frames.tail.sourceKeep).mpr
            materialHeadAtCommonCanonical
    let materialRename := WireRenaming.comp frames.tail.sourceKeep
      (EqualityNormalization.formalSubstitution application)
    have materialRegionEq : materialRegion =
        (Region.singleton materialHead).renameWires materialRename := by
      simp only [materialRegion, materialHeadAtCommon, materialRename,
        Region.singleton_renameWires, Item.renameWires_comp]
    have materialEmpty : ∀ {signature} (wire : Var sourceWires signature),
        materialRegion.incidencePaths wire.index.val = [] := by
      intro signature wire
      rw [materialRegionEq]
      simp only [Region.singleton, Region.ofItems, Region.renameWires,
        Region.incidencePaths]
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · simp
      · intro materialSignature materialWire
        cases materialWire
    have materialScope : ScopePreservation (Region.blank sourceWires)
        materialRegion :=
      ScopePreservation.of_incidence_empty materialCanonical
        (by intro signature wire; rfl) materialEmpty
    have atomEq : sourceAtom = targetAtom := by
      rcases application with ⟨⟩
      simp only [sourceAtom, targetAtom, headApplication, Vars.map]
      rw [frames.tail_selected]
    have atomScope : ScopePreservation sourceAtom targetAtom :=
      ScopePreservation.ofIso (RegionIso.ofEq atomEq)
    have targetEq : materialRegion.conjoin
          (targetAtom.conjoin (Region.blank sourceWires)) =
        Region.ofItems tailSource := by
      simp only [materialRegion, targetAtom]
      have tailEq : targetAtom.conjoin (Region.blank sourceWires) =
          Region.ofItems
            (.cons (.atom frames.tail.selected headApplication) .nil) := by
        simpa only [targetAtom, Region.blank, Region.ofItems,
          ItemSeq.renameWires] using
          Region.singleton_conjoin_ofItems
            (.atom frames.tail.selected headApplication) .nil
      rw [tailEq]
      exact Region.singleton_conjoin_ofItems
        (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
        (.cons (.atom frames.tail.selected headApplication) .nil)
    let sourcePresentation := (RegionIso.blankConjoin sourceAtom).symm
    exact (ScopePreservation.ofIso sourcePresentation).trans
      ((ScopePreservation.conjoin materialScope
        (atomScope.trans
          (ScopePreservation.ofIso
            (RegionIso.conjoinBlank targetAtom).symm))).trans
        (ScopePreservation.ofIso (RegionIso.ofEq targetEq)))
  · have substitutionEq :
        WireRenaming.comp frames.tail.sourceKeep
            (EqualityNormalization.formalSubstitution application) =
          EqualityNormalization.formalSubstitution headApplication := by
      apply WireRenaming.ext
      intro signature wire
      cases wire
    have materialItemEq :
        materialHeadAtCommon.renameWires frames.tail.sourceKeep =
          materialHead.renameWires
            (EqualityNormalization.formalSubstitution headApplication) := by
      rw [Item.renameWires_comp, substitutionEq]
    have targetEq :
        ((Region.singleton materialHead).renameWires
            (EqualityNormalization.formalSubstitution headApplication)).conjoin
          ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
            (Region.blank _)) = Region.ofItems tailSource := by
      rw [Region.singleton_renameWires, ← materialItemEq]
      have tailEq :
          (Region.singleton (.atom frames.tail.selected headApplication)).conjoin
              (Region.blank _) =
            Region.ofItems
              (.cons (.atom frames.tail.selected headApplication) .nil) := by
        simpa only [Region.blank, Region.ofItems, ItemSeq.renameWires] using
          Region.singleton_conjoin_ofItems
            (.atom frames.tail.selected headApplication) .nil
      rw [tailEq]
      exact Region.singleton_conjoin_ofItems
        (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
        (.cons (.atom frames.tail.selected headApplication) .nil)
    exact HostedStrict.iso (RegionIso.refl headResult) (RegionIso.ofEq targetEq)
      (HostedStrict.conjoin
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          headPattern headApplication)
        ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
          (Region.blank _))
        ((Region.singleton materialHead).renameWires
          (EqualityNormalization.formalSubstitution headApplication))
        ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
          (Region.blank _))
        (supportInstantiationHosted
          (Region.singleton materialHead) headCanonical headApplication)
        (HostedStrict.refl
          ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
            (Region.blank _))))
  · have substitutionEq :
        WireRenaming.comp frames.tail.sourceKeep
            (EqualityNormalization.formalSubstitution application) =
          EqualityNormalization.formalSubstitution headApplication := by
      apply WireRenaming.ext
      intro signature wire
      cases wire
    have materialItemEq :
        materialHeadAtCommon.renameWires frames.tail.sourceKeep =
          materialHead.renameWires
            (EqualityNormalization.formalSubstitution headApplication) := by
      rw [Item.renameWires_comp, substitutionEq]
    have targetEq :
        ((Region.singleton materialHead).renameWires
            (EqualityNormalization.formalSubstitution headApplication)).conjoin
          ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
            (Region.blank _)) = Region.ofItems tailSource := by
      rw [Region.singleton_renameWires, ← materialItemEq]
      have tailEq :
          (Region.singleton (.atom frames.tail.selected headApplication)).conjoin
              (Region.blank _) =
            Region.ofItems
              (.cons (.atom frames.tail.selected headApplication) .nil) := by
        simpa only [Region.blank, Region.ofItems, ItemSeq.renameWires] using
          Region.singleton_conjoin_ofItems
            (.atom frames.tail.selected headApplication) .nil
      rw [tailEq]
      exact Region.singleton_conjoin_ofItems
        (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
        (.cons (.atom frames.tail.selected headApplication) .nil)
    let instantiated :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        headPattern headApplication
    let exposed := (Region.singleton materialHead).renameWires
      (EqualityNormalization.formalSubstitution headApplication)
    have instantiatedEmpty : ∀ {signature} (wire : Var sourceWires signature),
        instantiated.incidencePaths wire.index.val = [] := by
      intro signature wire
      apply List.eq_nil_of_length_eq_zero
      rw [EqualityNormalization.instantiate_incidencePaths_length]
      cases headApplication
      rfl
    have exposedEmpty : ∀ {signature} (wire : Var sourceWires signature),
        exposed.incidencePaths wire.index.val = [] := by
      intro signature wire
      simp only [exposed, Region.singleton, Region.ofItems,
        Region.renameWires, Region.incidencePaths]
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · simp
      · intro materialSignature materialWire
        cases materialWire
    have exposedCanonical : exposed.Canonical :=
      (Region.Canonical.renameWires_iff (Region.singleton materialHead)
        (EqualityNormalization.formalSubstitution headApplication)).mpr
          headCanonical
    have supportScope : ScopePreservation instantiated exposed :=
      ScopePreservation.of_incidence_empty
        exposedCanonical instantiatedEmpty exposedEmpty
    exact (ScopePreservation.conjoin supportScope
      (ScopePreservation.refl
        ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
          (Region.blank _)))).trans
      (ScopePreservation.ofIso (RegionIso.ofEq targetEq))
  · have substitutionEq :
        WireRenaming.comp frames.tail.sourceKeep
            (EqualityNormalization.formalSubstitution application) =
          EqualityNormalization.formalSubstitution headApplication := by
      apply WireRenaming.ext
      intro signature wire
      cases wire
    have materialItemEq :
        materialHeadAtCommon.renameWires frames.tail.sourceKeep =
          materialHead.renameWires
            (EqualityNormalization.formalSubstitution headApplication) := by
      rw [Item.renameWires_comp, substitutionEq]
    have targetEq :
        ((Region.singleton materialHead).renameWires
            (EqualityNormalization.formalSubstitution headApplication)).conjoin
          ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
            (Region.blank _)) = Region.ofItems tailSource := by
      rw [Region.singleton_renameWires, ← materialItemEq]
      have tailEq :
          (Region.singleton (.atom frames.tail.selected headApplication)).conjoin
              (Region.blank _) =
            Region.ofItems
              (.cons (.atom frames.tail.selected headApplication) .nil) := by
        simpa only [Region.blank, Region.ofItems, ItemSeq.renameWires] using
          Region.singleton_conjoin_ofItems
            (.atom frames.tail.selected headApplication) .nil
      rw [tailEq]
      exact Region.singleton_conjoin_ofItems
        (materialHeadAtCommon.renameWires frames.tail.sourceKeep)
        (.cons (.atom frames.tail.selected headApplication) .nil)
    let instantiated :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        headPattern headApplication
    let exposed := (Region.singleton materialHead).renameWires
      (EqualityNormalization.formalSubstitution headApplication)
    have instantiatedEmpty : ∀ {signature} (wire : Var sourceWires signature),
        instantiated.incidencePaths wire.index.val = [] := by
      intro signature wire
      apply List.eq_nil_of_length_eq_zero
      rw [EqualityNormalization.instantiate_incidencePaths_length]
      cases headApplication
      rfl
    have exposedEmpty : ∀ {signature} (wire : Var sourceWires signature),
        exposed.incidencePaths wire.index.val = [] := by
      intro signature wire
      simp only [exposed, Region.singleton, Region.ofItems,
        Region.renameWires, Region.incidencePaths]
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · simp
      · intro materialSignature materialWire
        cases materialWire
    have instantiatedCanonical : instantiated.Canonical :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        headPattern headApplication
    have reverseSupportScope : ScopePreservation exposed instantiated :=
      ScopePreservation.of_incidence_empty
        instantiatedCanonical exposedEmpty instantiatedEmpty
    exact (ScopePreservation.ofIso (RegionIso.ofEq targetEq.symm)).trans
      (ScopePreservation.conjoin reverseSupportScope
        (ScopePreservation.refl
          ((Region.singleton (.atom frames.tail.selected headApplication)).conjoin
            (Region.blank _))))
  · let fullExposed :=
      (Region.ofItems (.cons materialHead materialTail)).renameWires
        (EqualityNormalization.formalSubstitution application)
    let tailExposed := (Region.ofItems materialTail).renameWires
      (EqualityNormalization.formalSubstitution application)
    have materialPresentation :
        (Region.singleton materialHead).conjoin (Region.ofItems materialTail) =
          Region.ofItems (.cons materialHead materialTail) :=
      Region.singleton_conjoin_ofItems materialHead materialTail
    have fullEq : fullExposed =
        (Region.singleton materialHeadAtCommon).conjoin tailExposed := by
      simp only [fullExposed, tailExposed, materialHeadAtCommon]
      rw [← materialPresentation, Region.renameWires_conjoin,
        Region.singleton_renameWires]
    have fullHosted : HostedStrict
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          fullPattern application) fullExposed :=
      supportInstantiationHosted
        (Region.ofItems (.cons materialHead materialTail)) fullCanonical
          application
    have headHosted : HostedStrict
        (retainedItemPresentation materialHeadAtCommon)
        (Region.singleton materialHeadAtCommon) :=
      HostedStrict.ofIso (retainedItemPresentationIso materialHeadAtCommon)
    have tailHosted : HostedStrict
        ((VisualProof.Rule.Comprehension.Instantiation.instantiate
          tailPattern application).conjoin (Region.blank _)) tailExposed :=
      HostedStrict.iso
        (RegionIso.conjoinBlank
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            tailPattern application))
        (RegionIso.refl tailExposed)
        (supportInstantiationHosted
          (Region.ofItems materialTail) tailCanonical application)
    have combinedHosted : HostedStrict tailResult
        ((Region.singleton materialHeadAtCommon).conjoin tailExposed) :=
      HostedStrict.conjoin
        (retainedItemPresentation materialHeadAtCommon)
        ((VisualProof.Rule.Comprehension.Instantiation.instantiate
          tailPattern application).conjoin (Region.blank _))
        (Region.singleton materialHeadAtCommon) tailExposed
        headHosted tailHosted
    have tailToFull : HostedStrict tailResult fullExposed :=
      HostedStrict.iso (RegionIso.refl tailResult)
        (RegionIso.ofEq fullEq.symm) combinedHosted
    exact HostedStrict.trans fullHosted tailToFull.symm (by
      intro outer hostLocals rename hostItems
      let tailInstantiated :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          tailPattern application
      have tailInstantiatedRenamedEmpty : ∀ {signature}
          (wire : Var (outer ++ hostLocals) signature),
          (tailInstantiated.renameWires rename).incidencePaths
              wire.index.val = [] := by
        intro signature wire
        rw [EqualityNormalization.instantiate_renameWires]
        apply List.eq_nil_of_length_eq_zero
        rw [EqualityNormalization.instantiate_incidencePaths_length]
        cases application
        rfl
      have tailExposedRenamedEmpty : ∀ {signature}
          (wire : Var (outer ++ hostLocals) signature),
          (tailExposed.renameWires rename).incidencePaths wire.index.val = [] := by
        intro signature wire
        simp only [tailExposed]
        rw [Region.renameWires_comp]
        simp only [Region.ofItems, Region.renameWires, Region.incidencePaths]
        apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
        · simpa using wire.index.isLt
        · intro materialSignature materialWire
          cases materialWire
      have tailExposedCanonical : tailExposed.Canonical :=
        (Region.Canonical.renameWires_iff (Region.ofItems materialTail)
          (EqualityNormalization.formalSubstitution application)).mpr
            tailCanonical
      have tailExposedRenamedCanonical :
          (tailExposed.renameWires rename).Canonical :=
        (Region.Canonical.renameWires_iff tailExposed rename).mpr
          tailExposedCanonical
      have renamedTailScope : ScopePreservation
          (tailInstantiated.renameWires rename)
          (tailExposed.renameWires rename) :=
        ScopePreservation.of_incidence_empty
          tailExposedRenamedCanonical
          tailInstantiatedRenamedEmpty tailExposedRenamedEmpty
      let tailPresentation : RegionIso (WireEquiv.refl common) tailResult
          ((Region.singleton materialHeadAtCommon).conjoin tailInstantiated) :=
        RegionIso.conjoinCongr
          (retainedItemPresentationIso materialHeadAtCommon)
          (RegionIso.conjoinBlank tailInstantiated)
      let mappedTailPresentation : RegionIso
          (WireEquiv.refl (outer ++ hostLocals))
          (tailResult.renameWires rename)
          (((Region.singleton materialHeadAtCommon).conjoin
            tailInstantiated).renameWires rename) :=
        RegionIso.renameExisting tailPresentation rename rename
          (WireEquiv.refl (outer ++ hostLocals)) (fun _ => rfl)
      let tailSourcePresentation : RegionIso
          (WireEquiv.refl (outer ++ hostLocals))
          (tailResult.renameWires rename)
          ((Region.singleton materialHeadAtCommon).renameWires rename |>.conjoin
            (tailInstantiated.renameWires rename)) :=
        mappedTailPresentation.trans
          (RegionIso.ofEq (Region.renameWires_conjoin
            (Region.singleton materialHeadAtCommon) tailInstantiated rename))
      have componentScope : ScopePreservation
          ((Region.singleton materialHeadAtCommon).renameWires rename |>.conjoin
            (tailInstantiated.renameWires rename))
          ((Region.singleton materialHeadAtCommon).renameWires rename |>.conjoin
            (tailExposed.renameWires rename)) :=
        ScopePreservation.conjoin
          (ScopePreservation.refl
            ((Region.singleton materialHeadAtCommon).renameWires rename))
          renamedTailScope
      let fullPresentation : RegionIso (WireEquiv.refl common) fullExposed
          ((Region.singleton materialHeadAtCommon).conjoin tailExposed) :=
        RegionIso.ofEq fullEq
      let mappedFullPresentation : RegionIso
          (WireEquiv.refl (outer ++ hostLocals))
          (fullExposed.renameWires rename)
          (((Region.singleton materialHeadAtCommon).conjoin
            tailExposed).renameWires rename) :=
        RegionIso.renameExisting fullPresentation rename rename
          (WireEquiv.refl (outer ++ hostLocals)) (fun _ => rfl)
      let tailTargetPresentation : RegionIso
          (WireEquiv.refl (outer ++ hostLocals))
          ((Region.singleton materialHeadAtCommon).renameWires rename |>.conjoin
            (tailExposed.renameWires rename))
          (fullExposed.renameWires rename) :=
        (RegionIso.ofEq (Region.renameWires_conjoin
          (Region.singleton materialHeadAtCommon) tailExposed rename).symm).trans
            mappedFullPresentation.symm
      have materialScope : ScopePreservation
          (tailResult.renameWires rename) (fullExposed.renameWires rename) :=
        (ScopePreservation.ofIso tailSourcePresentation).trans
          (componentScope.trans
            (ScopePreservation.ofIso tailTargetPresentation))
      exact adjoinAt_preserves_scope hostLocals hostItems
        (tailResult.renameWires rename) (fullExposed.renameWires rename)
          materialScope)
  · let fullInstantiated :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        fullPattern application
    let tailInstantiated :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        tailPattern application
    let fullExposed :=
      (Region.ofItems (.cons materialHead materialTail)).renameWires
        (EqualityNormalization.formalSubstitution application)
    let tailExposed := (Region.ofItems materialTail).renameWires
      (EqualityNormalization.formalSubstitution application)
    have materialPresentation :
        (Region.singleton materialHead).conjoin (Region.ofItems materialTail) =
          Region.ofItems (.cons materialHead materialTail) :=
      Region.singleton_conjoin_ofItems materialHead materialTail
    have fullEq : fullExposed =
        (Region.singleton materialHeadAtCommon).conjoin tailExposed := by
      simp only [fullExposed, tailExposed, materialHeadAtCommon]
      rw [← materialPresentation, Region.renameWires_conjoin,
        Region.singleton_renameWires]
    have fullInstantiatedEmpty : ∀ {signature} (wire : Var common signature),
        fullInstantiated.incidencePaths wire.index.val = [] := by
      intro signature wire
      apply List.eq_nil_of_length_eq_zero
      rw [EqualityNormalization.instantiate_incidencePaths_length]
      cases application
      rfl
    have tailInstantiatedEmpty : ∀ {signature} (wire : Var common signature),
        tailInstantiated.incidencePaths wire.index.val = [] := by
      intro signature wire
      apply List.eq_nil_of_length_eq_zero
      rw [EqualityNormalization.instantiate_incidencePaths_length]
      cases application
      rfl
    have fullExposedEmpty : ∀ {signature} (wire : Var common signature),
        fullExposed.incidencePaths wire.index.val = [] := by
      intro signature wire
      simp only [fullExposed, Region.ofItems, Region.renameWires,
        Region.incidencePaths]
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · simp
      · intro materialSignature materialWire
        cases materialWire
    have tailExposedEmpty : ∀ {signature} (wire : Var common signature),
        tailExposed.incidencePaths wire.index.val = [] := by
      intro signature wire
      simp only [tailExposed, Region.ofItems, Region.renameWires,
        Region.incidencePaths]
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · simp
      · intro materialSignature materialWire
        cases materialWire
    have fullExposedCanonical : fullExposed.Canonical :=
      (Region.Canonical.renameWires_iff
        (Region.ofItems (.cons materialHead materialTail))
        (EqualityNormalization.formalSubstitution application)).mpr
          fullCanonical
    have tailInstantiatedCanonical : tailInstantiated.Canonical :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        tailPattern application
    have fullSupportScope : ScopePreservation fullInstantiated fullExposed :=
      ScopePreservation.of_incidence_empty fullExposedCanonical
        fullInstantiatedEmpty fullExposedEmpty
    have tailReverseScope : ScopePreservation tailExposed tailInstantiated :=
      ScopePreservation.of_incidence_empty
        tailInstantiatedCanonical
        tailExposedEmpty tailInstantiatedEmpty
    have tailWithBlankScope : ScopePreservation tailExposed
        (tailInstantiated.conjoin (Region.blank _)) :=
      tailReverseScope.trans
        (ScopePreservation.ofIso
          (RegionIso.conjoinBlank tailInstantiated).symm)
    have headPresentationScope : ScopePreservation
        (Region.singleton materialHeadAtCommon)
        (retainedItemPresentation materialHeadAtCommon) :=
      ScopePreservation.ofIso
        (retainedItemPresentationIso materialHeadAtCommon).symm
    exact fullSupportScope |>.trans
      ((ScopePreservation.ofIso (RegionIso.ofEq fullEq)).trans
        (ScopePreservation.conjoin headPresentationScope tailWithBlankScope))

end VisualProof.Rule.Completeness.Comprehension.Structural
