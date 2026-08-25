import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel
import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

theorem supportParallelAppendRightNil
    (wire : Var wires signature) : Var.appendRight [] wire = wire := by
  induction wire with
  | here => rfl
  | there wire induction => exact congrArg Var.there induction

/-- The one coherent pair of sequential comprehension frames underlying a
Parallel edit. The first child removes the first split binder, the second
removes the remaining binder, and their retained maps compose to the edit's
target map. -/
structure SupportParallelFrames
    {arguments common sourceWires splitWires middleWires : List Sig}
    (frame : Transform.Frame arguments common sourceWires splitWires)
    (data : (Content.Parallel.operation arguments).Data frame) where
  head : Transform.Frame arguments middleWires splitWires middleWires
  tail : Transform.Frame arguments common middleWires common
  headTarget : ∀ {signature} (wire : Var middleWires signature),
    head.targetKeep wire = wire
  tailTarget : ∀ {signature} (wire : Var common signature),
    tail.targetKeep wire = wire
  retained : ∀ {signature} (wire : Var common signature),
    head.sourceKeep (tail.sourceKeep wire) = frame.targetKeep wire
  first : head.selected = data.1
  second : head.sourceKeep tail.selected = data.2

def SupportParallelFrames.append
    {arguments common sourceWires splitWires middleWires locals : List Sig}
    {frame : Transform.Frame arguments common sourceWires splitWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    (frames : SupportParallelFrames
      (middleWires := middleWires) frame data) :
    SupportParallelFrames (middleWires := middleWires ++ locals)
      (frame.append locals)
      ((Content.Parallel.operation arguments).appendData frame data locals) :=
  {
    head := frames.head.append locals
    tail := frames.tail.append locals
    headTarget := by
      intro signature wire
      apply Var.appendCases (left := middleWires) (right := locals)
        (motive := fun wire =>
          (frames.head.append locals).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.headTarget inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    tailTarget := by
      intro signature wire
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun wire =>
          (frames.tail.append locals).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.tailTarget inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    retained := by
      intro signature wire
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun wire =>
          ((frames.head.append locals).sourceKeep
              ((frames.tail.append locals).sourceKeep wire)) =
            (frame.append locals).targetKeep wire)
      · intro inheritedSignature inherited
        simpa [Transform.Frame.append, WireRenaming.appendRight] using
          congrArg (fun wire => wire.appendLeft locals)
            (frames.retained inherited)
      · intro localSignature localWire
        simp [Transform.Frame.append, WireRenaming.appendRight]
    first := by
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using congrArg (fun wire =>
          wire.appendLeft locals) frames.first
    second := by
      simpa [Content.Parallel.operation, Transform.Frame.append,
        WireRenaming.appendRight] using congrArg (fun wire =>
          wire.appendLeft locals) frames.second
  }

def supportParallelRootFrames
    (outer before after arguments : List Sig) :
    SupportParallelFrames
      (middleWires :=
        outer ++ (before ++ .rel arguments :: after))
      (Content.Parallel.rootFrame outer before after arguments)
      (Content.Parallel.firstHead outer before after arguments,
        Content.Parallel.secondHead outer before after arguments) :=
  {
    head := Transform.Frame.replace outer before
      (.rel arguments :: after) [] arguments
    tail := Transform.Frame.replace outer before after [] arguments
    headTarget := by
      intro signature wire
      apply Var.appendCases (left := outer)
        (right := before ++ .rel arguments :: after)
        (motive := fun wire =>
          (Transform.Frame.replace outer before
            (.rel arguments :: after) [] arguments).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [Transform.Frame.replace, Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before)
          (right := .rel arguments :: after)
          (motive := fun localWire' =>
            (Transform.Frame.replace outer before
              (.rel arguments :: after) [] arguments).targetKeep
                (Var.appendRight outer localWire') =
                  Var.appendRight outer localWire')
        · intro beforeSignature beforeWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
          exact congrArg (fun wire => Var.appendRight outer
            (Var.appendRight before wire))
              (supportParallelAppendRightNil afterWire)
    tailTarget := by
      intro signature wire
      apply Var.appendCases (left := outer) (right := before ++ after)
        (motive := fun wire =>
          (Transform.Frame.replace outer before after [] arguments
            ).targetKeep wire = wire)
      · intro inheritedSignature inherited
        simp [Transform.Frame.replace, Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before) (right := after)
          (motive := fun localWire' =>
            (Transform.Frame.replace outer before after [] arguments
              ).targetKeep (Var.appendRight outer localWire') =
                Var.appendRight outer localWire')
        · intro beforeSignature beforeWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep]
          exact congrArg (fun wire => Var.appendRight outer
            (Var.appendRight before wire))
              (supportParallelAppendRightNil afterWire)
    retained := by
      intro signature wire
      apply Var.appendCases (left := outer)
        (right := before ++ after)
        (motive := fun wire =>
          ((Transform.Frame.replace outer before
              (.rel arguments :: after) [] arguments).sourceKeep
            ((Transform.Frame.replace outer before after [] arguments
              ).sourceKeep wire)) =
            (Content.Parallel.rootFrame outer before after arguments
              ).targetKeep wire)
      · intro inheritedSignature inherited
        simp [Content.Parallel.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep]
      · intro localSignature localWire
        apply Var.appendCases (left := before) (right := after)
          (motive := fun wire =>
            ((Transform.Frame.replace outer before
                (.rel arguments :: after) [] arguments).sourceKeep
              ((Transform.Frame.replace outer before after [] arguments
                ).sourceKeep (Var.appendRight outer wire))) =
              (Content.Parallel.rootFrame outer before after arguments
                ).targetKeep (Var.appendRight outer wire))
        · intro beforeSignature beforeWire
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
        · intro afterSignature afterWire
          simp [Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
          change Var.appendRight outer
              (Var.appendRight before (.there (.there afterWire))) =
            Var.appendRight outer
              (Var.appendRight before (.there (.there afterWire)))
          rfl
    first := by
      rfl
    second := by
      simp [Content.Parallel.secondHead, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep,
        Transform.Frame.insertedHead]
      change Var.appendRight outer (Var.appendRight before (.there .here)) =
        Var.appendRight outer (Var.appendRight before (.there .here))
      rfl
  }

/-- Canonicality and retained-wire incidence facts transported by one factor
endpoint.  The incidence algebra remains `SupportParallelIncidenceScope`; this
record only keeps the exact fields consumed by the owning theorem together. -/
structure SupportParallelRetainedValidity
    {common sourceWires targetWires : List Sig}
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (source : Region sourceWires) (target : Region targetWires) : Prop where
  canonical : source.Canonical → target.Canonical
  retained : ∀ {signature} (wire : Var common signature),
    SupportParallelIncidenceScope
      (source.incidencePaths (sourceKeep wire).index.val)
      (target.incidencePaths (targetKeep wire).index.val)

/-- A factor endpoint that additionally transports the active selected wire. -/
structure SupportParallelSelectedValidity
    {arguments common sourceWires targetWires : List Sig}
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (sourceSelected : Var sourceWires (.rel arguments))
    (targetSelected : Var targetWires (.rel arguments))
    (source : Region sourceWires) (target : Region targetWires) : Prop
    extends SupportParallelRetainedValidity sourceKeep targetKeep source target where
  selected : SupportParallelIncidenceScope
    (source.incidencePaths sourceSelected.index.val)
    (target.incidencePaths targetSelected.index.val)

/-- The Parallel edit endpoint transports retained wires and sends the one
selected source wire to each of the two split heads. -/
structure SupportParallelSplitValidity
    {arguments common sourceWires targetWires : List Sig}
    (frame : Transform.Frame arguments common sourceWires targetWires)
    (data : (Content.Parallel.operation arguments).Data frame)
    (source : Region sourceWires) (target : Region targetWires) : Prop
    extends SupportParallelRetainedValidity frame.sourceKeep frame.targetKeep
      source target where
  first : SupportParallelIncidenceScope
    (source.incidencePaths frame.selected.index.val)
    (target.incidencePaths data.1.index.val)
  second : SupportParallelIncidenceScope
    (source.incidencePaths frame.selected.index.val)
    (target.incidencePaths data.2.index.val)

theorem SupportParallelFrames.firstFresh
    {frame : Transform.Frame arguments common sourceWires splitWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {middleWires : List Sig}
    (frames : SupportParallelFrames (middleWires := middleWires) frame data)
    (headInvariant : Transform.RetainedIndexInvariant frames.head)
    (wire : Var common signature) :
    data.1.index.val ≠ (frame.targetKeep wire).index.val := by
  rw [← frames.first, ← frames.retained wire]
  exact headInvariant.selectedFresh (frames.tail.sourceKeep wire)

theorem SupportParallelFrames.secondFresh
    {frame : Transform.Frame arguments common sourceWires splitWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {middleWires : List Sig}
    (frames : SupportParallelFrames (middleWires := middleWires) frame data)
    (headInvariant : Transform.RetainedIndexInvariant frames.head)
    (tailInvariant : Transform.RetainedIndexInvariant frames.tail)
    (wire : Var common signature) :
    data.2.index.val ≠ (frame.targetKeep wire).index.val := by
  intro equality
  rw [← frames.second, ← frames.retained wire] at equality
  have targetEquality := (headInvariant.reflects
    frames.tail.selected (frames.tail.sourceKeep wire)).mp equality
  rw [frames.headTarget, frames.headTarget] at targetEquality
  exact tailInvariant.selectedFresh wire targetEquality

theorem SupportParallelFrames.headsDistinct
    {frame : Transform.Frame arguments common sourceWires splitWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {middleWires : List Sig}
    (frames : SupportParallelFrames (middleWires := middleWires) frame data)
    (headInvariant : Transform.RetainedIndexInvariant frames.head) :
    data.1.index.val ≠ data.2.index.val := by
  rw [← frames.first, ← frames.second]
  exact headInvariant.selectedFresh frames.tail.selected

theorem SupportParallelRetainedValidity.conjoin
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : SupportParallelRetainedValidity sourceKeep targetKeep
      sourceFirst targetFirst)
    (second : SupportParallelRetainedValidity sourceKeep targetKeep
      sourceSecond targetSecond) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      (sourceFirst.conjoin sourceSecond) (targetFirst.conjoin targetSecond) :=
  {
    canonical := fun sourceCanonical => by
      have split := (Region.Canonical.conjoin_iff _ _).mp sourceCanonical
      exact (Region.Canonical.conjoin_iff _ _).mpr
        ⟨first.canonical split.1, second.canonical split.2⟩
    retained := fun wire => SupportParallelIncidenceScope.conjoin
      (sourceKeep wire) (targetKeep wire) (first.retained wire)
        (second.retained wire)
  }

theorem SupportParallelSelectedValidity.conjoin
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceSelected : Var sourceWires (.rel arguments)}
    {targetSelected : Var targetWires (.rel arguments)}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected sourceFirst targetFirst)
    (second : SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected sourceSecond targetSecond) :
    SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected (sourceFirst.conjoin sourceSecond)
        (targetFirst.conjoin targetSecond) :=
  {
    toSupportParallelRetainedValidity := first.1.conjoin second.1
    selected := SupportParallelIncidenceScope.conjoin sourceSelected
      targetSelected first.selected second.selected
  }

theorem SupportParallelSplitValidity.conjoin
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {sourceFirst sourceSecond : Region sourceWires}
    {targetFirst targetSecond : Region targetWires}
    (first : SupportParallelSplitValidity frame data sourceFirst targetFirst)
    (second : SupportParallelSplitValidity frame data sourceSecond targetSecond) :
    SupportParallelSplitValidity frame data
      (sourceFirst.conjoin sourceSecond) (targetFirst.conjoin targetSecond) :=
  {
    toSupportParallelRetainedValidity := first.1.conjoin second.1
    first := SupportParallelIncidenceScope.conjoin frame.selected data.1
      first.first second.first
    second := SupportParallelIncidenceScope.conjoin frame.selected data.2
      first.second second.second
  }

theorem SupportParallelRetainedValidity.cut
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {source : Region sourceWires} {target : Region targetWires}
    (validity : SupportParallelRetainedValidity sourceKeep targetKeep
      source target) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      (Region.singleton (.cut source)) (Region.singleton (.cut target)) :=
  {
    canonical := fun sourceCanonical =>
      (Region.singleton_cut_canonical_iff target).mpr
        (validity.canonical
          ((Region.singleton_cut_canonical_iff source).mp sourceCanonical))
    retained := fun wire => SupportParallelIncidenceScope.cut
      (sourceKeep wire) (targetKeep wire) (validity.retained wire)
  }

theorem SupportParallelSelectedValidity.cut
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceSelected : Var sourceWires (.rel arguments)}
    {targetSelected : Var targetWires (.rel arguments)}
    {source : Region sourceWires} {target : Region targetWires}
    (validity : SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected source target) :
    SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected (Region.singleton (.cut source))
        (Region.singleton (.cut target)) :=
  {
    toSupportParallelRetainedValidity := validity.1.cut
    selected := SupportParallelIncidenceScope.cut sourceSelected
      targetSelected validity.selected
  }

theorem SupportParallelSplitValidity.cut
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {source : Region sourceWires} {target : Region targetWires}
    (validity : SupportParallelSplitValidity frame data source target) :
    SupportParallelSplitValidity frame data
      (Region.singleton (.cut source)) (Region.singleton (.cut target)) :=
  {
    toSupportParallelRetainedValidity := validity.1.cut
    first := SupportParallelIncidenceScope.cut frame.selected data.1
      validity.first
    second := SupportParallelIncidenceScope.cut frame.selected data.2
      validity.second
  }

theorem SupportParallelRetainedValidity.iso
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (validity : SupportParallelRetainedValidity sourceKeep targetKeep
      sourceAfter targetBefore) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      sourceBefore targetAfter :=
  {
    canonical := fun canonical =>
      targetIso.canonical_iff.mp
        (validity.canonical (sourceIso.canonical_iff.mp canonical))
    retained := fun wire => SupportParallelIncidenceScope.iso
      sourceIso targetIso (sourceKeep wire) (targetKeep wire)
        (validity.retained wire)
  }

theorem SupportParallelSelectedValidity.iso
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceSelected : Var sourceWires (.rel arguments)}
    {targetSelected : Var targetWires (.rel arguments)}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (validity : SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected sourceAfter targetBefore) :
    SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected sourceBefore targetAfter :=
  {
    toSupportParallelRetainedValidity := validity.1.iso sourceIso targetIso
    selected := SupportParallelIncidenceScope.iso sourceIso targetIso
      sourceSelected targetSelected validity.selected
  }

theorem SupportParallelSplitValidity.iso
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    {sourceBefore sourceAfter : Region sourceWires}
    {targetBefore targetAfter : Region targetWires}
    (sourceIso : RegionIso (WireEquiv.refl sourceWires)
      sourceBefore sourceAfter)
    (targetIso : RegionIso (WireEquiv.refl targetWires)
      targetBefore targetAfter)
    (validity : SupportParallelSplitValidity frame data sourceAfter targetBefore) :
    SupportParallelSplitValidity frame data sourceBefore targetAfter :=
  {
    toSupportParallelRetainedValidity := validity.1.iso sourceIso targetIso
    first := SupportParallelIncidenceScope.iso sourceIso targetIso
      frame.selected data.1 validity.first
    second := SupportParallelIncidenceScope.iso sourceIso targetIso
      frame.selected data.2 validity.second
  }

theorem SupportParallelRetainedValidity.adjoin
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (validity : SupportParallelRetainedValidity
      (sourceKeep.appendRight locals) (targetKeep.appendRight locals)
      source target) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil target) := by
  constructor
  · intro sourceCanonical
    have sourceMaterialCanonical :=
      Region.Canonical.material_of_adjoinAt locals .nil source sourceCanonical
    apply Region.Canonical.adjoinAt_of_material_roots locals .nil target
      True.intro (validity.canonical sourceMaterialCanonical)
    intro localIndex
    let localWire : Var (common ++ locals) (locals.get localIndex) :=
      Var.appendRight common (Var.ofIndex localIndex)
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
        sourceCanonical localIndex
    have sourceRoot' : RegionPath.RootedTwo
        (source.incidencePaths
          ((sourceKeep.appendRight locals) localWire).index.val) := by
      simpa [localWire, WireRenaming.appendRight] using sourceRoot
    have targetRoot := (validity.retained localWire).rooted sourceRoot'
    simpa [localWire, WireRenaming.appendRight] using targetRoot
  · intro signature wire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      ((sourceKeep wire).appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      ((targetKeep wire).appendLeft locals)
    rw [show (sourceKeep wire).index.val =
        ((sourceKeep wire).appendLeft locals).index.val by simp,
      sourcePaths,
      show (targetKeep wire).index.val =
        ((targetKeep wire).appendLeft locals).index.val by simp,
      targetPaths]
    simpa [WireRenaming.appendRight] using
      validity.retained (wire.appendLeft locals)

theorem SupportParallelSelectedValidity.adjoin
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceSelected : Var sourceWires (.rel arguments)}
    {targetSelected : Var targetWires (.rel arguments)}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (validity : SupportParallelSelectedValidity
      (sourceKeep.appendRight locals) (targetKeep.appendRight locals)
      (sourceSelected.appendLeft locals) (targetSelected.appendLeft locals)
      source target) :
    SupportParallelSelectedValidity sourceKeep targetKeep sourceSelected
      targetSelected (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil target) := by
  constructor
  · exact validity.1.adjoin locals
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (sourceSelected.appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      (targetSelected.appendLeft locals)
    rw [show sourceSelected.index.val =
        (sourceSelected.appendLeft locals).index.val by simp,
      sourcePaths,
      show targetSelected.index.val =
        (targetSelected.appendLeft locals).index.val by simp,
      targetPaths]
    exact validity.selected

theorem SupportParallelSplitValidity.adjoin
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : (Content.Parallel.operation arguments).Data frame}
    (locals : List Sig)
    {source : Region (sourceWires ++ locals)}
    {target : Region (targetWires ++ locals)}
    (validity : SupportParallelSplitValidity (frame.append locals)
      ((Content.Parallel.operation arguments).appendData frame data locals)
      source target) :
    SupportParallelSplitValidity frame data
      (Region.adjoinAt locals .nil source)
      (Region.adjoinAt locals .nil target) := by
  constructor
  · exact validity.1.adjoin locals
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (frame.selected.appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      (data.1.appendLeft locals)
    rw [show frame.selected.index.val =
        (frame.selected.appendLeft locals).index.val by simp,
      sourcePaths,
      show data.1.index.val = (data.1.appendLeft locals).index.val by simp,
      targetPaths]
    simpa [Content.Parallel.operation, Transform.Frame.append] using
      validity.first
  · have sourcePaths := Region.incidencePaths_adjoinAt_nil source
      (frame.selected.appendLeft locals)
    have targetPaths := Region.incidencePaths_adjoinAt_nil target
      (data.2.appendLeft locals)
    rw [show frame.selected.index.val =
        (frame.selected.appendLeft locals).index.val by simp,
      sourcePaths,
      show data.2.index.val = (data.2.appendLeft locals).index.val by simp,
      targetPaths]
    simpa [Content.Parallel.operation, Transform.Frame.append] using
      validity.second

theorem supportParallelRegionLift
    {wires common sourceWires splitWires middleWires locals : List Sig}
    {frame : Transform.Frame wires common sourceWires splitWires}
    {data : (Content.Parallel.operation wires).Data frame}
    (frames : SupportParallelFrames (middleWires := middleWires) frame data)
    {items : ItemSeq (sourceWires ++ locals)}
    {splitItems : ItemSeq (splitWires ++ locals)}
    {childTailItems : ItemSeq (middleWires ++ locals)}
    {childHeadResult : Region (middleWires ++ locals)}
    {itemResult childTailResult : Region (common ++ locals)}
    (splitValidity : SupportParallelSplitValidity (frame.append locals)
      ((Content.Parallel.operation wires).appendData frame data locals)
      (Region.ofItems items) (Region.ofItems splitItems))
    (sourceTailValidity : SupportParallelSelectedValidity
      (frame.sourceKeep.appendRight locals)
      (frames.tail.sourceKeep.appendRight locals)
      (frame.selected.appendLeft locals)
      (frames.tail.selected.appendLeft locals)
      (Region.ofItems items) (Region.ofItems childTailItems))
    (tailHeadValidity : SupportParallelSelectedValidity
      (frames.tail.sourceKeep.appendRight locals)
      (frames.tail.sourceKeep.appendRight locals)
      (frames.tail.selected.appendLeft locals)
      (frames.tail.selected.appendLeft locals)
      (Region.ofItems childTailItems) childHeadResult)
    (resultValidity : SupportParallelRetainedValidity
      ((WireEquiv.refl common).toRenaming.appendRight locals)
      ((WireEquiv.refl common).toRenaming.appendRight locals)
      itemResult childTailResult) :
    SupportParallelSplitValidity frame data (.mk locals items)
        (.mk locals splitItems) ∧
      SupportParallelSelectedValidity frame.sourceKeep frames.tail.sourceKeep
        frame.selected frames.tail.selected (.mk locals items)
          (.mk locals childTailItems) ∧
      SupportParallelSelectedValidity frames.tail.sourceKeep
        frames.tail.sourceKeep frames.tail.selected frames.tail.selected
        (.mk locals childTailItems)
          (Region.adjoinAt locals .nil childHeadResult) ∧
      SupportParallelRetainedValidity (WireEquiv.refl common).toRenaming
        (WireEquiv.refl common).toRenaming
        (Region.adjoinAt locals .nil itemResult)
        (Region.adjoinAt locals .nil childTailResult) := by
  let sourceIso := RegionIso.adjoinAtOfItems locals items
  let splitIso' := RegionIso.adjoinAtOfItems locals splitItems
  let tailIso := RegionIso.adjoinAtOfItems locals childTailItems
  exact ⟨
    (splitValidity.adjoin locals).iso sourceIso.symm splitIso',
    (sourceTailValidity.adjoin locals).iso sourceIso.symm tailIso,
    (tailHeadValidity.adjoin locals).iso tailIso.symm (RegionIso.refl _),
    resultValidity.adjoin locals
  ⟩

theorem supportParallelAtomRetainedValidity
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (head : Var common (.rel arguments)) (ports : Vars common arguments) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      (Region.singleton (.atom (sourceKeep head)
        (ports.map fun wire => sourceKeep wire)))
      (Region.singleton (.atom (targetKeep head)
        (ports.map fun wire => targetKeep wire))) := by
  constructor
  · intro _
    exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
  · intro signature wire
    have headEq := reflects head wire
    have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
      sourceKeep targetKeep reflects wire
    have pathsEq :
        (Region.singleton (.atom (sourceKeep head)
          (ports.map fun port => sourceKeep port))).incidencePaths
            (sourceKeep wire).index.val =
        (Region.singleton (.atom (targetKeep head)
          (ports.map fun port => targetKeep port))).incidencePaths
            (targetKeep wire).index.val := by
      simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
        ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
        Item.incidencePaths, List.append_nil, Var.index_appendLeft,
        Vars.countIndex_map_appendLeft_nil]
      simp only [headEq, portsEq]
    rw [pathsEq]
    exact SupportParallelIncidenceScope.refl _

theorem supportParallelIdentityRetainedValidity
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var common signature) :
    SupportParallelRetainedValidity sourceKeep targetKeep
      (Region.singleton (.identity signature arity
        (fun index => sourceKeep (ports index))))
      (Region.singleton (.identity signature arity
        (fun index => targetKeep (ports index)))) := by
  constructor
  · intro _
    exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
  · intro wireSignature wire
    have portsEq := Transform.countPorts_map_eq_of_reflection arity ports
      sourceKeep targetKeep reflects wire
    simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
      ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
      Item.incidencePaths, List.append_nil, Var.index_appendLeft]
    rw [portsEq]
    exact SupportParallelIncidenceScope.refl _

theorem supportParallelAtomFreshScope
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (sourceSelected : Var sourceWires (.rel selectedArguments))
    (targetSelected : Var targetWires (.rel selectedArguments))
    (sourceFresh : ∀ {signature} (wire : Var common signature),
      sourceSelected.index.val ≠ (sourceKeep wire).index.val)
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetSelected.index.val ≠ (targetKeep wire).index.val)
    (head : Var common (.rel arguments)) (ports : Vars common arguments) :
    SupportParallelIncidenceScope
      ((Region.singleton (.atom (sourceKeep head)
        (ports.map fun wire => sourceKeep wire))).incidencePaths
          sourceSelected.index.val)
      ((Region.singleton (.atom (targetKeep head)
        (ports.map fun wire => targetKeep wire))).incidencePaths
          targetSelected.index.val) := by
  have sourcePortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
    sourceKeep sourceSelected.index.val
      (fun wire => Ne.symm (sourceFresh wire))
  have targetPortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
    targetKeep targetSelected.index.val
      (fun wire => Ne.symm (targetFresh wire))
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, Var.index_appendLeft,
    Vars.countIndex_map_appendLeft_nil, sourcePortsZero, targetPortsZero,
    Nat.add_zero]
  rw [if_neg (Ne.symm (sourceFresh head)),
    if_neg (Ne.symm (targetFresh head))]
  exact SupportParallelIncidenceScope.refl []

theorem supportParallelIdentityFreshScope
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (sourceSelected : Var sourceWires (.rel selectedArguments))
    (targetSelected : Var targetWires (.rel selectedArguments))
    (sourceFresh : ∀ {signature} (wire : Var common signature),
      sourceSelected.index.val ≠ (sourceKeep wire).index.val)
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetSelected.index.val ≠ (targetKeep wire).index.val)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var common signature) :
    SupportParallelIncidenceScope
      ((Region.singleton (.identity signature arity
        (fun index => sourceKeep (ports index)))).incidencePaths
          sourceSelected.index.val)
      ((Region.singleton (.identity signature arity
        (fun index => targetKeep (ports index)))).incidencePaths
          targetSelected.index.val) := by
  have sourcePortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
    sourceKeep sourceSelected.index.val
      (fun wire => Ne.symm (sourceFresh wire))
  have targetPortsZero := countPorts_map_eq_zero_of_no_preimage arity ports
    targetKeep targetSelected.index.val
      (fun wire => Ne.symm (targetFresh wire))
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, Var.index_appendLeft]
  rw [sourcePortsZero, targetPortsZero]
  exact SupportParallelIncidenceScope.refl []

theorem supportParallelSelectedAtomToHeadScope
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (sourceSelected : Var sourceWires (.rel arguments))
    (targetHead : Var targetWires (.rel arguments))
    (sourceFresh : ∀ {signature} (wire : Var common signature),
      sourceSelected.index.val ≠ (sourceKeep wire).index.val)
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetHead.index.val ≠ (targetKeep wire).index.val)
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (ports : Vars common arguments) (wire : Var common signature) :
    SupportParallelIncidenceScope
      ((Region.singleton (.atom sourceSelected
        (ports.map fun port => sourceKeep port))).incidencePaths
          (sourceKeep wire).index.val)
      ((Region.singleton (.atom targetHead
        (ports.map fun port => targetKeep port))).incidencePaths
          (targetKeep wire).index.val) := by
  have portsEq := Transform.Vars.countIndex_map_eq_of_reflection ports
    sourceKeep targetKeep reflects wire
  have sourceHead := sourceFresh wire
  have targetHeadNe := targetFresh wire
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, Var.index_appendLeft,
    Vars.countIndex_map_appendLeft_nil]
  simp only [sourceHead, targetHeadNe, portsEq]
  exact SupportParallelIncidenceScope.refl _

theorem supportParallelSelectedAtomSplitValidity
    {frame : Transform.Frame arguments common sourceWires targetWires}
    (data : (Content.Parallel.operation arguments).Data frame)
    (invariant : Transform.RetainedIndexInvariant frame)
    (firstFresh : ∀ {signature} (wire : Var common signature),
      data.1.index.val ≠ (frame.targetKeep wire).index.val)
    (secondFresh : ∀ {signature} (wire : Var common signature),
      data.2.index.val ≠ (frame.targetKeep wire).index.val)
    (headsDistinct : data.1.index.val ≠ data.2.index.val)
    (ports : Vars common arguments) :
    SupportParallelSplitValidity frame data
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((Region.singleton (.atom data.1
        (ports.map fun wire => frame.targetKeep wire))).conjoin
       (Region.singleton (.atom data.2
        (ports.map fun wire => frame.targetKeep wire)))) := by
  let sourceRegion := Region.singleton (.atom frame.selected
    (ports.map fun wire => frame.sourceKeep wire))
  let firstRegion := Region.singleton (.atom data.1
    (ports.map fun wire => frame.targetKeep wire))
  let secondRegion := Region.singleton (.atom data.2
    (ports.map fun wire => frame.targetKeep wire))
  have firstRetained : ∀ {signature} (wire : Var common signature),
      SupportParallelIncidenceScope
        (sourceRegion.incidencePaths (frame.sourceKeep wire).index.val)
        (firstRegion.incidencePaths (frame.targetKeep wire).index.val) := by
    intro signature wire
    exact supportParallelSelectedAtomToHeadScope frame.selected data.1
      invariant.selectedFresh firstFresh invariant.reflects ports wire
  have secondRetained : ∀ {signature} (wire : Var common signature),
      SupportParallelIncidenceScope
        (sourceRegion.incidencePaths (frame.sourceKeep wire).index.val)
        (secondRegion.incidencePaths (frame.targetKeep wire).index.val) := by
    intro signature wire
    exact supportParallelSelectedAtomToHeadScope frame.selected data.2
      invariant.selectedFresh secondFresh invariant.reflects ports wire
  refine {
    canonical := ?_
    retained := ?_
    first := ?_
    second := ?_
  }
  · intro _
    apply (Region.Canonical.conjoin_iff firstRegion secondRegion).mpr
    constructor <;>
      exact ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
  · intro signature wire
    constructor
    · constructor
      · intro sourceNonempty
        rw [Region.incidencePaths_conjoin]
        exact List.append_ne_nil_of_left_ne_nil
          ((firstRetained wire).nonempty.mp sourceNonempty) _
      · intro targetNonempty
        intro sourceEmpty
        have firstEmpty : firstRegion.incidencePaths
            (frame.targetKeep wire).index.val = [] := by
          apply Classical.byContradiction
          intro nonempty
          exact ((firstRetained wire).nonempty.mpr nonempty) sourceEmpty
        have secondEmpty : secondRegion.incidencePaths
            (frame.targetKeep wire).index.val = [] := by
          apply Classical.byContradiction
          intro nonempty
          exact ((secondRetained wire).nonempty.mpr nonempty) sourceEmpty
        rw [Region.incidencePaths_conjoin, firstEmpty, secondEmpty,
          List.map_nil, List.nil_append] at targetNonempty
        exact targetNonempty rfl
    · intro sourceRooted
      rw [Region.incidencePaths_conjoin]
      exact RegionPath.RootedTwo.of_sublist
        (List.sublist_append_left _ _)
        ((firstRetained wire).rooted sourceRooted)
  · have sourcePortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
      frame.sourceKeep frame.selected.index.val
        (fun wire => Ne.symm (invariant.selectedFresh wire))
    have firstPortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
      frame.targetKeep data.1.index.val (fun wire => Ne.symm (firstFresh wire))
    have secondAtFirst : data.2.index.val ≠ data.1.index.val :=
      Ne.symm headsDistinct
    simp [Region.singleton, Region.incidencePaths_ofItems,
      Region.incidencePaths_conjoin,
      ItemSeq.incidencePaths, Item.incidencePaths, sourcePortsZero,
      firstPortsZero, secondAtFirst]
    exact SupportParallelIncidenceScope.refl [[]]
  · have sourcePortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
      frame.sourceKeep frame.selected.index.val
        (fun wire => Ne.symm (invariant.selectedFresh wire))
    have secondPortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
      frame.targetKeep data.2.index.val
        (fun wire => Ne.symm (secondFresh wire))
    simp [Region.singleton, Region.incidencePaths_ofItems,
      Region.incidencePaths_conjoin,
      ItemSeq.incidencePaths, Item.incidencePaths, sourcePortsZero,
      secondPortsZero, headsDistinct]
    exact SupportParallelIncidenceScope.refl [[]]

theorem supportParallelRenamedItemCoveredByApplication
    (item : Item arguments) (application : Vars common arguments)
    (selected : Var common (.rel arguments))
    (wire : Var common signature)
    (hostNonempty :
      (Region.singleton (item.renameWires
        (EqualityNormalization.formalSubstitution application))).incidencePaths
          wire.index.val ≠ []) :
    (Region.singleton (.atom selected application)).incidencePaths
      wire.index.val ≠ [] := by
  by_cases countZero : application.countIndex wire.index.val = 0
  · have noPreimage : ∀ {sourceSignature}
        (sourceWire : Var arguments sourceSignature),
        (EqualityNormalization.formalSubstitution application sourceWire
          ).index.val ≠ wire.index.val :=
      fun sourceWire =>
        EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
          application wire countZero sourceWire
    have hostEmpty :
        (Region.singleton (item.renameWires
          (EqualityNormalization.formalSubstitution application))).incidencePaths
            wire.index.val = [] := by
      change (Region.ofItems (.cons (item.renameWires
        (EqualityNormalization.formalSubstitution application)) .nil)
          ).incidencePaths wire.index.val = []
      rw [Region.incidencePaths_ofItems]
      change ((ItemSeq.cons item .nil).renameWires
        (EqualityNormalization.formalSubstitution application)
          ).incidencePaths wire.index.val 0 = []
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · exact wire.index.isLt
      · exact noPreimage
    exact False.elim (hostNonempty hostEmpty)
  · change (Region.ofItems (.cons (.atom selected application) .nil)
      ).incidencePaths wire.index.val ≠ []
    rw [Region.incidencePaths_ofItems]
    simp only [ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil]
    intro empty
    have lengthZero := congrArg List.length empty
    simp only [List.length_replicate, List.length_nil] at lengthZero
    exact countZero (by omega)

theorem SupportParallelIncidenceScope.hostLeft
    (source : Region sourceWires) (host target : Region targetWires)
    (sourceWire : Var sourceWires sourceSignature)
    (targetWire : Var targetWires targetSignature)
    (scope : SupportParallelIncidenceScope
      (source.incidencePaths sourceWire.index.val)
      (target.incidencePaths targetWire.index.val))
    (hostCovered : host.incidencePaths targetWire.index.val ≠ [] →
      target.incidencePaths targetWire.index.val ≠ []) :
    SupportParallelIncidenceScope
      (source.incidencePaths sourceWire.index.val)
      ((host.conjoin target).incidencePaths targetWire.index.val) := by
  constructor
  · constructor
    · intro sourceNonempty
      have targetNonempty := scope.nonempty.mp sourceNonempty
      rw [Region.incidencePaths_conjoin]
      intro combinedEmpty
      have targetEmpty := (List.append_eq_nil_iff.mp combinedEmpty).2
      exact targetNonempty ((List.map_eq_nil_iff).mp targetEmpty)
    · intro combinedNonempty
      apply scope.nonempty.mpr
      rw [Region.incidencePaths_conjoin] at combinedNonempty
      by_cases targetEmpty : target.incidencePaths targetWire.index.val = []
      · have hostNonempty : host.incidencePaths targetWire.index.val ≠ [] := by
          intro hostEmpty
          exact combinedNonempty (by simp [hostEmpty, targetEmpty])
        exact hostCovered hostNonempty
      · exact targetEmpty
  · intro sourceRooted
    have targetRooted := scope.rooted sourceRooted
    rw [Region.incidencePaths_conjoin]
    exact RegionPath.RootedTwo.of_sublist
      (List.sublist_append_right _ _)
      ((RegionPath.RootedTwo.map_shiftHead_iff host.items.length _).mpr
        targetRooted)

theorem SupportParallelSelectedValidity.hostLeft
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {sourceSelected : Var sourceWires (.rel arguments)}
    {targetSelected : Var targetWires (.rel arguments)}
    {source : Region sourceWires} {target host : Region targetWires}
    (base : SupportParallelSelectedValidity sourceKeep targetKeep
      sourceSelected targetSelected source target)
    (hostCanonical : host.Canonical)
    (hostCovered : ∀ {signature} (wire : Var targetWires signature),
      host.incidencePaths wire.index.val ≠ [] →
        target.incidencePaths wire.index.val ≠ []) :
    SupportParallelSelectedValidity sourceKeep targetKeep sourceSelected
      targetSelected source (host.conjoin target) :=
  {
    canonical := fun sourceCanonical =>
      (Region.Canonical.conjoin_iff host target).mpr
        ⟨hostCanonical, base.canonical sourceCanonical⟩
    retained := fun wire => SupportParallelIncidenceScope.hostLeft
      source host target (sourceKeep wire) (targetKeep wire)
        (base.retained wire) (hostCovered (targetKeep wire))
    selected := SupportParallelIncidenceScope.hostLeft
      source host target sourceSelected targetSelected base.selected
        (hostCovered targetSelected)
  }

theorem SupportParallelRetainedValidity.hostLeft
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    {source : Region sourceWires} {target host : Region targetWires}
    (base : SupportParallelRetainedValidity sourceKeep targetKeep source target)
    (hostCanonical : host.Canonical)
    (hostCovered : ∀ {signature} (wire : Var targetWires signature),
      host.incidencePaths wire.index.val ≠ [] →
        target.incidencePaths wire.index.val ≠ []) :
    SupportParallelRetainedValidity sourceKeep targetKeep source
      (host.conjoin target) :=
  {
    canonical := fun sourceCanonical =>
      (Region.Canonical.conjoin_iff host target).mpr
        ⟨hostCanonical, base.canonical sourceCanonical⟩
    retained := fun wire => SupportParallelIncidenceScope.hostLeft
      source host target (sourceKeep wire) (targetKeep wire)
        (base.retained wire) (hostCovered (targetKeep wire))
  }

theorem supportParallelSelectedAtomMappedValidity
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (sourceSelected : Var sourceWires (.rel arguments))
    (targetSelected : Var targetWires (.rel arguments))
    (sourceFresh : ∀ {signature} (wire : Var common signature),
      sourceSelected.index.val ≠ (sourceKeep wire).index.val)
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetSelected.index.val ≠ (targetKeep wire).index.val)
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (ports : Vars common arguments) :
    SupportParallelSelectedValidity sourceKeep targetKeep sourceSelected
      targetSelected
      (Region.singleton (.atom sourceSelected
        (ports.map fun wire => sourceKeep wire)))
      (Region.singleton (.atom targetSelected
        (ports.map fun wire => targetKeep wire))) := by
  refine {
    canonical := fun _ =>
      ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩
    retained := fun wire => supportParallelSelectedAtomToHeadScope
      sourceSelected targetSelected sourceFresh targetFresh reflects ports wire
    selected := ?_
  }
  have sourcePortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
    sourceKeep sourceSelected.index.val
      (fun wire => Ne.symm (sourceFresh wire))
  have targetPortsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
    targetKeep targetSelected.index.val
      (fun wire => Ne.symm (targetFresh wire))
  simp [Region.singleton, Region.incidencePaths_ofItems,
    ItemSeq.incidencePaths, Item.incidencePaths, sourcePortsZero,
    targetPortsZero]
  exact SupportParallelIncidenceScope.refl [[]]

theorem supportParallelSelectedSourceToTailValidity
    {sourceKeep : WireRenaming common sourceWires}
    {targetKeep : WireRenaming common targetWires}
    (sourceSelected : Var sourceWires (.rel arguments))
    (targetSelected : Var targetWires (.rel arguments))
    (sourceFresh : ∀ {signature} (wire : Var common signature),
      sourceSelected.index.val ≠ (sourceKeep wire).index.val)
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetSelected.index.val ≠ (targetKeep wire).index.val)
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (materialHead : Item arguments)
    (headCanonical : (Region.singleton materialHead).Canonical)
    (application : Vars common arguments) :
    let targetApplication := application.map fun wire => targetKeep wire
    let rawHead := materialHead.renameWires
      (EqualityNormalization.formalSubstitution targetApplication)
    SupportParallelSelectedValidity sourceKeep targetKeep sourceSelected
      targetSelected
      (Region.singleton (.atom sourceSelected
        (application.map fun wire => sourceKeep wire)))
      ((Region.singleton rawHead).conjoin
        (Region.singleton (.atom targetSelected targetApplication))) := by
  dsimp only
  let targetApplication := application.map fun wire => targetKeep wire
  let rawHead := materialHead.renameWires
    (EqualityNormalization.formalSubstitution targetApplication)
  let anchor := Region.singleton (.atom targetSelected targetApplication)
  have base := supportParallelSelectedAtomMappedValidity sourceSelected
    targetSelected sourceFresh targetFresh reflects application
  apply base.hostLeft
  · simpa only [Region.singleton_renameWires] using
      (Region.Canonical.renameWires_iff (Region.singleton materialHead)
        (EqualityNormalization.formalSubstitution targetApplication)).mpr
          headCanonical
  · intro signature wire hostNonempty
    exact supportParallelRenamedItemCoveredByApplication materialHead
      targetApplication targetSelected wire hostNonempty

theorem supportParallelSelectedResultToTailValidity
    (materialHead : Item arguments) (materialTail : ItemSeq arguments)
    (fullCanonical : (Region.ofItems (.cons materialHead materialTail)).Canonical)
    (headCanonical : (Region.singleton materialHead).Canonical)
    (tailCanonical : (Region.ofItems materialTail).Canonical)
    (application : Vars common arguments) :
    let fullPattern := Erasure.Exposure.supportPattern
      (Region.ofItems (.cons materialHead materialTail)) fullCanonical
    let tailPattern := Erasure.Exposure.supportPattern
      (Region.ofItems materialTail) tailCanonical
    let rawHead := materialHead.renameWires
      (EqualityNormalization.formalSubstitution application)
    SupportParallelRetainedValidity (WireEquiv.refl common).toRenaming
      (WireEquiv.refl common).toRenaming
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        fullPattern application)
      ((Region.singleton rawHead).conjoin
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          tailPattern application)) := by
  dsimp only
  let fullPattern := Erasure.Exposure.supportPattern
    (Region.ofItems (.cons materialHead materialTail)) fullCanonical
  let tailPattern := Erasure.Exposure.supportPattern
    (Region.ofItems materialTail) tailCanonical
  let rawHead := materialHead.renameWires
    (EqualityNormalization.formalSubstitution application)
  let fullInst := VisualProof.Rule.Comprehension.Instantiation.instantiate
    fullPattern application
  let tailInst := VisualProof.Rule.Comprehension.Instantiation.instantiate
    tailPattern application
  have base : SupportParallelRetainedValidity
      (WireEquiv.refl common).toRenaming
      (WireEquiv.refl common).toRenaming fullInst tailInst := by
    constructor
    · intro _
      exact VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        tailPattern application
    · intro signature wire
      constructor
      · rw [EqualityNormalization.instantiate_incidence_nonempty_iff,
          EqualityNormalization.instantiate_incidence_nonempty_iff]
      · intro rooted
        rw [EqualityNormalization.instantiate_rootedTwo_iff] at rooted ⊢
        exact rooted
  apply base.hostLeft
  · simpa only [Region.singleton_renameWires] using
      (Region.Canonical.renameWires_iff (Region.singleton materialHead)
        (EqualityNormalization.formalSubstitution application)).mpr
          headCanonical
  · intro signature wire hostNonempty
    have countNe : application.countIndex wire.index.val ≠ 0 := by
      intro countZero
      have noPreimage : ∀ {sourceSignature}
          (sourceWire : Var arguments sourceSignature),
          (EqualityNormalization.formalSubstitution application sourceWire
            ).index.val ≠ wire.index.val := fun sourceWire =>
        EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
          application wire countZero sourceWire
      have hostEmpty : (Region.singleton rawHead).incidencePaths
          wire.index.val = [] := by
        change (Region.ofItems (.cons (materialHead.renameWires
          (EqualityNormalization.formalSubstitution application)) .nil)
            ).incidencePaths wire.index.val = []
        rw [Region.incidencePaths_ofItems]
        change ((ItemSeq.cons materialHead .nil).renameWires
          (EqualityNormalization.formalSubstitution application)
            ).incidencePaths wire.index.val 0 = []
        apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
        · exact wire.index.isLt
        · exact noPreimage
      exact hostNonempty hostEmpty
    apply (EqualityNormalization.instantiate_incidence_nonempty_iff
      tailPattern application wire).mpr
    omega

theorem SupportParallelIncidenceScope.betweenAnchoredHosts
    (sourceHost targetHost anchor : Region wires)
    (wire : Var wires signature)
    (sourceCovered : sourceHost.incidencePaths wire.index.val ≠ [] →
      anchor.incidencePaths wire.index.val ≠ [])
    (targetCovered : targetHost.incidencePaths wire.index.val ≠ [] →
      anchor.incidencePaths wire.index.val ≠ [])
    (targetSupplied : anchor.incidencePaths wire.index.val ≠ [] →
      targetHost.incidencePaths wire.index.val ≠ []) :
    SupportParallelIncidenceScope
      ((sourceHost.conjoin anchor).incidencePaths wire.index.val)
      ((targetHost.conjoin anchor).incidencePaths wire.index.val) := by
  have sourceIff : (sourceHost.conjoin anchor).incidencePaths
        wire.index.val ≠ [] ↔ anchor.incidencePaths wire.index.val ≠ [] := by
    rw [Region.incidencePaths_conjoin]
    constructor
    · intro combinedNonempty
      by_cases anchorEmpty : anchor.incidencePaths wire.index.val = []
      · have hostNonempty : sourceHost.incidencePaths wire.index.val ≠ [] := by
          intro hostEmpty
          exact combinedNonempty (by simp [hostEmpty, anchorEmpty])
        exact False.elim ((sourceCovered hostNonempty) anchorEmpty)
      · exact anchorEmpty
    · intro anchorNonempty combinedEmpty
      exact anchorNonempty ((List.map_eq_nil_iff).mp
        (List.append_eq_nil_iff.mp combinedEmpty).2)
  have targetIff : (targetHost.conjoin anchor).incidencePaths
        wire.index.val ≠ [] ↔ anchor.incidencePaths wire.index.val ≠ [] := by
    rw [Region.incidencePaths_conjoin]
    constructor
    · intro combinedNonempty
      by_cases anchorEmpty : anchor.incidencePaths wire.index.val = []
      · have hostNonempty : targetHost.incidencePaths wire.index.val ≠ [] := by
          intro hostEmpty
          exact combinedNonempty (by simp [hostEmpty, anchorEmpty])
        exact False.elim ((targetCovered hostNonempty) anchorEmpty)
      · exact anchorEmpty
    · intro anchorNonempty combinedEmpty
      exact anchorNonempty ((List.map_eq_nil_iff).mp
        (List.append_eq_nil_iff.mp combinedEmpty).2)
  constructor
  · exact sourceIff.trans targetIff.symm
  · intro sourceRooted
    have anchorNonempty := sourceIff.mp sourceRooted.nonempty
    exact supportParallelRootedTwoConjoinOfBoth targetHost anchor wire
      (targetSupplied anchorNonempty) anchorNonempty

theorem supportParallelSelectedTailToHeadValidity
    {targetKeep : WireRenaming common targetWires}
    (targetSelected : Var targetWires (.rel arguments))
    (targetFresh : ∀ {signature} (wire : Var common signature),
      targetSelected.index.val ≠ (targetKeep wire).index.val)
    (materialHead : Item arguments)
    (headCanonical : (Region.singleton materialHead).Canonical)
    (application : Vars common arguments) :
    let targetApplication := application.map fun wire => targetKeep wire
    let rawHead := materialHead.renameWires
      (EqualityNormalization.formalSubstitution targetApplication)
    let headPattern := Erasure.Exposure.supportPattern
      (Region.singleton materialHead) headCanonical
    let anchor := Region.singleton (.atom targetSelected targetApplication)
    SupportParallelSelectedValidity targetKeep targetKeep targetSelected
      targetSelected ((Region.singleton rawHead).conjoin anchor)
      ((VisualProof.Rule.Comprehension.Instantiation.instantiate
        headPattern targetApplication).conjoin anchor) := by
  dsimp only
  let targetApplication := application.map fun wire => targetKeep wire
  let rawHead := materialHead.renameWires
    (EqualityNormalization.formalSubstitution targetApplication)
  let headPattern := Erasure.Exposure.supportPattern
    (Region.singleton materialHead) headCanonical
  let sourceHost := Region.singleton rawHead
  let targetHost := VisualProof.Rule.Comprehension.Instantiation.instantiate
    headPattern targetApplication
  let anchor := Region.singleton (.atom targetSelected targetApplication)
  refine {
    canonical := fun _ => (Region.Canonical.conjoin_iff targetHost anchor).mpr
      ⟨VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        headPattern targetApplication,
        ⟨fun index => Fin.elim0 index, ⟨True.intro, True.intro⟩⟩⟩
    retained := ?_
    selected := ?_
  }
  · intro signature wire
    let actualWire := targetKeep wire
    apply SupportParallelIncidenceScope.betweenAnchoredHosts
      sourceHost targetHost anchor actualWire
    · exact fun hostNonempty =>
        supportParallelRenamedItemCoveredByApplication materialHead
          targetApplication targetSelected actualWire hostNonempty
    · intro hostNonempty
      have positive :=
        (EqualityNormalization.instantiate_incidence_nonempty_iff
          headPattern targetApplication actualWire).mp hostNonempty
      change anchor.incidencePaths actualWire.index.val ≠ []
      change (Region.ofItems (.cons (.atom targetSelected targetApplication) .nil)
        ).incidencePaths actualWire.index.val ≠ []
      rw [Region.incidencePaths_ofItems]
      simp only [ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil]
      intro empty
      have lengthZero := congrArg List.length empty
      simp only [List.length_replicate, List.length_nil] at lengthZero
      have fresh := targetFresh wire
      omega
    · intro anchorNonempty
      apply (EqualityNormalization.instantiate_incidence_nonempty_iff
        headPattern targetApplication actualWire).mpr
      change 0 < targetApplication.countIndex actualWire.index.val
      change anchor.incidencePaths actualWire.index.val ≠ [] at anchorNonempty
      change (Region.ofItems (.cons (.atom targetSelected targetApplication) .nil)
        ).incidencePaths actualWire.index.val ≠ [] at anchorNonempty
      rw [Region.incidencePaths_ofItems] at anchorNonempty
      simp only [ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil]
        at anchorNonempty
      have fresh := targetFresh wire
      have fresh' : targetSelected.index.val ≠ actualWire.index.val := by
        simpa [actualWire] using fresh
      have countNe : targetApplication.countIndex actualWire.index.val ≠ 0 := by
        intro zero
        exact anchorNonempty (by simp [fresh', zero])
      omega
  · have rawEmpty : sourceHost.incidencePaths targetSelected.index.val = [] := by
      change (Region.singleton (materialHead.renameWires
        (EqualityNormalization.formalSubstitution targetApplication))
          ).incidencePaths targetSelected.index.val = []
      change (Region.ofItems (.cons (materialHead.renameWires
        (EqualityNormalization.formalSubstitution targetApplication)) .nil)
          ).incidencePaths targetSelected.index.val = []
      rw [Region.incidencePaths_ofItems]
      change ((ItemSeq.cons materialHead .nil).renameWires
        (EqualityNormalization.formalSubstitution targetApplication)
          ).incidencePaths targetSelected.index.val 0 = []
      apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
      · exact targetSelected.index.isLt
      · intro sourceSignature sourceWire
        have countZero := Vars.countIndex_map_eq_zero_of_no_preimage application
          targetKeep targetSelected.index.val
            (fun wire => Ne.symm (targetFresh wire))
        exact
          EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
            targetApplication targetSelected countZero sourceWire
    have instEmpty : targetHost.incidencePaths targetSelected.index.val = [] := by
      have countZero := Vars.countIndex_map_eq_zero_of_no_preimage application
        targetKeep targetSelected.index.val
          (fun wire => Ne.symm (targetFresh wire))
      apply List.eq_nil_of_length_eq_zero
      rw [EqualityNormalization.instantiate_incidencePaths_length]
      exact countZero
    exact SupportParallelIncidenceScope.conjoin targetSelected targetSelected
      (by rw [rawEmpty, instEmpty]
          exact SupportParallelIncidenceScope.refl [])
      (SupportParallelIncidenceScope.refl _)
/-- At one selected site, the support of the whole nonempty sequence is
hostedly equivalent to a retained presentation of the raw head conjoined with
the support of the tail. `HostedStrict.transPinned` supplies one shared
Vacuity support envelope for the two support-instantiation bridges. -/
theorem supportParallelSelectedResultHosted
    {wires common : List Sig}
    (materialHead : Item wires) (materialTail : ItemSeq wires)
    (fullCanonical : (Region.ofItems (.cons materialHead materialTail)).Canonical)
    (tailCanonical : (Region.ofItems materialTail).Canonical)
    (application : Vars common wires) :
    HostedStrict
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.ofItems (.cons materialHead materialTail)) fullCanonical)
        application)
      ((retainedItemPresentation
          (materialHead.renameWires
            (EqualityNormalization.formalSubstitution application))).conjoin
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern
            (Region.ofItems materialTail) tailCanonical) application)) := by
  let fullMaterial := Region.ofItems (.cons materialHead materialTail)
  let tailMaterial := Region.ofItems materialTail
  let substitution := EqualityNormalization.formalSubstitution application
  let rawHead := materialHead.renameWires substitution
  let rawTail := tailMaterial.renameWires substitution
  let rawFull := fullMaterial.renameWires substitution
  let fullHosted := supportInstantiationHosted fullMaterial fullCanonical
    application
  let tailHosted := supportInstantiationHosted tailMaterial tailCanonical
    application
  let childToRaw := HostedStrict.conjoin
    (retainedItemPresentation rawHead)
    (VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern tailMaterial tailCanonical) application)
    (Region.singleton rawHead) rawTail
    (HostedStrict.ofIso (retainedItemPresentationIso rawHead)) tailHosted
  let rawPresentation : RegionIso (WireEquiv.refl common)
      ((Region.singleton rawHead).conjoin rawTail) rawFull := by
    apply RegionIso.ofEq
    have equality := congrArg (fun region => region.renameWires substitution)
      (Region.singleton_conjoin_ofItems materialHead materialTail)
    simpa only [rawHead, rawTail, rawFull, fullMaterial, tailMaterial,
      Region.renameWires_conjoin, Region.singleton_renameWires] using equality
  have presentedChildToRaw :=
    HostedStrict.iso (RegionIso.refl _) rawPresentation childToRaw
  exact HostedStrict.transPinned fullHosted presentedChildToRaw.symm
    ((Region.Canonical.renameWires_iff fullMaterial substitution).mpr
      fullCanonical)

/-- The first child support at a selected site is hostedly equivalent to the
raw head followed by the retained second application. -/
theorem supportParallelSelectedHeadHosted
    {wires middle : List Sig}
    (materialHead : Item wires)
    (headCanonical : (Region.singleton materialHead).Canonical)
    (application : Vars middle wires)
    (second : Var middle (.rel wires)) :
    let rawHead := materialHead.renameWires
      (EqualityNormalization.formalSubstitution application)
    let secondItem := Item.atom second application
    HostedStrict
      ((VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton materialHead) headCanonical) application).conjoin
        (Region.singleton secondItem))
      (Region.ofItems (.cons rawHead (.cons secondItem .nil))) := by
  dsimp only
  let rawHead := materialHead.renameWires
    (EqualityNormalization.formalSubstitution application)
  let secondItem := Item.atom second application
  let headHosted := supportInstantiationHosted
    (Region.singleton materialHead) headCanonical application
  have headHosted' : HostedStrict
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton materialHead) headCanonical) application)
      (Region.singleton rawHead) := by
    simpa only [rawHead, Region.singleton_renameWires] using headHosted
  let combined := HostedStrict.conjoin
    (VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern
        (Region.singleton materialHead) headCanonical) application)
    (Region.singleton secondItem) (Region.singleton rawHead)
    (Region.singleton secondItem) headHosted' (HostedStrict.refl _)
  apply HostedStrict.iso (RegionIso.refl _) (RegionIso.ofEq ?_) combined
  exact Region.singleton_conjoin_ofItems rawHead (.cons secondItem .nil)

set_option maxRecDepth 2000 in
mutual
  /-- One fused traversal under a region binder constructs the Parallel edit
  and both sequential child instantiations. -/
  theorem supportParallelRegionFactor
      {wires common sourceWires splitWires middleWires : List Sig}
      (materialHead : Item wires) (materialTail : ItemSeq wires)
      (fullCanonical :
        (Region.ofItems (.cons materialHead materialTail)).Canonical)
      (headCanonical : (Region.singleton materialHead).Canonical)
      (tailCanonical : (Region.ofItems materialTail).Canonical)
      {frame : Transform.Frame wires common sourceWires splitWires}
      {data : (Content.Parallel.operation wires).Data frame}
      (frames : SupportParallelFrames (middleWires := middleWires) frame data)
      (frameInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.RetainedIndexInvariant frames.head)
      (tailInvariant : Transform.RetainedIndexInvariant frames.tail)
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (Erasure.Exposure.supportPattern
            (Region.ofItems (.cons materialHead materialTail)) fullCanonical)
          frame.sourceKeep frame.selected source result) :
      ∃ edit : Transform.RegionEdit (Content.Parallel.operation wires)
          frame data source,
        ∃ splitSource : Region splitWires,
          ∃ headResult tailSource : Region middleWires,
            ∃ tailResult : Region common,
              VisualProof.Rule.Comprehension.Instantiation.RegionResult
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  frames.head.sourceKeep frames.head.selected
                  splitSource headResult ∧
              VisualProof.Rule.Comprehension.Instantiation.RegionResult
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  frames.tail.sourceKeep frames.tail.selected
                  tailSource tailResult ∧
              Nonempty (RegionIso (WireEquiv.refl splitWires)
                edit.run splitSource) ∧
              HostedStrict headResult tailSource ∧
              HostedStrict result tailResult ∧
              SupportParallelSplitValidity frame data source splitSource ∧
              SupportParallelSelectedValidity frame.sourceKeep
                frames.tail.sourceKeep frame.selected frames.tail.selected
                source tailSource ∧
              SupportParallelSelectedValidity frames.tail.sourceKeep
                frames.tail.sourceKeep frames.tail.selected frames.tail.selected
                tailSource headResult ∧
              SupportParallelRetainedValidity (WireEquiv.refl common).toRenaming
                (WireEquiv.refl common).toRenaming result tailResult := by
    cases evidence with
    | @mk _ _ _ _ locals items itemResult childEvidence =>
        obtain ⟨itemsEdit, splitItems, childHeadResult, childTailItems,
            childTailResult, headEvidence, tailEvidence, ⟨itemsIso⟩,
            headBridge, resultBridge, splitValidity, sourceTailValidity,
            tailHeadValidity, resultValidity⟩ :=
          supportParallelItemsFactor materialHead materialTail fullCanonical
            headCanonical tailCanonical
              (SupportParallelFrames.append (locals := locals) frames)
              (frameInvariant.append locals) (headInvariant.append locals)
              (tailInvariant.append locals)
              childEvidence
        let edit : Transform.RegionEdit (Content.Parallel.operation wires)
            frame data (.mk locals items) := .mk itemsEdit
        let splitSource : Region splitWires := .mk locals splitItems
        let headResult : Region middleWires :=
          Region.adjoinAt locals .nil childHeadResult
        let tailSource : Region middleWires := .mk locals childTailItems
        let tailResult : Region common :=
          Region.adjoinAt locals .nil childTailResult
        have runIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
            edit.run splitSource) := by
          let lifted := RegionIso.adjoinAt locals .nil itemsIso
          exact ⟨lifted.trans (RegionIso.adjoinAtOfItems locals splitItems)⟩
        have headBridge' : HostedStrict headResult tailSource := by
          apply HostedStrict.iso (RegionIso.refl _)
            (RegionIso.adjoinAtOfItems locals childTailItems)
          exact HostedStrict.adjoinAt locals childHeadResult
            (Region.ofItems childTailItems) headBridge
        have resultValidity' : SupportParallelRetainedValidity
            ((WireEquiv.refl common).toRenaming.appendRight locals)
            ((WireEquiv.refl common).toRenaming.appendRight locals)
            itemResult childTailResult := by
          constructor
          · exact resultValidity.canonical
          · intro signature wire
            apply Var.appendCases (left := common) (right := locals)
              (motive := fun wire => SupportParallelIncidenceScope
                (itemResult.incidencePaths
                  (((WireEquiv.refl common).toRenaming.appendRight locals)
                    wire).index.val)
                (childTailResult.incidencePaths
                  (((WireEquiv.refl common).toRenaming.appendRight locals)
                    wire).index.val))
            · intro inheritedSignature inherited
              simpa [WireRenaming.appendRight] using
                resultValidity.retained (inherited.appendLeft locals)
            · intro localSignature localWire
              simpa [WireRenaming.appendRight] using
                resultValidity.retained (Var.appendRight common localWire)
        obtain ⟨regionSplitValidity, regionSourceTailValidity,
            regionTailHeadValidity, regionResultValidity⟩ :=
          supportParallelRegionLift frames splitValidity sourceTailValidity
            tailHeadValidity resultValidity'
        exact ⟨edit, splitSource, headResult, tailSource, tailResult,
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            headEvidence,
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            tailEvidence,
          runIso, headBridge',
          HostedStrict.adjoinAt locals itemResult childTailResult
            resultBridge,
          regionSplitValidity, regionSourceTailValidity,
          regionTailHeadValidity, regionResultValidity⟩
  termination_by sizeOf source

  /-- The item-sequence half of the same fused traversal. -/
  theorem supportParallelItemsFactor
      {wires common sourceWires splitWires middleWires : List Sig}
      (materialHead : Item wires) (materialTail : ItemSeq wires)
      (fullCanonical :
        (Region.ofItems (.cons materialHead materialTail)).Canonical)
      (headCanonical : (Region.singleton materialHead).Canonical)
      (tailCanonical : (Region.ofItems materialTail).Canonical)
      {frame : Transform.Frame wires common sourceWires splitWires}
      {data : (Content.Parallel.operation wires).Data frame}
      (frames : SupportParallelFrames (middleWires := middleWires) frame data)
      (frameInvariant : Transform.RetainedIndexInvariant frame)
      (headInvariant : Transform.RetainedIndexInvariant frames.head)
      (tailInvariant : Transform.RetainedIndexInvariant frames.tail)
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (Erasure.Exposure.supportPattern
            (Region.ofItems (.cons materialHead materialTail)) fullCanonical)
          frame.sourceKeep frame.selected source result) :
      ∃ edit : Transform.ItemsEdit (Content.Parallel.operation wires)
          frame data source,
        ∃ splitItems : ItemSeq splitWires,
          ∃ headResult : Region middleWires,
            ∃ tailItems : ItemSeq middleWires,
              ∃ tailResult : Region common,
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                    (Erasure.Exposure.supportPattern
                      (Region.singleton materialHead) headCanonical)
                    frames.head.sourceKeep frames.head.selected
                    splitItems headResult ∧
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                    (Erasure.Exposure.supportPattern
                      (Region.ofItems materialTail) tailCanonical)
                    frames.tail.sourceKeep frames.tail.selected
                    tailItems tailResult ∧
                Nonempty (RegionIso (WireEquiv.refl splitWires)
                  edit.run (Region.ofItems splitItems)) ∧
                HostedStrict headResult (Region.ofItems tailItems) ∧
                HostedStrict result tailResult ∧
                SupportParallelSplitValidity frame data
                  (Region.ofItems source) (Region.ofItems splitItems) ∧
                SupportParallelSelectedValidity frame.sourceKeep
                  frames.tail.sourceKeep frame.selected frames.tail.selected
                  (Region.ofItems source) (Region.ofItems tailItems) ∧
                SupportParallelSelectedValidity frames.tail.sourceKeep
                  frames.tail.sourceKeep frames.tail.selected frames.tail.selected
                  (Region.ofItems tailItems) headResult ∧
                SupportParallelRetainedValidity
                  (WireEquiv.refl common).toRenaming
                  (WireEquiv.refl common).toRenaming result tailResult := by
    cases evidence with
    | nil =>
        exact ⟨.nil, .nil, Region.blank middleWires, .nil,
          Region.blank common,
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil,
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil,
          ⟨RegionIso.refl _⟩, HostedStrict.refl _, HostedStrict.refl _,
          {
            canonical := fun canonical => by
              simpa using canonical
            retained := fun _ => SupportParallelIncidenceScope.refl []
            first := SupportParallelIncidenceScope.refl []
            second := SupportParallelIncidenceScope.refl []
          },
          {
            canonical := fun canonical => by
              simpa using canonical
            retained := fun _ => SupportParallelIncidenceScope.refl []
            selected := SupportParallelIncidenceScope.refl []
          },
          {
            canonical := fun canonical => by
              simpa using canonical
            retained := fun _ => SupportParallelIncidenceScope.refl []
            selected := SupportParallelIncidenceScope.refl []
          },
          {
            canonical := fun canonical => by
              simpa using canonical
            retained := fun _ => SupportParallelIncidenceScope.refl []
          }⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨tailEdit, splitTail, childHeadResult, childTailItems,
            childTailResult, childHeadEvidence, childTailEvidence,
            ⟨tailIso⟩, childHeadBridge, childResultBridge,
            childSplitValidity, childSourceTailValidity,
            childTailHeadValidity, childResultValidity⟩ :=
          supportParallelItemsFactor materialHead materialTail fullCanonical
            headCanonical tailCanonical frames frameInvariant headInvariant
              tailInvariant tailEvidence
        cases itemEvidence with
        | atom head ports =>
            let splitItem := Item.atom (frame.targetKeep head)
              (ports.map fun wire => frame.targetKeep wire)
            let middleItem := Item.atom (frames.tail.sourceKeep head)
              (ports.map fun wire => frames.tail.sourceKeep wire)
            have splitEq :
                Item.atom
                    (frames.head.sourceKeep (frames.tail.sourceKeep head))
                    ((ports.map fun wire => frames.tail.sourceKeep wire).map
                      fun wire => frames.head.sourceKeep wire) =
                  splitItem := by
              simp only [Vars.map_map, splitItem]
              rw [frames.retained head]
              congr 1
              apply Vars.map_congr
              intro signature wire
              exact frames.retained wire
            let edit : Transform.ItemsEdit (Content.Parallel.operation wires)
                frame data _ := .cons (.atom head ports) tailEdit
            let splitItems := ItemSeq.cons splitItem splitTail
            let headResult :=
              (Region.singleton middleItem).conjoin childHeadResult
            let tailItems := ItemSeq.cons middleItem childTailItems
            let tailResult :=
              (Region.singleton (.atom head ports)).conjoin childTailResult
            have headEvidence :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  frames.head.sourceKeep frames.head.selected
                  splitItems headResult := by
              simp only [splitItems, headResult]
              rw [← splitEq]
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
                    (frames.tail.sourceKeep head)
                    (ports.map fun wire => frames.tail.sourceKeep wire))
                  childHeadEvidence
            have tailEvidence' :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  frames.tail.sourceKeep frames.tail.selected
                  tailItems tailResult := by
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
                    head ports) childTailEvidence
            have editIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
                edit.run (Region.ofItems splitItems)) := by
              exact ⟨(RegionIso.conjoinCongr (RegionIso.refl _) tailIso).trans
                (RegionIso.ofEq
                  (Region.singleton_conjoin_ofItems splitItem splitTail))⟩
            have headBridge : HostedStrict headResult
                (Region.ofItems tailItems) := by
              apply HostedStrict.iso (RegionIso.refl _)
                (RegionIso.ofEq
                  (Region.singleton_conjoin_ofItems middleItem childTailItems))
              exact HostedStrict.conjoin _ _ _ _ (HostedStrict.refl _)
                childHeadBridge
            have sourceTailReflects : ∀ {leftSignature rightSignature}
                (left : Var common leftSignature)
                (right : Var common rightSignature),
                (frame.sourceKeep left).index.val =
                    (frame.sourceKeep right).index.val ↔
                  (frames.tail.sourceKeep left).index.val =
                    (frames.tail.sourceKeep right).index.val := by
              intro leftSignature rightSignature left right
              rw [frameInvariant.reflects left right]
              rw [← frames.retained left, ← frames.retained right]
              rw [headInvariant.reflects
                (frames.tail.sourceKeep left) (frames.tail.sourceKeep right)]
              rw [frames.headTarget, frames.headTarget]
            have firstFresh : ∀ {wireSignature}
                (wire : Var common wireSignature),
                data.1.index.val ≠ (frame.targetKeep wire).index.val := by
              intro wireSignature wire
              rw [← frames.first, ← frames.retained wire]
              exact headInvariant.selectedFresh (frames.tail.sourceKeep wire)
            have secondFresh : ∀ {wireSignature}
                (wire : Var common wireSignature),
                data.2.index.val ≠ (frame.targetKeep wire).index.val := by
              intro wireSignature wire equality
              rw [← frames.second, ← frames.retained wire] at equality
              have targetEquality := (headInvariant.reflects
                frames.tail.selected (frames.tail.sourceKeep wire)).mp equality
              rw [frames.headTarget, frames.headTarget] at targetEquality
              exact tailInvariant.selectedFresh wire targetEquality
            have siteSplitValidity : SupportParallelSplitValidity frame data
                (Region.singleton (.atom (frame.sourceKeep head)
                  (ports.map fun wire => frame.sourceKeep wire)))
                (Region.singleton splitItem) := by
              refine {
                toSupportParallelRetainedValidity := ?_
                first := ?_
                second := ?_
              }
              · exact supportParallelAtomRetainedValidity
                  frameInvariant.reflects head ports
              · exact supportParallelAtomFreshScope frame.selected data.1
                  frameInvariant.selectedFresh firstFresh head ports
              · exact supportParallelAtomFreshScope frame.selected data.2
                  frameInvariant.selectedFresh secondFresh head ports
            have siteSourceTailValidity : SupportParallelSelectedValidity
                frame.sourceKeep frames.tail.sourceKeep frame.selected
                  frames.tail.selected
                (Region.singleton (.atom (frame.sourceKeep head)
                  (ports.map fun wire => frame.sourceKeep wire)))
                (Region.singleton middleItem) := {
              toSupportParallelRetainedValidity :=
                supportParallelAtomRetainedValidity sourceTailReflects head ports
              selected := supportParallelAtomFreshScope frame.selected
                frames.tail.selected frameInvariant.selectedFresh
                  tailInvariant.selectedFresh head ports
            }
            have siteTailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                (Region.singleton middleItem) (Region.singleton middleItem) := {
              toSupportParallelRetainedValidity :=
                supportParallelAtomRetainedValidity
                  (fun _ _ => Iff.rfl) head ports
              selected := supportParallelAtomFreshScope frames.tail.selected
                frames.tail.selected tailInvariant.selectedFresh
                  tailInvariant.selectedFresh head ports
            }
            have siteResultValidity : SupportParallelRetainedValidity
                (WireEquiv.refl common).toRenaming
                (WireEquiv.refl common).toRenaming
                (Region.singleton (.atom head ports))
                (Region.singleton (.atom head ports)) := {
              canonical := fun canonical => canonical
              retained := fun wire => by
                simpa using SupportParallelIncidenceScope.refl
                  ((Region.singleton (.atom head ports)).incidencePaths
                    wire.index.val)
            }
            let splitValidityCore :=
              siteSplitValidity.conjoin childSplitValidity
            let sourceTailValidityCore :=
              siteSourceTailValidity.conjoin childSourceTailValidity
            have tailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                (Region.ofItems tailItems) headResult := by
              rw [← Region.singleton_conjoin_ofItems]
              exact siteTailHeadValidity.conjoin childTailHeadValidity
            let resultValidityCore :=
              siteResultValidity.conjoin childResultValidity
            exact ⟨edit, splitItems, headResult, tailItems, tailResult,
              headEvidence, tailEvidence', editIso, headBridge,
              HostedStrict.conjoin _ _ _ _ (HostedStrict.refl _)
                childResultBridge,
              (by simpa only [Region.singleton_conjoin_ofItems] using
                splitValidityCore),
              (by simpa only [Region.singleton_conjoin_ofItems] using
                sourceTailValidityCore), tailHeadValidity,
              resultValidityCore⟩
        | identity signature arity ports =>
            let splitItem := Item.identity signature arity
              (fun index => frame.targetKeep (ports index))
            let middleItem := Item.identity signature arity
              (fun index => frames.tail.sourceKeep (ports index))
            have splitEq :
                Item.identity signature arity
                    (fun index => frames.head.sourceKeep
                      (frames.tail.sourceKeep (ports index))) =
                  splitItem := by
              simp only [splitItem]
              congr 1
              funext index
              exact frames.retained (ports index)
            let edit : Transform.ItemsEdit (Content.Parallel.operation wires)
                frame data _ := .cons (.identity signature arity ports) tailEdit
            let splitItems := ItemSeq.cons splitItem splitTail
            let headResult :=
              (Region.singleton middleItem).conjoin childHeadResult
            let tailItems := ItemSeq.cons middleItem childTailItems
            let tailResult :=
              (Region.singleton (.identity signature arity ports)).conjoin
                childTailResult
            have headEvidence :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  frames.head.sourceKeep frames.head.selected
                  splitItems headResult := by
              simp only [splitItems, headResult]
              rw [← splitEq]
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
                    signature arity
                    (fun index => frames.tail.sourceKeep (ports index)))
                  childHeadEvidence
            have tailEvidence' :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  frames.tail.sourceKeep frames.tail.selected
                  tailItems tailResult := by
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
                    signature arity ports) childTailEvidence
            have editIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
                edit.run (Region.ofItems splitItems)) := by
              exact ⟨(RegionIso.conjoinCongr (RegionIso.refl _) tailIso).trans
                (RegionIso.ofEq
                  (Region.singleton_conjoin_ofItems splitItem splitTail))⟩
            have headBridge : HostedStrict headResult
                (Region.ofItems tailItems) := by
              apply HostedStrict.iso (RegionIso.refl _)
                (RegionIso.ofEq
                  (Region.singleton_conjoin_ofItems middleItem childTailItems))
              exact HostedStrict.conjoin _ _ _ _ (HostedStrict.refl _)
                childHeadBridge
            have sourceTailReflects : ∀ {leftSignature rightSignature}
                (left : Var common leftSignature)
                (right : Var common rightSignature),
                (frame.sourceKeep left).index.val =
                    (frame.sourceKeep right).index.val ↔
                  (frames.tail.sourceKeep left).index.val =
                    (frames.tail.sourceKeep right).index.val := by
              intro leftSignature rightSignature left right
              rw [frameInvariant.reflects left right]
              rw [← frames.retained left, ← frames.retained right]
              rw [headInvariant.reflects
                (frames.tail.sourceKeep left) (frames.tail.sourceKeep right)]
              rw [frames.headTarget, frames.headTarget]
            have firstFresh : ∀ {wireSignature}
                (wire : Var common wireSignature),
                data.1.index.val ≠ (frame.targetKeep wire).index.val := by
              intro wireSignature wire
              rw [← frames.first, ← frames.retained wire]
              exact headInvariant.selectedFresh (frames.tail.sourceKeep wire)
            have secondFresh : ∀ {wireSignature}
                (wire : Var common wireSignature),
                data.2.index.val ≠ (frame.targetKeep wire).index.val := by
              intro wireSignature wire equality
              rw [← frames.second, ← frames.retained wire] at equality
              have targetEquality := (headInvariant.reflects
                frames.tail.selected (frames.tail.sourceKeep wire)).mp equality
              rw [frames.headTarget, frames.headTarget] at targetEquality
              exact tailInvariant.selectedFresh wire targetEquality
            have siteSplitValidity : SupportParallelSplitValidity frame data
                (Region.singleton (.identity signature arity
                  (fun index => frame.sourceKeep (ports index))))
                (Region.singleton splitItem) := {
              toSupportParallelRetainedValidity :=
                supportParallelIdentityRetainedValidity
                  frameInvariant.reflects signature arity ports
              first := supportParallelIdentityFreshScope frame.selected data.1
                frameInvariant.selectedFresh firstFresh signature arity ports
              second := supportParallelIdentityFreshScope frame.selected data.2
                frameInvariant.selectedFresh secondFresh signature arity ports
            }
            have siteSourceTailValidity : SupportParallelSelectedValidity
                frame.sourceKeep frames.tail.sourceKeep frame.selected
                  frames.tail.selected
                (Region.singleton (.identity signature arity
                  (fun index => frame.sourceKeep (ports index))))
                (Region.singleton middleItem) := {
              toSupportParallelRetainedValidity :=
                supportParallelIdentityRetainedValidity sourceTailReflects
                  signature arity ports
              selected := supportParallelIdentityFreshScope frame.selected
                frames.tail.selected frameInvariant.selectedFresh
                  tailInvariant.selectedFresh signature arity ports
            }
            have siteTailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                (Region.singleton middleItem) (Region.singleton middleItem) := {
              toSupportParallelRetainedValidity :=
                supportParallelIdentityRetainedValidity
                  (fun _ _ => Iff.rfl) signature arity ports
              selected := supportParallelIdentityFreshScope
                frames.tail.selected frames.tail.selected
                  tailInvariant.selectedFresh tailInvariant.selectedFresh
                  signature arity ports
            }
            have siteResultValidity : SupportParallelRetainedValidity
                (WireEquiv.refl common).toRenaming
                (WireEquiv.refl common).toRenaming
                (Region.singleton (.identity signature arity ports))
                (Region.singleton (.identity signature arity ports)) := {
              canonical := fun canonical => canonical
              retained := fun wire => by
                simpa using SupportParallelIncidenceScope.refl
                  ((Region.singleton (.identity signature arity ports)
                    ).incidencePaths wire.index.val)
            }
            let splitValidityCore :=
              siteSplitValidity.conjoin childSplitValidity
            let sourceTailValidityCore :=
              siteSourceTailValidity.conjoin childSourceTailValidity
            have tailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                (Region.ofItems tailItems) headResult := by
              rw [← Region.singleton_conjoin_ofItems]
              exact siteTailHeadValidity.conjoin childTailHeadValidity
            let resultValidityCore :=
              siteResultValidity.conjoin childResultValidity
            exact ⟨edit, splitItems, headResult, tailItems, tailResult,
              headEvidence, tailEvidence', editIso, headBridge,
              HostedStrict.conjoin _ _ _ _ (HostedStrict.refl _)
                childResultBridge,
              (by simpa only [Region.singleton_conjoin_ofItems] using
                splitValidityCore),
              (by simpa only [Region.singleton_conjoin_ofItems] using
                sourceTailValidityCore), tailHeadValidity,
              resultValidityCore⟩
        | selectedAtom application =>
            let splitFirst := Item.atom data.1
              (application.map fun wire => frame.targetKeep wire)
            let splitSecond := Item.atom data.2
              (application.map fun wire => frame.targetKeep wire)
            let middleApplication :=
              application.map fun wire => frames.tail.sourceKeep wire
            let middleSecond := Item.atom frames.tail.selected middleApplication
            let rawHead := materialHead.renameWires
              (EqualityNormalization.formalSubstitution application)
            let middleRawHead := rawHead.renameWires frames.tail.sourceKeep
            let edit : Transform.ItemsEdit (Content.Parallel.operation wires)
                frame data _ :=
              .cons (.selectedAtom application PUnit.unit) tailEdit
            let splitItems :=
              ItemSeq.cons splitFirst (.cons splitSecond splitTail)
            let headResult :=
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (Region.singleton materialHead) headCanonical)
                middleApplication).conjoin
                ((Region.singleton middleSecond).conjoin childHeadResult)
            let tailItems := ItemSeq.cons middleRawHead
              (.cons middleSecond childTailItems)
            let tailResult :=
              (retainedItemPresentation rawHead).conjoin
                ((VisualProof.Rule.Comprehension.Instantiation.instantiate
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  application).conjoin childTailResult)
            have splitFirstEq :
                Item.atom frames.head.selected
                    (middleApplication.map fun wire =>
                      frames.head.sourceKeep wire) = splitFirst := by
              simp only [middleApplication, Vars.map_map, splitFirst,
                frames.first]
              congr 1
              apply Vars.map_congr
              intro signature wire
              exact frames.retained wire
            have splitSecondEq :
                Item.atom (frames.head.sourceKeep frames.tail.selected)
                    (middleApplication.map fun wire =>
                      frames.head.sourceKeep wire) = splitSecond := by
              simp only [middleApplication, Vars.map_map, splitSecond,
                frames.second]
              congr 1
              apply Vars.map_congr
              intro signature wire
              exact frames.retained wire
            have headEvidence :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  frames.head.sourceKeep frames.head.selected
                  splitItems headResult := by
              simp only [splitItems, headResult]
              rw [← splitFirstEq, ← splitSecondEq]
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                    middleApplication)
                  (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                    (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
                      frames.tail.selected middleApplication)
                    childHeadEvidence)
            have tailEvidence' :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  frames.tail.sourceKeep frames.tail.selected
                  tailItems tailResult := by
              exact
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                  (retainedItemResult
                    (Erasure.Exposure.supportPattern
                      (Region.ofItems materialTail) tailCanonical)
                    frames.tail rawHead)
                  (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                    (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
                      application) childTailEvidence)
            have editIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
                edit.run (Region.ofItems splitItems)) := by
              let firstRegion := Region.singleton splitFirst
              let secondRegion := Region.singleton splitSecond
              let children : RegionIso (WireEquiv.refl splitWires)
                  ((firstRegion.conjoin secondRegion).conjoin tailEdit.run)
                  ((firstRegion.conjoin secondRegion).conjoin
                    (Region.ofItems splitTail)) :=
                RegionIso.conjoinCongr
                  (RegionIso.conjoinCongr (RegionIso.refl firstRegion)
                    (RegionIso.refl secondRegion)) tailIso
              let associated : RegionIso (WireEquiv.refl splitWires)
                  ((firstRegion.conjoin secondRegion).conjoin
                    (Region.ofItems splitTail))
                  (firstRegion.conjoin
                    (secondRegion.conjoin (Region.ofItems splitTail))) :=
                RegionIso.conjoinAssoc _ _ _
              let presented : RegionIso (WireEquiv.refl splitWires)
                  (firstRegion.conjoin
                    (secondRegion.conjoin (Region.ofItems splitTail)))
                  (Region.ofItems splitItems) := RegionIso.ofEq (by
                simp only [firstRegion, secondRegion, splitItems]
                rw [Region.singleton_conjoin_ofItems splitSecond splitTail,
                  Region.singleton_conjoin_ofItems splitFirst
                    (.cons splitSecond splitTail)])
              exact ⟨children.trans (associated.trans presented)⟩
            have middleRawHeadEq :
                materialHead.renameWires
                    (EqualityNormalization.formalSubstitution
                      middleApplication) = middleRawHead := by
              simp only [middleRawHead, rawHead, Item.renameWires_comp]
              congr 1
              apply WireRenaming.ext
              intro signature wire
              exact EqualityNormalization.formalSubstitution_map
                application frames.tail.sourceKeep wire
            have siteHeadBridge : HostedStrict
                ((VisualProof.Rule.Comprehension.Instantiation.instantiate
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  middleApplication).conjoin (Region.singleton middleSecond))
                (Region.ofItems (.cons middleRawHead
                  (.cons middleSecond .nil))) := by
              rw [← middleRawHeadEq]
              exact supportParallelSelectedHeadHosted materialHead
                headCanonical middleApplication frames.tail.selected
            have headBridge : HostedStrict headResult
                (Region.ofItems tailItems) := by
              let targetPresentation : RegionIso (WireEquiv.refl middleWires)
                  ((Region.ofItems (.cons middleRawHead
                    (.cons middleSecond .nil))).conjoin
                      (Region.ofItems childTailItems))
                  (Region.ofItems tailItems) := by
                apply RegionIso.ofEq
                rw [Region.ofItems_conjoin]
                simp only [tailItems, ItemSeq.append]
              apply HostedStrict.iso
                (RegionIso.conjoinAssoc _ _ _).symm
                targetPresentation
              exact HostedStrict.conjoin _ _ _ _ siteHeadBridge
                childHeadBridge
            have siteResultBridge : HostedStrict
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems (.cons materialHead materialTail))
                      fullCanonical) application)
                ((retainedItemPresentation rawHead).conjoin
                  (VisualProof.Rule.Comprehension.Instantiation.instantiate
                    (Erasure.Exposure.supportPattern
                      (Region.ofItems materialTail) tailCanonical)
                    application)) :=
              supportParallelSelectedResultHosted materialHead materialTail
                fullCanonical tailCanonical application
            have sourceTailReflects : ∀ {leftSignature rightSignature}
                (left : Var common leftSignature)
                (right : Var common rightSignature),
                (frame.sourceKeep left).index.val =
                    (frame.sourceKeep right).index.val ↔
                  (frames.tail.sourceKeep left).index.val =
                    (frames.tail.sourceKeep right).index.val := by
              intro leftSignature rightSignature left right
              rw [frameInvariant.reflects left right]
              rw [← frames.retained left, ← frames.retained right]
              rw [headInvariant.reflects
                (frames.tail.sourceKeep left) (frames.tail.sourceKeep right)]
              rw [frames.headTarget, frames.headTarget]
            have siteSplitValidity : SupportParallelSplitValidity frame data
                (Region.singleton (.atom frame.selected
                  (application.map fun wire => frame.sourceKeep wire)))
                ((Region.singleton splitFirst).conjoin
                  (Region.singleton splitSecond)) := by
              exact supportParallelSelectedAtomSplitValidity data frameInvariant
                (frames.firstFresh headInvariant)
                (frames.secondFresh headInvariant tailInvariant)
                (frames.headsDistinct headInvariant) application
            have siteSourceTailValidity : SupportParallelSelectedValidity
                frame.sourceKeep frames.tail.sourceKeep frame.selected
                  frames.tail.selected
                (Region.singleton (.atom frame.selected
                  (application.map fun wire => frame.sourceKeep wire)))
                ((Region.singleton middleRawHead).conjoin
                  (Region.singleton middleSecond)) := by
              have base := supportParallelSelectedSourceToTailValidity
                frame.selected frames.tail.selected
                frameInvariant.selectedFresh tailInvariant.selectedFresh
                sourceTailReflects materialHead headCanonical application
              simpa only [middleApplication, middleSecond,
                middleRawHeadEq] using base
            have siteTailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                ((Region.singleton middleRawHead).conjoin
                  (Region.singleton middleSecond))
                ((VisualProof.Rule.Comprehension.Instantiation.instantiate
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  middleApplication).conjoin
                    (Region.singleton middleSecond)) := by
              have base := supportParallelSelectedTailToHeadValidity
                frames.tail.selected tailInvariant.selectedFresh
                materialHead headCanonical application
              simpa only [middleApplication, middleSecond,
                middleRawHeadEq] using base
            have siteResultValidity : SupportParallelRetainedValidity
                (WireEquiv.refl common).toRenaming
                (WireEquiv.refl common).toRenaming
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems (.cons materialHead materialTail))
                    fullCanonical) application)
                ((retainedItemPresentation rawHead).conjoin
                  (VisualProof.Rule.Comprehension.Instantiation.instantiate
                    (Erasure.Exposure.supportPattern
                      (Region.ofItems materialTail) tailCanonical)
                    application)) := by
              have base := supportParallelSelectedResultToTailValidity
                materialHead materialTail fullCanonical headCanonical
                  tailCanonical application
              exact base.iso (RegionIso.refl _)
                (RegionIso.conjoinCongr
                  (retainedItemPresentationIso rawHead).symm
                  (RegionIso.refl _))
            let splitValidityCore :=
              siteSplitValidity.conjoin childSplitValidity
            let sourceTailValidityCore :=
              siteSourceTailValidity.conjoin childSourceTailValidity
            let tailHeadValidityCore :=
              siteTailHeadValidity.conjoin childTailHeadValidity
            let resultValidityCore :=
              siteResultValidity.conjoin childResultValidity
            let splitValidity := splitValidityCore.iso
              (RegionIso.ofEq
                (Region.singleton_conjoin_ofItems _ _)).symm
              ((RegionIso.conjoinAssoc _ _ _).trans
                (RegionIso.ofEq (by
                  rw [Region.singleton_conjoin_ofItems splitSecond splitTail,
                    Region.singleton_conjoin_ofItems splitFirst
                      (.cons splitSecond splitTail)])))
            let sourceTailValidity := sourceTailValidityCore.iso
              (RegionIso.ofEq
                (Region.singleton_conjoin_ofItems _ _)).symm
              ((RegionIso.conjoinAssoc _ _ _).trans
                (RegionIso.ofEq (by
                  rw [Region.singleton_conjoin_ofItems middleSecond
                      childTailItems,
                    Region.singleton_conjoin_ofItems middleRawHead
                      (.cons middleSecond childTailItems)])))
            have tailHeadValidity : SupportParallelSelectedValidity
                frames.tail.sourceKeep frames.tail.sourceKeep
                  frames.tail.selected frames.tail.selected
                (Region.ofItems tailItems) headResult := by
              apply tailHeadValidityCore.iso
              · exact ((RegionIso.conjoinAssoc _ _ _).trans
                  (RegionIso.ofEq (by
                    rw [Region.singleton_conjoin_ofItems middleSecond
                        childTailItems,
                      Region.singleton_conjoin_ofItems middleRawHead
                        (.cons middleSecond childTailItems)]))).symm
              · exact RegionIso.conjoinAssoc _ _ _
            let resultValidity := resultValidityCore.iso (RegionIso.refl _)
              (RegionIso.conjoinAssoc _ _ _)
            exact ⟨edit, splitItems, headResult, tailItems, tailResult,
              headEvidence, tailEvidence', editIso, headBridge,
              HostedStrict.iso (RegionIso.refl _)
                (RegionIso.conjoinAssoc _ _ _)
                (HostedStrict.conjoin _ _ _ _ siteResultBridge
                  childResultBridge), splitValidity, sourceTailValidity,
              tailHeadValidity, resultValidity⟩
        | cut bodyEvidence =>
            obtain ⟨bodyEdit, splitBody, bodyHeadResult, bodyTailSource,
                bodyTailResult, bodyHeadEvidence, bodyTailEvidence,
                ⟨bodyIso⟩, bodyHeadBridge, bodyResultBridge,
                bodySplitValidity, bodySourceTailValidity,
                bodyTailHeadValidity, bodyResultValidity⟩ :=
              supportParallelRegionFactor materialHead materialTail
                fullCanonical headCanonical tailCanonical frames frameInvariant
                  headInvariant tailInvariant bodyEvidence
            let edit : Transform.ItemsEdit (Content.Parallel.operation wires)
                frame data _ := .cons (.cut bodyEdit) tailEdit
            let splitItem := Item.cut splitBody
            let tailItem := Item.cut bodyTailSource
            let splitItems := ItemSeq.cons splitItem splitTail
            let headResult :=
              (Region.singleton (.cut bodyHeadResult)).conjoin childHeadResult
            let tailItems := ItemSeq.cons tailItem childTailItems
            let tailResult :=
              (Region.singleton (.cut bodyTailResult)).conjoin childTailResult
            have headEvidence :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.singleton materialHead) headCanonical)
                  frames.head.sourceKeep frames.head.selected
                  splitItems headResult :=
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                (VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
                  bodyHeadEvidence) childHeadEvidence
            have tailEvidence' :
                VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                  (Erasure.Exposure.supportPattern
                    (Region.ofItems materialTail) tailCanonical)
                  frames.tail.sourceKeep frames.tail.selected
                  tailItems tailResult :=
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                (VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
                  bodyTailEvidence) childTailEvidence
            have editIso : Nonempty (RegionIso (WireEquiv.refl splitWires)
                edit.run (Region.ofItems splitItems)) := by
              exact ⟨(RegionIso.conjoinCongr
                (RegionIso.singletonCutCongr bodyIso) tailIso).trans
                  (RegionIso.ofEq
                    (Region.singleton_conjoin_ofItems splitItem splitTail))⟩
            have headBridge : HostedStrict headResult
                (Region.ofItems tailItems) := by
              apply HostedStrict.iso (RegionIso.refl _)
                (RegionIso.ofEq
                  (Region.singleton_conjoin_ofItems tailItem childTailItems))
              exact HostedStrict.conjoin _ _ _ _
                (HostedStrict.cut _ _ bodyHeadBridge) childHeadBridge
            let splitValidityCore :=
              bodySplitValidity.cut.conjoin childSplitValidity
            let sourceTailValidityCore :=
              bodySourceTailValidity.cut.conjoin childSourceTailValidity
            let tailHeadValidityCore :=
              bodyTailHeadValidity.cut.conjoin childTailHeadValidity
            let resultValidityCore :=
              bodyResultValidity.cut.conjoin childResultValidity
            exact ⟨edit, splitItems, headResult, tailItems, tailResult,
              headEvidence, tailEvidence', editIso, headBridge,
              HostedStrict.conjoin _ _ _ _
                (HostedStrict.cut _ _ bodyResultBridge) childResultBridge,
              (by simpa only [Region.singleton_conjoin_ofItems] using
                splitValidityCore),
              (by simpa only [Region.singleton_conjoin_ofItems] using
                sourceTailValidityCore),
              (by simpa only [Region.singleton_conjoin_ofItems] using
                tailHeadValidityCore),
              resultValidityCore⟩
  termination_by sizeOf source
end

theorem supportParallelRootSelectedAdjoinCanonical
    (outer before after arguments : List Sig)
    {source target : Region
      (outer ++ (before ++ .rel arguments :: after))}
    (sourceCanonical :
      (Region.adjoinAt (before ++ .rel arguments :: after) .nil
        source).Canonical)
    (validity : SupportParallelSelectedValidity
      (Transform.Frame.replace outer before after [] arguments).sourceKeep
      (Transform.Frame.replace outer before after [] arguments).sourceKeep
      (Transform.Frame.replace outer before after [] arguments).selected
      (Transform.Frame.replace outer before after [] arguments).selected
      source target) :
    (Region.adjoinAt (before ++ .rel arguments :: after) .nil
      target).Canonical := by
  let locals := before ++ .rel arguments :: after
  let frame := Transform.Frame.replace outer before after [] arguments
  have targetMaterialCanonical := validity.canonical
    (Region.Canonical.material_of_adjoinAt locals .nil source
      (by simpa only [locals] using sourceCanonical))
  apply Region.Canonical.adjoinAt_of_material_roots locals .nil target
    True.intro targetMaterialCanonical
  intro localIndex
  by_cases beforeCase : localIndex.val < before.length
  · let beforeIndex : Fin before.length := ⟨localIndex.val, beforeCase⟩
    let commonWire := Var.appendRight outer
      ((Var.ofIndex beforeIndex).appendLeft after)
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
        (by simpa only [locals] using sourceCanonical) localIndex
    have transferred := (validity.retained commonWire).rooted (by
      simpa [frame, commonWire, beforeIndex, locals,
        Transform.Frame.replace, Transform.Frame.keep,
        Transform.Frame.localKeep] using sourceRoot)
    simpa [frame, commonWire, beforeIndex, locals,
      Transform.Frame.replace, Transform.Frame.keep,
      Transform.Frame.localKeep] using transferred
  · by_cases selectedCase : localIndex.val = before.length
    · have sourceRoot :=
        Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
          (by simpa only [locals] using sourceCanonical) localIndex
      have transferred := validity.selected.rooted (by
        simpa [frame, selectedCase, locals, Transform.Frame.replace,
          Transform.Frame.insertedHead] using sourceRoot)
      simpa [frame, selectedCase, locals, Transform.Frame.replace,
        Transform.Frame.insertedHead] using transferred
    · have afterBound : localIndex.val - before.length - 1 < after.length := by
        have bound := localIndex.isLt
        simp [locals] at bound
        omega
      let afterIndex : Fin after.length :=
        ⟨localIndex.val - before.length - 1, afterBound⟩
      let commonWire := Var.appendRight outer
        (Var.appendRight before (Var.ofIndex afterIndex))
      have sourceRoot :=
        Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil source
          (by simpa only [locals] using sourceCanonical) localIndex
      have lifted : (Var.appendRight [.rel arguments]
          (Var.ofIndex afterIndex)).index.val = 1 + afterIndex.val := by
        simpa using (Var.index_appendRight [.rel arguments]
          (Var.ofIndex afterIndex))
      have indexEq : (frame.sourceKeep commonWire).index.val =
          outer.length + localIndex.val := by
        have raw : (frame.sourceKeep commonWire).index.val =
            outer.length + (before.length +
              (Var.appendRight [.rel arguments]
                (Var.ofIndex afterIndex)).index.val) := by
          simp [frame, commonWire, afterIndex, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
        calc
          _ = outer.length + (before.length +
              (Var.appendRight [.rel arguments]
                (Var.ofIndex afterIndex)).index.val) := raw
          _ = outer.length + (before.length + (1 + afterIndex.val)) :=
            congrArg (fun index => outer.length + (before.length + index))
              lifted
          _ = outer.length + localIndex.val := by
            simp only [afterIndex]
            omega
      have transferred := (validity.retained commonWire).rooted (by
        rw [indexEq]
        exact sourceRoot)
      rw [indexEq] at transferred
      exact transferred

theorem SupportParallelSelectedValidity.root
    (outer before after arguments : List Sig)
    {source target : Region
      (outer ++ (before ++ .rel arguments :: after))}
    (validity : SupportParallelSelectedValidity
      (Transform.Frame.replace outer before after [] arguments).sourceKeep
      (Transform.Frame.replace outer before after [] arguments).sourceKeep
      (Transform.Frame.replace outer before after [] arguments).selected
      (Transform.Frame.replace outer before after [] arguments).selected
      source target) :
    SupportParallelRetainedValidity (WireEquiv.refl outer).toRenaming
      (WireEquiv.refl outer).toRenaming
      (Region.adjoinAt (before ++ .rel arguments :: after) .nil source)
      (Region.adjoinAt (before ++ .rel arguments :: after) .nil target) := by
  let locals := before ++ .rel arguments :: after
  let frame := Transform.Frame.replace outer before after [] arguments
  constructor
  · intro sourceCanonical
    exact supportParallelRootSelectedAdjoinCanonical outer before after
      arguments sourceCanonical validity
  · intro signature wire
    change SupportParallelIncidenceScope
      ((Region.adjoinAt (before ++ .rel arguments :: after) .nil source
        ).incidencePaths wire.index.val)
      ((Region.adjoinAt (before ++ .rel arguments :: after) .nil target
        ).incidencePaths wire.index.val)
    let commonWire := wire.appendLeft (before ++ after)
    let actualWire := wire.appendLeft locals
    have sourcePaths := Region.incidencePaths_adjoinAt_nil source actualWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil target actualWire
    rw [show wire.index.val = actualWire.index.val by simp [actualWire],
      sourcePaths, targetPaths]
    simpa [frame, commonWire, actualWire, WireEquiv.refl,
      Transform.Frame.replace, Transform.Frame.keep] using
        validity.retained commonWire

/-- A nonempty item sequence is derivable by recursively deriving its head
and tail and joining their support binders with ParallelShape. -/
theorem supportParallelDerives
    {wires : List Sig} (materialHead : Item wires)
    (materialTail : ItemSeq wires)
    (materialHeadIH : SupportDerives (Region.singleton materialHead))
    (materialTailIH : SupportDerives (Region.ofItems materialTail)) :
    SupportDerives (Region.ofItems (.cons materialHead materialTail)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence request
  have materialPartsCanonical :
      ((Region.singleton materialHead).conjoin
        (Region.ofItems materialTail)).Canonical :=
    (RegionIso.ofEq
      (Region.singleton_conjoin_ofItems materialHead materialTail)
      ).canonical_iff.mpr materialCanonical
  have canonicalParts :=
    (Region.Canonical.conjoin_iff (Region.singleton materialHead)
      (Region.ofItems materialTail)).mp materialPartsCanonical
  have headCanonical := canonicalParts.1
  have tailCanonical := canonicalParts.2
  let oldLocals := structuralBefore ++ structuralAfter
  let sourceLocals := structuralBefore ++ .rel wires :: structuralAfter
  let splitLocals := structuralBefore ++
    .rel wires :: .rel wires :: structuralAfter
  let common := structuralOuter ++ oldLocals
  let frame := Content.Parallel.rootFrame structuralOuter structuralBefore
    structuralAfter wires
  let data := (Content.Parallel.firstHead structuralOuter structuralBefore
      structuralAfter wires,
    Content.Parallel.secondHead structuralOuter structuralBefore
      structuralAfter wires)
  let frames := supportParallelRootFrames structuralOuter structuralBefore
    structuralAfter wires
  have frameInvariant : Transform.RetainedIndexInvariant frame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have headInvariant : Transform.RetainedIndexInvariant frames.head := by
    dsimp only [frames, supportParallelRootFrames]
    exact Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have tailInvariant : Transform.RetainedIndexInvariant frames.tail := by
    dsimp only [frames, supportParallelRootFrames]
    exact Transform.RetainedIndexInvariant.replace _ _ _ _ _
  obtain ⟨edit, splitItems, headResult, tailItems, tailResult,
      headEvidence, tailEvidence, ⟨editIso⟩, headBridge, resultBridge,
      splitValidity, sourceTailValidity, tailHeadValidity, resultValidity⟩ :=
    supportParallelItemsFactor materialHead materialTail materialCanonical
      headCanonical tailCanonical frames frameInvariant headInvariant
        tailInvariant (by
          simpa only [frame, data, Content.Parallel.rootFrame,
            Content.Parallel.firstHead, Content.Parallel.secondHead] using
              evidence)
  let originalPending : Region structuralOuter := .mk sourceLocals items
  let splitPending : Region structuralOuter := .mk splitLocals splitItems
  let tailPending : Region structuralOuter := .mk sourceLocals tailItems
  let fullInstantiated : Region structuralOuter :=
    Region.adjoinAt oldLocals .nil result
  let headInstantiated : Region structuralOuter :=
    Region.adjoinAt sourceLocals .nil headResult
  let tailInstantiated : Region structuralOuter :=
    Region.adjoinAt oldLocals .nil tailResult
  have fullLocalCanonical : fullInstantiated.Canonical :=
    request.occurrence.context.holeCanonical fullInstantiated
      (by simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical)
  have resultMaterialCanonical : result.Canonical :=
    Region.Canonical.material_of_adjoinAt oldLocals .nil result
      (by simpa only [fullInstantiated] using fullLocalCanonical)
  have tailResultMaterialCanonical : tailResult.Canonical :=
    resultValidity.canonical resultMaterialCanonical
  have tailInstantiatedLocalCanonical : tailInstantiated.Canonical := by
    apply Region.Canonical.adjoinAt_of_material_roots oldLocals .nil
      tailResult True.intro tailResultMaterialCanonical
    intro localIndex
    let oldWire : Var oldLocals (oldLocals.get localIndex) :=
      Var.ofIndex localIndex
    let commonWire := Var.appendRight structuralOuter oldWire
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil result
        fullLocalCanonical localIndex
    have commonIndex : commonWire.index.val =
        structuralOuter.length + localIndex.val := by
      simp [commonWire, oldWire]
    have sourceRoot' : RegionPath.RootedTwo
        (result.incidencePaths commonWire.index.val) := by
      rw [commonIndex]
      exact sourceRoot
    have targetRoot := (resultValidity.retained commonWire).rooted (by
      simpa [WireEquiv.refl] using sourceRoot')
    simpa [tailInstantiated, commonWire, oldWire] using targetRoot
  have instantiatedNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      fullInstantiated.incidencePaths wire.index.val ≠ [] ↔
        tailInstantiated.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    let commonWire := wire.appendLeft oldLocals
    have scope := resultValidity.retained commonWire
    have sourcePaths := Region.incidencePaths_adjoinAt_nil result commonWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil tailResult commonWire
    change
      (Region.adjoinAt oldLocals .nil result).incidencePaths
          wire.index.val ≠ [] ↔
        (Region.adjoinAt oldLocals .nil tailResult).incidencePaths
          wire.index.val ≠ []
    rw [show wire.index.val = commonWire.index.val by simp [commonWire],
      sourcePaths, targetPaths]
    simpa [commonWire] using scope.nonempty
  have tailInstantiatedValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    fullInstantiated tailInstantiated
    (by simpa only [fullInstantiated, oldLocals] using
      request.instantiatedCanonical)
    (by
      intro signature wire
      simpa only [fullInstantiated, oldLocals] using
        request.instantiatedExternalTwoEnded wire)
    tailInstantiatedLocalCanonical instantiatedNonempty
  have originalLocalCanonical : originalPending.Canonical :=
    request.occurrence.context.holeCanonical originalPending
      (by simpa only [originalPending, sourceLocals] using
        request.pendingCanonical)
  have originalMaterialCanonical : (Region.ofItems items).Canonical := by
    have adjoinedCanonical :
        (Region.adjoinAt sourceLocals .nil
          (Region.ofItems items)).Canonical :=
      (RegionIso.adjoinAtOfItems sourceLocals items).canonical_iff.mpr
        originalLocalCanonical
    exact Region.Canonical.material_of_adjoinAt sourceLocals .nil
      (Region.ofItems items) adjoinedCanonical
  have rootSourceTailValidity : SupportParallelSelectedValidity
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).sourceKeep
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).sourceKeep
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).selected
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).selected
      (Region.ofItems items) (Region.ofItems tailItems) := by
    simpa [frame, frames, supportParallelRootFrames,
      Content.Parallel.rootFrame] using sourceTailValidity
  have originalAdjoinedCanonical :
      (Region.adjoinAt sourceLocals .nil (Region.ofItems items)).Canonical :=
    (RegionIso.adjoinAtOfItems sourceLocals items).canonical_iff.mpr
      originalLocalCanonical
  have tailRootValidity := rootSourceTailValidity.root structuralOuter
    structuralBefore structuralAfter wires
  have tailAdjoinedCanonical :
      (Region.adjoinAt sourceLocals .nil
        (Region.ofItems tailItems)).Canonical := by
    exact tailRootValidity.canonical (by
      simpa only [sourceLocals] using originalAdjoinedCanonical)
  have tailLocalCanonical : tailPending.Canonical :=
    (RegionIso.adjoinAtOfItems sourceLocals tailItems).canonical_iff.mp
      tailAdjoinedCanonical
  have originalTailNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      originalPending.incidencePaths wire.index.val ≠ [] ↔
        tailPending.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have scope := tailRootValidity.retained wire
    change SupportParallelIncidenceScope
      ((Region.adjoinAt sourceLocals .nil
        (Region.ofItems items)).incidencePaths wire.index.val)
      ((Region.adjoinAt sourceLocals .nil
        (Region.ofItems tailItems)).incidencePaths wire.index.val) at scope
    let actualWire := wire.appendLeft sourceLocals
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems items) actualWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems tailItems) actualWire
    rw [show wire.index.val = actualWire.index.val by simp [actualWire],
      sourcePaths, targetPaths] at scope
    rw [Region.incidencePaths_ofItems items actualWire,
      Region.incidencePaths_ofItems tailItems actualWire] at scope
    change items.incidencePaths wire.index.val 0 ≠ [] ↔
      tailItems.incidencePaths wire.index.val 0 ≠ []
    simpa [actualWire] using scope.nonempty
  have tailPendingValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    originalPending tailPending
    (by simpa only [originalPending, sourceLocals] using
      request.pendingCanonical)
    (by
      intro signature wire
      simpa only [originalPending, sourceLocals] using
        request.pendingExternalTwoEnded wire)
    tailLocalCanonical originalTailNonempty
  have splitMaterialCanonical : (Region.ofItems splitItems).Canonical :=
    splitValidity.canonical originalMaterialCanonical
  have splitLocalCanonical : splitPending.Canonical := by
    let presentation := RegionIso.adjoinAtOfItems splitLocals splitItems
    apply presentation.canonical_iff.mp
    apply Region.Canonical.adjoinAt_of_material_roots splitLocals .nil
      (Region.ofItems splitItems) True.intro splitMaterialCanonical
    intro localIndex
    by_cases beforeCase : localIndex.val < structuralBefore.length
    · let beforeIndex : Fin structuralBefore.length :=
        ⟨localIndex.val, beforeCase⟩
      let commonWire := Var.appendRight structuralOuter
        ((Var.ofIndex beforeIndex).appendLeft structuralAfter)
      let sourceIndex : Fin sourceLocals.length :=
        ⟨localIndex.val, by simp [sourceLocals]; omega⟩
      have sourceRoot := originalLocalCanonical.1 sourceIndex
      have materialRoot : RegionPath.RootedTwo
          ((Region.ofItems items).incidencePaths
            (frame.sourceKeep commonWire).index.val) := by
        rw [Region.incidencePaths_ofItems]
        simpa [frame, commonWire, beforeIndex, sourceIndex, sourceLocals,
          Content.Parallel.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep] using sourceRoot
      have targetRoot := (splitValidity.retained commonWire).rooted materialRoot
      simpa [frame, commonWire, beforeIndex, splitLocals,
        Content.Parallel.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep] using targetRoot
    · by_cases firstCase : localIndex.val = structuralBefore.length
      · let sourceIndex : Fin sourceLocals.length :=
          ⟨structuralBefore.length, by simp [sourceLocals]⟩
        have sourceRoot := originalLocalCanonical.1 sourceIndex
        have materialRoot : RegionPath.RootedTwo
            ((Region.ofItems items).incidencePaths frame.selected.index.val) := by
          rw [Region.incidencePaths_ofItems]
          simpa [frame, sourceIndex, sourceLocals,
            Content.Parallel.rootFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using sourceRoot
        have targetRoot := splitValidity.first.rooted materialRoot
        simpa [data, firstCase, splitLocals, Content.Parallel.firstHead,
          Transform.Frame.insertedHead] using targetRoot
      · by_cases secondCase :
            localIndex.val = structuralBefore.length + 1
        · let sourceIndex : Fin sourceLocals.length :=
            ⟨structuralBefore.length, by simp [sourceLocals]⟩
          have sourceRoot := originalLocalCanonical.1 sourceIndex
          have materialRoot : RegionPath.RootedTwo
              ((Region.ofItems items).incidencePaths frame.selected.index.val) := by
            rw [Region.incidencePaths_ofItems]
            simpa [frame, sourceIndex, sourceLocals,
              Content.Parallel.rootFrame, Transform.Frame.replace,
              Transform.Frame.insertedHead] using sourceRoot
          have targetRoot := splitValidity.second.rooted materialRoot
          simpa [data, secondCase, splitLocals,
            Content.Parallel.secondHead, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep,
            Transform.Frame.insertedHead] using targetRoot
        · have afterBound :
              localIndex.val - structuralBefore.length - 2 <
                structuralAfter.length := by
            have bound := localIndex.isLt
            simp [splitLocals] at bound
            omega
          let afterIndex : Fin structuralAfter.length :=
            ⟨localIndex.val - structuralBefore.length - 2, afterBound⟩
          let commonWire := Var.appendRight structuralOuter
            (Var.appendRight structuralBefore (Var.ofIndex afterIndex))
          let sourceIndex : Fin sourceLocals.length :=
            ⟨structuralBefore.length + 1 + afterIndex.val,
              by simp [sourceLocals]; omega⟩
          have sourceRoot := originalLocalCanonical.1 sourceIndex
          have sourceLifted :
              (Var.appendRight [.rel wires]
                (Var.ofIndex afterIndex)).index.val =
                  1 + afterIndex.val := by
            simpa using (Var.index_appendRight [.rel wires]
              (Var.ofIndex afterIndex))
          have sourceIndexEq :
              (frame.sourceKeep commonWire).index.val =
                structuralOuter.length + sourceIndex.val := by
            simp [frame, commonWire, sourceIndex,
              Content.Parallel.rootFrame, Transform.Frame.replace,
              Transform.Frame.keep, Transform.Frame.localKeep]
            calc
              structuralBefore.length +
                  (Var.appendRight [.rel wires]
                    (Var.ofIndex afterIndex)).index.val =
                structuralBefore.length + (1 + afterIndex.val) :=
                  congrArg (fun index => structuralBefore.length + index)
                    sourceLifted
              _ = structuralBefore.length + 1 + afterIndex.val := by omega
          have materialRoot : RegionPath.RootedTwo
              ((Region.ofItems items).incidencePaths
                (frame.sourceKeep commonWire).index.val) := by
            rw [Region.incidencePaths_ofItems, sourceIndexEq]
            exact sourceRoot
          have targetRoot :=
            (splitValidity.retained commonWire).rooted materialRoot
          have targetLifted :
              (Var.appendRight [.rel wires, .rel wires]
                (Var.ofIndex afterIndex)).index.val =
                  2 + afterIndex.val := by
            simpa using (Var.index_appendRight
              [.rel wires, .rel wires] (Var.ofIndex afterIndex))
          have targetIndexEq :
              (frame.targetKeep commonWire).index.val =
                structuralOuter.length + localIndex.val := by
            simp [frame, commonWire, afterIndex, splitLocals,
              Content.Parallel.rootFrame, Transform.Frame.replace,
              Transform.Frame.keep, Transform.Frame.localKeep]
            calc
              structuralBefore.length +
                  (Var.appendRight [.rel wires, .rel wires]
                    (Var.ofIndex afterIndex)).index.val =
                structuralBefore.length + (2 + afterIndex.val) :=
                  congrArg (fun index => structuralBefore.length + index)
                    targetLifted
              _ = localIndex.val := by simp only [afterIndex]; omega
          rw [targetIndexEq] at targetRoot
          exact targetRoot
  have originalSplitNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      originalPending.incidencePaths wire.index.val ≠ [] ↔
        splitPending.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    let commonWire := wire.appendLeft oldLocals
    have scope := splitValidity.retained commonWire
    have scope' : SupportParallelIncidenceScope
        ((Region.ofItems items).incidencePaths wire.index.val)
        ((Region.ofItems splitItems).incidencePaths wire.index.val) := by
      simpa [commonWire, oldLocals, frame, Content.Parallel.rootFrame,
        Transform.Frame.replace, Transform.Frame.keep] using scope
    let sourceWire := wire.appendLeft sourceLocals
    let targetWire := wire.appendLeft splitLocals
    have sourcePaths' :
        (Region.ofItems items).incidencePaths wire.index.val =
          items.incidencePaths wire.index.val 0 := by
      rw [show wire.index.val = sourceWire.index.val by simp [sourceWire]]
      exact Region.incidencePaths_ofItems items sourceWire
    have targetPaths' :
        (Region.ofItems splitItems).incidencePaths wire.index.val =
          splitItems.incidencePaths wire.index.val 0 := by
      rw [show wire.index.val = targetWire.index.val by simp [targetWire]]
      exact Region.incidencePaths_ofItems splitItems targetWire
    rw [sourcePaths', targetPaths'] at scope'
    change items.incidencePaths wire.index.val 0 ≠ [] ↔
      splitItems.incidencePaths wire.index.val 0 ≠ []
    exact scope'.nonempty
  have splitPendingValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    originalPending splitPending
    (by simpa only [originalPending, sourceLocals] using
      request.pendingCanonical)
    (by
      intro signature wire
      simpa only [originalPending, sourceLocals] using
        request.pendingExternalTwoEnded wire)
    splitLocalCanonical originalSplitNonempty
  have rootTailHeadValidity : SupportParallelSelectedValidity
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).sourceKeep
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).sourceKeep
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).selected
      (Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [] wires).selected
      (Region.ofItems tailItems) headResult := by
    simpa [frames, supportParallelRootFrames] using tailHeadValidity
  have headRootValidity := rootTailHeadValidity.root structuralOuter
    structuralBefore structuralAfter wires
  have headInstantiatedLocalCanonical : headInstantiated.Canonical := by
    exact headRootValidity.canonical (by
      simpa only [sourceLocals] using tailAdjoinedCanonical)
  have tailHeadNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      tailPending.incidencePaths wire.index.val ≠ [] ↔
        headInstantiated.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have scope := headRootValidity.retained wire
    change SupportParallelIncidenceScope
      ((Region.adjoinAt sourceLocals .nil
        (Region.ofItems tailItems)).incidencePaths wire.index.val)
      (headInstantiated.incidencePaths wire.index.val) at scope
    let actualWire := wire.appendLeft sourceLocals
    have sourcePaths := Region.incidencePaths_adjoinAt_nil
      (Region.ofItems tailItems) actualWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil
      headResult actualWire
    rw [show wire.index.val = actualWire.index.val by simp [actualWire],
      sourcePaths, targetPaths] at scope
    rw [Region.incidencePaths_ofItems tailItems actualWire] at scope
    have targetPaths' :
        headInstantiated.incidencePaths wire.index.val =
          headResult.incidencePaths wire.index.val := by
      simpa [headInstantiated, actualWire] using targetPaths
    rw [targetPaths']
    change tailItems.incidencePaths wire.index.val 0 ≠ [] ↔
      headResult.incidencePaths wire.index.val ≠ []
    simpa [actualWire] using scope.nonempty
  have headInstantiatedValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    tailPending headInstantiated tailPendingValidity.1
    tailPendingValidity.2 headInstantiatedLocalCanonical tailHeadNonempty
  obtain ⟨tailInstCanonical, tailInstExternal⟩ :=
    tailInstantiatedValidity
  obtain ⟨tailPendingCanonical, tailPendingExternal⟩ :=
    tailPendingValidity
  obtain ⟨headInstCanonical, headInstExternal⟩ :=
    headInstantiatedValidity
  obtain ⟨splitPendingCanonical, splitPendingExternal⟩ :=
    splitPendingValidity
  have polarityEq : request.occurrence.context.polarity = request.polarity :=
    request.continuation.1
  let headRequest : Telescope.Request headInstantiated splitPending := {
    boundary := request.boundary
    source := request.occurrence.interface.withBody
      (request.occurrence.context.fill
        (polaritySource request.polarity headInstantiated splitPending))
      (polaritySource_property request.polarity
        (fun region => (request.occurrence.context.fill region).Canonical)
        headInstantiated splitPending headInstCanonical splitPendingCanonical)
      (polaritySource_property request.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill region))
        headInstantiated splitPending headInstExternal splitPendingExternal)
    endpoint := splitPending
    polarity := request.polarity
    occurrence := exactOccurrence request.occurrence.interface
      request.occurrence.context
      (polaritySource request.polarity headInstantiated splitPending)
      (polaritySource_property request.polarity
        (fun region => (request.occurrence.context.fill region).Canonical)
        headInstantiated splitPending headInstCanonical splitPendingCanonical)
      (polaritySource_property request.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill region))
        headInstantiated splitPending headInstExternal splitPendingExternal)
    instantiatedCanonical := headInstCanonical
    instantiatedExternalTwoEnded := headInstExternal
    pendingCanonical := splitPendingCanonical
    pendingExternalTwoEnded := splitPendingExternal
    endpointCanonical := splitPendingCanonical
    endpointExternalTwoEnded := splitPendingExternal
    continuation := Telescope.refl request.polarity
      request.occurrence.interface request.occurrence.context
      splitPendingCanonical splitPendingExternal polarityEq
  }
  have headCompiled := materialHeadIH headCanonical headEvidence headRequest
  have headTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      headInstantiated splitPending headInstCanonical headInstExternal
      splitPendingCanonical splitPendingExternal := by
    exact Telescope.StrictDerives.toTelescope request.polarity
      request.occurrence.interface request.occurrence.context
      headInstCanonical headInstExternal splitPendingCanonical
      splitPendingExternal polarityEq
      (by simpa only [headRequest, Telescope.Request.Result] using headCompiled)
  have tailHeadHosted : HostedStrict tailPending headInstantiated := by
    have lifted := HostedStrict.adjoinAt sourceLocals
      (Region.ofItems tailItems) headResult headBridge.symm
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems sourceLocals tailItems).symm
      (RegionIso.refl _) lifted
  have tailHeadTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      tailPending headInstantiated tailPendingCanonical tailPendingExternal
      headInstCanonical headInstExternal :=
    telescopeOfHostedExact tailHeadHosted request.polarity
      request.occurrence.interface request.occurrence.context
      tailPendingCanonical tailPendingExternal headInstCanonical
      headInstExternal polarityEq
  have tailContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      tailPending splitPending tailPendingCanonical tailPendingExternal
      splitPendingCanonical splitPendingExternal :=
    telescopeTrans tailHeadTelescope headTelescope
  let tailRequest : Telescope.Request tailInstantiated tailPending := {
    boundary := request.boundary
    source := request.occurrence.interface.withBody
      (request.occurrence.context.fill
        (polaritySource request.polarity tailInstantiated splitPending))
      (polaritySource_property request.polarity
        (fun region => (request.occurrence.context.fill region).Canonical)
        tailInstantiated splitPending tailInstCanonical splitPendingCanonical)
      (polaritySource_property request.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill region))
        tailInstantiated splitPending tailInstExternal splitPendingExternal)
    endpoint := splitPending
    polarity := request.polarity
    occurrence := exactOccurrence request.occurrence.interface
      request.occurrence.context
      (polaritySource request.polarity tailInstantiated splitPending)
      (polaritySource_property request.polarity
        (fun region => (request.occurrence.context.fill region).Canonical)
        tailInstantiated splitPending tailInstCanonical splitPendingCanonical)
      (polaritySource_property request.polarity
        (fun region => OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill region))
        tailInstantiated splitPending tailInstExternal splitPendingExternal)
    instantiatedCanonical := tailInstCanonical
    instantiatedExternalTwoEnded := tailInstExternal
    pendingCanonical := tailPendingCanonical
    pendingExternalTwoEnded := tailPendingExternal
    endpointCanonical := splitPendingCanonical
    endpointExternalTwoEnded := splitPendingExternal
    continuation := tailContinuation
  }
  have tailCompiled := materialTailIH tailCanonical tailEvidence tailRequest
  have tailTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      tailInstantiated splitPending tailInstCanonical tailInstExternal
      splitPendingCanonical splitPendingExternal := by
    exact Telescope.StrictDerives.toTelescope request.polarity
      request.occurrence.interface request.occurrence.context
      tailInstCanonical tailInstExternal splitPendingCanonical
      splitPendingExternal polarityEq
      (by simpa only [tailRequest, Telescope.Request.Result] using tailCompiled)
  have resultHosted : HostedStrict fullInstantiated tailInstantiated := by
    simpa only [fullInstantiated, tailInstantiated] using
      HostedStrict.adjoinAt oldLocals result tailResult resultBridge
  have resultTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      fullInstantiated tailInstantiated request.instantiatedCanonical
      request.instantiatedExternalTwoEnded tailInstCanonical
      tailInstExternal :=
    telescopeOfHostedExact resultHosted request.polarity
      request.occurrence.interface request.occurrence.context
      request.instantiatedCanonical request.instantiatedExternalTwoEnded
      tailInstCanonical tailInstExternal polarityEq
  have preparation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      fullInstantiated splitPending request.instantiatedCanonical
      request.instantiatedExternalTwoEnded splitPendingCanonical
      splitPendingExternal := telescopeTrans resultTelescope tailTelescope
  let description : Content.Parallel.Split.Description structuralOuter := {
    arguments := wires
    before := structuralBefore
    after := structuralAfter
    items := items
    itemsEdit := edit
  }
  let preparedIso : RegionIso (WireEquiv.refl structuralOuter)
      splitPending description.target :=
    (RegionIso.adjoinAtOfItems splitLocals splitItems).symm.trans
      (RegionIso.adjoinAt splitLocals .nil editIso.symm)
  have rawPreparedValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context
    splitPending description.target splitPendingCanonical
    splitPendingExternal (ScopePreservation.ofIso preparedIso)
  have pendingEq : originalPending = description.source := by rfl
  let branch : request.Branch splitPending := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := symmetric Content.Parallel.Local
    inject := fun step => Step.parallelShape step
    preparedCanonical := splitPendingCanonical
    preparedExternalTwoEnded := splitPendingExternal
    rawPreparedCanonical := rawPreparedValidity.1
    rawPreparedExternalTwoEnded := rawPreparedValidity.2
    rawPendingCanonical := by
      rw [← pendingEq]
      exact request.pendingCanonical
    rawPendingExternalTwoEnded := by
      intro signature wire
      rw [← pendingEq]
      exact request.pendingExternalTwoEnded wire
    preparedIso := preparedIso
    pendingIso := RegionIso.ofEq pendingEq
    localStep := Or.inr (.split (.mk description))
    preparation := preparation
  }
  exact branch.derive

end Structural

end VisualProof.Rule.Completeness.Comprehension
