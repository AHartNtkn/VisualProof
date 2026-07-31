import VisualProof.Rule.WirePrimitive.Content

namespace VisualProof

#check ConcreteWirePrimitive.AppliedSite.replacement_denotation
#check ConcreteWirePrimitive.AppliedSite.universal_scope_transport
#check ConcreteWirePrimitive.AppliedSite.universal_outer_transport
#check WirePrimitive.AppliedSiteErasure.Result.inductionOn
#check WirePrimitive.AppliedSiteErasure.Result.universal_scope_transport
#check WirePrimitive.AppliedSiteErasure.Result.universal_outer_transport

namespace WirePrimitive

namespace ContentFixtures

open ConcreteWirePrimitive

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def contentError? {α : Type} :
    Except ContentError α → Option ContentError
  | .error error => some error
  | .ok _ => none

private def ruleError? {α : Type} :
    Except WireContentError α → Option WireContentError
  | .error error => some error
  | .ok _ => none

/-!
An endpoint-free unary relation is spawned at one positive and one negative
site.  The ordered argument wire is root-scoped and visible at both.
-/
private def spawnSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .identity 0 .iota 2
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota]
          scope := 0
          endpoints := [] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 0
          endpoints :=
            [⟨0, .identity 0⟩, ⟨0, .identity 1⟩] }

private theorem spawnSourceRaw_wellFormed :
    spawnSourceRaw.WellFormed [] := by
  native_decide

private def spawnSource : CheckedDiagram [] :=
  ⟨spawnSourceRaw, spawnSourceRaw_wellFormed⟩

private def spawnSites :
    List (EndSite spawnSource (idx 0)) :=
  [⟨idx 0, [idx 1]⟩, ⟨idx 1, [idx 1]⟩]

private def spawned :
    EndsSpawnResult spawnSource (idx 0) spawnSites :=
  (spawnEnds spawnSource (idx 0) spawnSites).toOption.get
    (by native_decide)

example :
    (spawned.checked.val.nodeCount,
      (spawned.checked.val.wires (idx 0)).endpoints.length,
      (spawned.checked.val.wires (idx 1)).endpoints.length) =
      (3, 2, 4) := by
  native_decide

example :
    (spawned.checked.val.nodes (idx 1),
      spawned.checked.val.nodes (idx 2)) =
      (.atom (idx 0) [.iota], .atom (idx 1) [.iota]) := by
  native_decide

example :
    ConcreteIso spawned.inverse.checked.val spawnSource.val :=
  spawned.inverseIso

example :
    spawned.inverse.checkCommonCore.isSome = true := by
  native_decide

example :
    spawned.inverse.checkSiteLedger.isSome = true := by
  native_decide

private def deleteLedger :=
  spawned.inverse.checkSiteLedger.get (by native_decide)

example :
    deleteLedger.sourceScope.frame.context.cutDepth =
      deleteLedger.targetScope.frame.context.cutDepth :=
  deleteLedger.cutDepth

private def deletionTrace :=
  AppliedSiteErasure.check spawned.checked spawned.inverseWire
    |>.get (by native_decide)

example :
    (deletionTrace.target.val.wires
      deletionTrace.targetWire).endpoints = [] :=
  deletionTrace.target_empty

example :
    (ConcreteIsoSearch.findConcreteIso? deletionTrace.target.val
      spawned.inverse.checked.val).isSome = true := by
  native_decide

/-! Cut wrapping and exact absorption act on both mixed-parity sites. -/
private def wrapped :
    CutWrapResult spawned.checked spawned.inverseWire :=
  (cutWrap spawned.checked spawned.inverseWire).toOption.get
    (by native_decide)

example :
    (wrapped.checked.val.regionCount,
      wrapped.checked.val.nodeCount,
      wrapped.checked.val.wireCount,
      (wrapped.checked.val.wires wrapped.targetWire).endpoints.length) =
      (4, 3, 2, 2) := by
  native_decide

private def absorbed :
    CutAbsorbResult wrapped.checked wrapped.targetWire :=
  (cutAbsorb wrapped.checked wrapped.targetWire).toOption.get
    (by native_decide)

example :
    ConcreteIso absorbed.inverse.checked.val wrapped.checked.val :=
  absorbed.inverseIso

example :
    wrapped.checkCommonCore.isSome = true := by
  native_decide

example :
    wrapped.checkSiteLedger.isSome = true := by
  native_decide

private def wrappedLedger :=
  wrapped.checkSiteLedger.get (by native_decide)

example :
    wrappedLedger.sourceScope.frame.context.cutDepth =
      wrappedLedger.targetScope.frame.context.cutDepth :=
  wrappedLedger.cutDepth

example :
    (ConcreteIsoSearch.findConcreteIso?
      absorbed.checked.val spawned.checked.val).isSome = true := by
  native_decide

/-! Parallel split creates two exhaustive wires; fusion consumes exact pairs. -/
private def split :
    ParallelSplitResult spawned.checked spawned.inverseWire :=
  (parallelSplit spawned.checked spawned.inverseWire).toOption.get
    (by native_decide)

example :
    ((split.checked.val.wires split.firstWire).endpoints.length,
      (split.checked.val.wires split.secondWire).endpoints.length,
      split.checked.val.nodeCount,
      split.checked.val.wireCount) =
      (2, 2, 5, 3) := by
  native_decide

private def fused :
    ParallelFuseResult split.checked split.firstWire split.secondWire :=
  (parallelFuse split.checked split.firstWire split.secondWire).toOption.get
    (by native_decide)

example :
    ConcreteIso fused.inverse.checked.val split.checked.val :=
  fused.inverseIso

example :
    split.checkCommonCore.isSome = true := by
  native_decide

example :
    split.checkSiteLedger.isSome = true := by
  native_decide

private def splitLedger :=
  split.checkSiteLedger.get (by native_decide)

example :
    splitLedger.sourceScope.frame.context.cutDepth =
      splitLedger.firstScope.frame.context.cutDepth :=
  splitLedger.firstCutDepth

example :
    splitLedger.sourceScope.frame.context.cutDepth =
      splitLedger.secondScope.frame.context.cutDepth :=
  splitLedger.secondCutDepth

example :
    (ConcreteIsoSearch.findConcreteIso?
      fused.checked.val spawned.checked.val).isSome = true := by
  native_decide

example :
    contentError?
      (parallelFuse split.checked split.firstWire split.firstWire) =
        some .sameWire := by
  native_decide

/-! Endpoint-free equivalences remain executable and exhaustive at zero sites. -/
private def emptyWrapped :
    CutWrapResult spawnSource (idx 0) :=
  (cutWrap spawnSource (idx 0)).toOption.get (by native_decide)

private def emptySplit :
    ParallelSplitResult spawnSource (idx 0) :=
  (parallelSplit spawnSource (idx 0)).toOption.get (by native_decide)

example :
    ((emptyWrapped.checked.val.wires emptyWrapped.targetWire).endpoints,
      (emptySplit.checked.val.wires emptySplit.firstWire).endpoints,
      (emptySplit.checked.val.wires emptySplit.secondWire).endpoints) =
      ([], [], []) := by
  native_decide

example :
    emptyWrapped.checkCommonCore.isSome = true := by
  native_decide

example :
    emptySplit.checkCommonCore.isSome = true := by
  native_decide

example :
    emptyWrapped.checkSiteLedger.isSome = true := by
  native_decide

example :
    emptySplit.checkSiteLedger.isSome = true := by
  native_decide

/-! Empty site lists and non-head endpoints are refused. -/
example :
    contentError? (spawnEnds spawnSource (idx 0) []) =
      some .emptySites := by
  native_decide

private def nonHeadRaw : ConcreteDiagram 0 where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := fun _ => .atom 0 [.rel []]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel []
          scope := 0
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨1, _⟩ =>
        { sig := .rel [.rel []]
          scope := 0
          endpoints := [⟨0, .head⟩] }

private theorem nonHeadRaw_wellFormed :
    nonHeadRaw.WellFormed [] := by
  native_decide

private def nonHead : CheckedDiagram [] :=
  ⟨nonHeadRaw, nonHeadRaw_wellFormed⟩

example :
    contentError? (deleteEnds nonHead (idx 0)) =
      some .nonAppliedEndpoint := by
  native_decide

/-! Public receipts retain exact tags, targets, and checked polarity gates. -/

example (applied : AppliedCutWrap source wire) :
    applied.tag = .cutWrap := rfl

example (applied : AppliedCutAbsorb source wire) :
    applied.tag = .cutAbsorb := rfl

example (applied : AppliedParallelSplit source wire) :
    applied.tag = .parallelSplit := rfl

example (applied : AppliedParallelFuse source left right) :
    applied.tag = .parallelFuse := rfl

private def negativeRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 0
  wireCount := 1
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := nofun
  wires := fun _ =>
    { sig := .rel []
      scope := 1
      endpoints := [] }

private theorem negativeRaw_wellFormed :
    negativeRaw.WellFormed [] := by
  native_decide

private def negativeSource : CheckedDiagram [] :=
  ⟨negativeRaw, negativeRaw_wellFormed⟩

private def negativeSites :
    List (EndSite negativeSource (idx 0)) :=
  [⟨idx 1, []⟩]

example :
    ruleError?
      (applyEndsSpawn negativeSource (idx 0) negativeSites .forward) =
        some .endsSpawnRequiresPositive := by
  native_decide

example (applied : AppliedEndsSpawn source orientation wire sites) :
    applied.tag = .endsSpawn := rfl

private def negativeConcreteSpawn :=
  (spawnEnds negativeSource (idx 0) negativeSites)
    |>.toOption.get (by native_decide)

example :
    ruleError?
      (applyEndsDelete negativeConcreteSpawn.checked
        negativeConcreteSpawn.inverseWire .backward) =
        some .endsDeleteBackwardRequiresPositive := by
  native_decide

example (applied : AppliedEndsDelete source orientation wire) :
    applied.tag = .endsDelete := rfl

example :
    (applyEndsSpawn negativeSource (idx 0) negativeSites .backward).isOk =
      true := by
  native_decide

example :
    (applyEndsDelete negativeConcreteSpawn.checked
      negativeConcreteSpawn.inverseWire .forward).isOk = true := by
  native_decide

example :
    ruleError?
      (applyEndsDelete spawned.checked spawned.inverseWire .forward) =
        some .endsDeleteRequiresNegative := by
  native_decide

example :
    ruleError?
      (applyEndsSpawn spawnSource (idx 0) spawnSites .backward) =
        some .endsSpawnBackwardRequiresNegative := by
  native_decide

end ContentFixtures

end WirePrimitive

end VisualProof
