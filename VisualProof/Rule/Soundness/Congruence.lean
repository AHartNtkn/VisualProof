import VisualProof.Rule.Soundness.WireJoin

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace CongruenceSoundness

private theorem list_get_cast {left right : List α}
    (equality : left = right) (index : Fin right.length) :
    left.get (Fin.cast (congrArg List.length equality).symm index) =
      right.get index := by
  subst right
  rfl

noncomputable def quotientEnvironment
    (map : Fin source → Fin target)
    (surjective : Function.Surjective map)
    (sourceEnv : Fin source → D) :
    Fin target → D :=
  fun targetIndex => sourceEnv (Classical.choose (surjective targetIndex))

theorem quotientEnvironment_agrees
    (map : Fin source → Fin target)
    (surjective : Function.Surjective map)
    (sourceEnv : Fin source → D)
    (fiberConstant : ∀ left right, map left = map right →
      sourceEnv left = sourceEnv right) :
    sourceEnv = quotientEnvironment map surjective sourceEnv ∘ map := by
  funext sourceIndex
  unfold quotientEnvironment
  exact fiberConstant sourceIndex
    (Classical.choose (surjective (map sourceIndex)))
    (Classical.choose_spec (surjective (map sourceIndex))).symm

noncomputable def localEnvironmentOfComplete
    (context : Diagram.ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (complete : Fin (context.extend region).length → D) :
    Fin (Diagram.ConcreteElaboration.exactScopeWires diagram region).length → D :=
  fun localIndex =>
    complete
      (Fin.cast
        (Diagram.ConcreteElaboration.WireContext.length_extend context
          region).symm
        (Fin.natAdd context.length localIndex))

theorem extendedEnvironment_localEnvironmentOfComplete
    (context : Diagram.ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (complete : Fin (context.extend region).length → D)
    (inherited : ∀ index,
      complete
          (Fin.cast
            (Diagram.ConcreteElaboration.WireContext.length_extend context
              region).symm
            (Fin.castAdd
              (Diagram.ConcreteElaboration.exactScopeWires diagram region).length
              index)) =
        outerEnv index) :
    Diagram.ConcreteElaboration.extendedEnvironment context region outerEnv
        (localEnvironmentOfComplete context region complete) =
      complete := by
  funext index
  let split :=
    Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend context region)
      index
  have recover :
      Fin.cast
          (Diagram.ConcreteElaboration.WireContext.length_extend context
            region).symm
          split =
        index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inheritedIndex => ?_)
    (fun localIndex => ?_) split
  · simpa [Diagram.ConcreteElaboration.extendedEnvironment,
      extendWireEnv] using (inherited inheritedIndex).symm
  · simp [Diagram.ConcreteElaboration.extendedEnvironment,
      localEnvironmentOfComplete, extendWireEnv]

theorem wireJoin_extended_fiber_constant
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (sourceContext : Diagram.ConcreteElaboration.WireContext input)
    (targetContext :
      Diagram.ConcreteElaboration.WireContext
        (WireJoinSoundness.Target input outer inner))
    (witness : WireJoinSoundness.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceExact : sourceContext.Exact region)
    (sourceEnv : Fin sourceContext.length → D)
    (joinedValues : ∀ outerIndex innerIndex,
      sourceContext.get outerIndex = outer →
      sourceContext.get innerIndex = inner →
      sourceEnv outerIndex = sourceEnv innerIndex) :
    ∀ left right, witness.indexMap left = witness.indexMap right →
      sourceEnv left = sourceEnv right := by
  intro left right mapped
  have mappedWires :
      WireJoinSoundness.wireMap input outer inner distinct
          (sourceContext.get left) =
        WireJoinSoundness.wireMap input outer inner distinct
          (sourceContext.get right) := by
    calc
      _ = targetContext.get (witness.indexMap left) := (witness.get left).symm
      _ = targetContext.get (witness.indexMap right) := congrArg _ mapped
      _ = _ := witness.get right
  rcases
      (WireJoinSoundness.wireMap_eq_iff input outer inner
        (sourceContext.get left) (sourceContext.get right) distinct).mp
        mappedWires with
    same | outerInner | innerOuter
  · have indexEq : left = right := by
      apply Fin.ext
      exact (List.getElem_inj sourceExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using same)
    rw [indexEq]
  · exact joinedValues left right outerInner.1 outerInner.2
  · exact (joinedValues right left innerOuter.2 innerOuter.1).symm

/-- At the absorbed wire's scope, a source valuation descends through the
wire quotient exactly when the retained and absorbed wire values agree. -/
theorem wireJoin_site_forward_selection
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (sourceContext : Diagram.ConcreteElaboration.WireContext input)
    (targetContext :
      Diagram.ConcreteElaboration.WireContext
        (WireJoinSoundness.Target input outer inner))
    (witness : WireJoinSoundness.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ witness.indexMap)
    (sourceLocal :
      Fin (Diagram.ConcreteElaboration.exactScopeWires input region).length → D)
    (joinedValues : ∀ outerIndex innerIndex,
      (sourceContext.extend region).get outerIndex = outer →
      (sourceContext.extend region).get innerIndex = inner →
      Diagram.ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal outerIndex =
        Diagram.ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal innerIndex) :
    ∃ targetLocal :
        Fin (Diagram.ConcreteElaboration.exactScopeWires
          (WireJoinSoundness.Target input outer inner) region).length → D,
      Diagram.ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal =
        Diagram.ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal ∘
          (witness.extend wellFormed ordered region sourceExact targetExact).indexMap := by
  let extendedWitness :=
    witness.extend wellFormed ordered region sourceExact targetExact
  let sourceComplete :=
    Diagram.ConcreteElaboration.extendedEnvironment sourceContext region
      sourceOuter sourceLocal
  have fiberConstant : ∀ left right,
      extendedWitness.indexMap left = extendedWitness.indexMap right →
        sourceComplete left = sourceComplete right :=
    wireJoin_extended_fiber_constant input outer inner distinct
      (sourceContext.extend region) (targetContext.extend region)
      extendedWitness region sourceExact sourceComplete joinedValues
  let targetComplete :=
    quotientEnvironment extendedWitness.indexMap extendedWitness.surjective
      sourceComplete
  have completeAgrees :
      sourceComplete = targetComplete ∘ extendedWitness.indexMap :=
    quotientEnvironment_agrees extendedWitness.indexMap
      extendedWitness.surjective sourceComplete fiberConstant
  have targetInherited : ∀ targetIndex,
      targetComplete
          (Fin.cast
            (Diagram.ConcreteElaboration.WireContext.length_extend targetContext
              region).symm
            (Fin.castAdd
              (Diagram.ConcreteElaboration.exactScopeWires
                (WireJoinSoundness.Target input outer inner) region).length
              targetIndex)) =
        targetOuter targetIndex := by
    intro targetIndex
    obtain ⟨sourceIndex, sourceIndexMap⟩ := witness.surjective targetIndex
    let sourceExtendedIndex : Fin (sourceContext.extend region).length :=
      Fin.cast
        (Diagram.ConcreteElaboration.WireContext.length_extend sourceContext
          region).symm
        (Fin.castAdd
          (Diagram.ConcreteElaboration.exactScopeWires input region).length
          sourceIndex)
    let targetExtendedIndex : Fin (targetContext.extend region).length :=
      Fin.cast
        (Diagram.ConcreteElaboration.WireContext.length_extend targetContext
          region).symm
        (Fin.castAdd
          (Diagram.ConcreteElaboration.exactScopeWires
            (WireJoinSoundness.Target input outer inner) region).length
          targetIndex)
    have extendedIndexMap :
        extendedWitness.indexMap sourceExtendedIndex =
          targetExtendedIndex := by
      rw [WireJoinSoundness.ContextWitness.extend_index_inherited]
      exact congrArg
        (fun index =>
          Fin.cast
            (Diagram.ConcreteElaboration.WireContext.length_extend targetContext
              region).symm
            (Fin.castAdd
              (Diagram.ConcreteElaboration.exactScopeWires
                (WireJoinSoundness.Target input outer inner) region).length
              index))
        sourceIndexMap
    have agreesAt := congrFun completeAgrees sourceExtendedIndex
    change sourceComplete sourceExtendedIndex =
      targetComplete (extendedWitness.indexMap sourceExtendedIndex) at agreesAt
    rw [extendedIndexMap] at agreesAt
    have sourceValue :
        sourceComplete sourceExtendedIndex = sourceOuter sourceIndex := by
      simp [sourceComplete, sourceExtendedIndex,
        Diagram.ConcreteElaboration.extendedEnvironment, extendWireEnv]
    change targetComplete targetExtendedIndex = targetOuter targetIndex
    calc
      targetComplete targetExtendedIndex =
          sourceComplete sourceExtendedIndex := agreesAt.symm
      _ = sourceOuter sourceIndex := sourceValue
      _ = targetOuter (witness.indexMap sourceIndex) :=
        congrFun outerAgrees sourceIndex
      _ = targetOuter targetIndex := congrArg targetOuter sourceIndexMap
  let targetLocal :=
    localEnvironmentOfComplete targetContext region targetComplete
  refine ⟨targetLocal, ?_⟩
  have targetCompleteEq :
      Diagram.ConcreteElaboration.extendedEnvironment targetContext region
          targetOuter targetLocal =
        targetComplete :=
    extendedEnvironment_localEnvironmentOfComplete targetContext region
      targetOuter targetComplete targetInherited
  rw [targetCompleteEq]
  exact completeAgrees

noncomputable def rootLocalEnvironmentOfComplete
    (ambient locals : Diagram.ConcreteElaboration.WireContext diagram)
    (complete : Fin (ambient ++ locals).length → D) :
    Fin locals.length → D :=
  fun index => complete (WireJoinSoundness.rightIndex ambient locals index)

theorem rootEnvironment_rootLocalEnvironmentOfComplete
    (ambient locals : Diagram.ConcreteElaboration.WireContext diagram)
    (outerEnv : Fin ambient.length → D)
    (complete : Fin (ambient ++ locals).length → D)
    (inherited : ∀ index,
      complete (WireJoinSoundness.leftIndex ambient locals index) =
        outerEnv index) :
    Diagram.ConcreteElaboration.rootEnvironment ambient locals outerEnv
        (rootLocalEnvironmentOfComplete ambient locals complete) =
      complete := by
  funext index
  let split : Fin (ambient.length + locals.length) :=
    Fin.cast (by simp) index
  have recover :
      Fin.cast (by simp : ambient.length + locals.length =
        (ambient ++ locals).length) split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inheritedIndex => ?_) (fun localIndex => ?_) split
  · simpa [Diagram.ConcreteElaboration.rootEnvironment,
      WireJoinSoundness.leftIndex, extendWireEnv] using
        (inherited inheritedIndex).symm
  · simp [Diagram.ConcreteElaboration.rootEnvironment,
      rootLocalEnvironmentOfComplete, WireJoinSoundness.rightIndex,
      extendWireEnv]

theorem wireJoin_root_forward_selection
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered :
      source.val.diagram.Encloses (source.val.diagram.wires outer).scope
        (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (WireJoinSoundness.Target source.val.diagram outer inner).WellFormed
        signature)
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (targetOuter :
      Fin ((WireJoinSoundness.targetOpenRaw source.val outer inner distinct).exposedWires.length) →
        D)
    (outerAgrees :
      sourceOuter =
        targetOuter ∘
          WireJoinSoundness.exposedMap source.val outer inner distinct)
    (sourceHidden : Fin source.val.hiddenWires.length → D)
    (joinedValues : ∀ outerIndex innerIndex,
      source.val.rootWires.get outerIndex = outer →
      source.val.rootWires.get innerIndex = inner →
      Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceHidden outerIndex =
        Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceHidden innerIndex) :
    ∃ targetHidden :
        Fin ((WireJoinSoundness.targetOpenRaw source.val outer inner distinct).hiddenWires.length) →
          D,
      Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires sourceOuter sourceHidden =
        Diagram.ConcreteElaboration.rootEnvironment
            (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).exposedWires
            (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).hiddenWires
            targetOuter targetHidden ∘
          (WireJoinSoundness.rootWitness source outer inner distinct ordered
            targetWellFormed).indexMap := by
  let target :=
    WireJoinSoundness.targetOpen source outer inner distinct ordered
      targetWellFormed
  let witness :=
    WireJoinSoundness.rootWitness source outer inner distinct ordered
      targetWellFormed
  let sourceComplete :=
    Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
      source.val.hiddenWires sourceOuter sourceHidden
  have sourceExact :
      Diagram.ConcreteElaboration.WireContext.Exact source.val.rootWires
        source.val.diagram.root :=
    Diagram.Splice.openRootWires_exact source
  have fiberConstant : ∀ left right,
      witness.indexMap left = witness.indexMap right →
        sourceComplete left = sourceComplete right :=
    wireJoin_extended_fiber_constant source.val.diagram outer inner distinct
      source.val.rootWires
      (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).rootWires
      witness source.val.diagram.root sourceExact sourceComplete joinedValues
  let targetComplete :=
    quotientEnvironment witness.indexMap witness.surjective sourceComplete
  have completeAgrees :
      sourceComplete = targetComplete ∘ witness.indexMap :=
    quotientEnvironment_agrees witness.indexMap witness.surjective
      sourceComplete fiberConstant
  have targetInherited : ∀ targetIndex,
      targetComplete
          (WireJoinSoundness.leftIndex
            (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).exposedWires
            (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).hiddenWires
            targetIndex) =
        targetOuter targetIndex := by
    intro targetIndex
    obtain ⟨sourceIndex, sourceIndexMap⟩ :=
      WireJoinSoundness.exposedMap_surjective source.val outer inner distinct
        targetIndex
    have rootIndexMap :=
      WireJoinSoundness.rootWitness_index_exposed source outer inner distinct
        ordered targetWellFormed sourceIndex
    rw [sourceIndexMap] at rootIndexMap
    have agreesAt := congrFun completeAgrees
      (WireJoinSoundness.leftIndex source.val.exposedWires
        source.val.hiddenWires sourceIndex)
    change sourceComplete
        (WireJoinSoundness.leftIndex source.val.exposedWires
          source.val.hiddenWires sourceIndex) =
      targetComplete
        (witness.indexMap
          (WireJoinSoundness.leftIndex source.val.exposedWires
            source.val.hiddenWires sourceIndex)) at agreesAt
    rw [rootIndexMap] at agreesAt
    calc
      _ = sourceComplete
          (WireJoinSoundness.leftIndex source.val.exposedWires
            source.val.hiddenWires sourceIndex) := agreesAt.symm
      _ = sourceOuter sourceIndex := by
        simp [sourceComplete]
      _ = targetOuter
          (WireJoinSoundness.exposedMap source.val outer inner distinct
            sourceIndex) :=
        congrFun outerAgrees sourceIndex
      _ = targetOuter targetIndex := congrArg targetOuter sourceIndexMap
  let targetHidden :=
    rootLocalEnvironmentOfComplete
      (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).exposedWires
      (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).hiddenWires
      targetComplete
  refine ⟨targetHidden, ?_⟩
  have targetCompleteEq :
      Diagram.ConcreteElaboration.rootEnvironment
          (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).exposedWires
          (WireJoinSoundness.targetOpenRaw source.val outer inner distinct).hiddenWires
          targetOuter targetHidden =
        targetComplete :=
    rootEnvironment_rootLocalEnvironmentOfComplete _ _ targetOuter
      targetComplete targetInherited
  rw [targetCompleteEq]
  exact completeAgrees

theorem open_body_denote_root_items
    (checked : CheckedOpenDiagram signature)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin checked.val.exposedWires.length → model.Carrier)
    (bodyDenotes :
      denoteRegion (relCtx := []) model named outerEnv
        (PUnit.unit : RelEnv model.Carrier []) checked.elaborate.body) :
    ∃ items : ItemSeq signature checked.val.rootWires.length [],
      ∃ hiddenEnv : Fin checked.val.hiddenWires.length → model.Carrier,
        Diagram.ConcreteElaboration.compileOccurrencesWith? signature
            checked.val.diagram
            (Diagram.ConcreteElaboration.compileRegion? signature
              checked.val.diagram checked.val.diagram.regionCount)
            checked.val.rootWires
            Diagram.ConcreteElaboration.BinderContext.empty
            (Diagram.ConcreteElaboration.localOccurrences checked.val.diagram
              checked.val.diagram.root) =
          some items ∧
        denoteItemSeq (relCtx := []) model named
          (Diagram.ConcreteElaboration.rootEnvironment
            checked.val.exposedWires checked.val.hiddenWires outerEnv hiddenEnv)
          (PUnit.unit : RelEnv model.Carrier []) items := by
  obtain ⟨body, rootCompiled, bodyEq⟩ :=
    CheckedOpenDiagram.elaborate_body_computation checked
  rw [bodyEq] at bodyDenotes
  simp only [Diagram.ConcreteElaboration.compileRoot?] at rootCompiled
  cases itemsCompiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature
        checked.val.diagram
        (Diagram.ConcreteElaboration.compileRegion? signature
          checked.val.diagram checked.val.diagram.regionCount)
        (checked.val.exposedWires ++ checked.val.hiddenWires)
        Diagram.ConcreteElaboration.BinderContext.empty
        (Diagram.ConcreteElaboration.localOccurrences checked.val.diagram
          checked.val.diagram.root) with
  | none =>
      simp [itemsCompiled] at rootCompiled
  | some items =>
      simp [itemsCompiled] at rootCompiled
      rw [← rootCompiled] at bodyDenotes
      unfold Diagram.ConcreteElaboration.finishRoot at bodyDenotes
      simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
        at bodyDenotes
      obtain ⟨hiddenEnv, renamedDenotes⟩ := bodyDenotes
      refine ⟨items, hiddenEnv, ?_, ?_⟩
      · simpa only [OpenConcreteDiagram.rootWires] using itemsCompiled
      · exact (denoteItemSeq_renameWires (relCtx := []) model named
          (Fin.cast (by simp))
          (extendWireEnv outerEnv hiddenEnv)
          (PUnit.unit : RelEnv model.Carrier []) items).mp
          renamedDenotes

theorem exposedMap_fiber_constant_of_joined_values
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (classes : Fin source.val.exposedWires.length → D)
    (hidden : Fin source.val.hiddenWires.length → D)
    (joinedValues : ∀ outerIndex innerIndex,
      source.val.rootWires.get outerIndex = outer →
      source.val.rootWires.get innerIndex = inner →
      Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires classes hidden outerIndex =
        Diagram.ConcreteElaboration.rootEnvironment source.val.exposedWires
          source.val.hiddenWires classes hidden innerIndex) :
    ∀ left right,
      WireJoinSoundness.exposedMap source.val outer inner distinct left =
        WireJoinSoundness.exposedMap source.val outer inner distinct right →
      classes left = classes right := by
  intro left right mapped
  have mappedWires :
      WireJoinSoundness.wireMap source.val.diagram outer inner distinct
          (source.val.exposedWires.get left) =
        WireJoinSoundness.wireMap source.val.diagram outer inner distinct
          (source.val.exposedWires.get right) := by
    have leftGet :=
      WireJoinSoundness.exposedMap_get source.val outer inner distinct left
    have rightGet :=
      WireJoinSoundness.exposedMap_get source.val outer inner distinct right
    rw [mapped] at leftGet
    exact leftGet.symm.trans rightGet
  rcases
      (WireJoinSoundness.wireMap_eq_iff source.val.diagram outer inner
        (source.val.exposedWires.get left)
        (source.val.exposedWires.get right) distinct).mp mappedWires with
    same | outerInner | innerOuter
  · have indexEq : left = right := by
      apply Fin.ext
      exact (List.getElem_inj source.val.exposedWires_nodup).mp (by
        simpa only [List.get_eq_getElem] using same)
    rw [indexEq]
  · have joined :=
      joinedValues
        (WireJoinSoundness.leftIndex source.val.exposedWires
          source.val.hiddenWires left)
        (WireJoinSoundness.leftIndex source.val.exposedWires
          source.val.hiddenWires right)
        (by simpa only [OpenConcreteDiagram.rootWires,
          WireJoinSoundness.get_leftIndex] using outerInner.1)
        (by simpa only [OpenConcreteDiagram.rootWires,
          WireJoinSoundness.get_leftIndex] using outerInner.2)
    simpa using joined
  · have joined :=
      joinedValues
        (WireJoinSoundness.leftIndex source.val.exposedWires
          source.val.hiddenWires right)
        (WireJoinSoundness.leftIndex source.val.exposedWires
          source.val.hiddenWires left)
        (by simpa only [OpenConcreteDiagram.rootWires,
          WireJoinSoundness.get_leftIndex] using innerOuter.2)
        (by simpa only [OpenConcreteDiagram.rootWires,
          WireJoinSoundness.get_leftIndex] using innerOuter.1)
    simpa using joined.symm

/-- A route between regions at the same concrete cut depth crosses bubbles
only.  This is the concrete criterion used by congruence payloads to expose
their term equations at the joined output scope. -/
theorem route_cutDepth_zero_of_equal
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute checked.val start target path)
    (depth : Nat) (routeDepth : route.HasCutDepth depth)
    (sameDepth :
      concreteCutDepth checked.val start =
        concreteCutDepth checked.val target) :
    depth = 0 := by
  let startView := Classical.choice
    (Diagram.Splice.siteView_complete checked start)
  let targetView := Classical.choice
    (Diagram.Splice.siteView_complete checked target)
  let composed := startView.route.trans route
  have pathEq : startView.path ++ path = targetView.path :=
    Diagram.Splice.Input.RegionRoute.path_unique checked.property
      composed targetView.route
  have composedDepth :
      composed.HasCutDepth
        (startView.focus.context.cutDepth + depth) :=
    startView.cutDepth.trans routeDepth
  let castComposed := composed.castPath pathEq
  have castComposedDepth :
      castComposed.HasCutDepth
        (startView.focus.context.cutDepth + depth) :=
    composedDepth.castPath pathEq
  have routeEq : castComposed = targetView.route := Subsingleton.elim _ _
  rw [routeEq] at castComposedDepth
  have depthEq :=
    regionRoute_cutDepth_unique castComposedDepth targetView.cutDepth
  have depthEq' :
      startView.focus.context.cutDepth + depth =
        targetView.focus.context.cutDepth := by
    simpa [Diagram.Splice.SiteView.focus] using depthEq
  have startEq := siteView_concreteCutDepth_eq startView
  have targetEq := siteView_concreteCutDepth_eq targetView
  omega

/-- Denotation of a compiled region exposes the denotation at the end of any
bubble-only compiler route.  The returned trace is the authoritative trace
generated from the caller's existing compiler computation. -/
theorem compiled_descendant_denotes_of_zero_route
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute checked.val start target path)
    (routeZero : route.HasCutDepth 0)
    {rels : RelCtx}
    (context : Diagram.ConcreteElaboration.WireContext checked.val)
    (binders : Diagram.ConcreteElaboration.BinderContext checked.val rels)
    (fuel : Nat)
    (items : ItemSeq signature (context.extend start).length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature checked.val
        (Diagram.ConcreteElaboration.compileRegion? signature checked.val fuel)
        (context.extend start) binders
        (Diagram.ConcreteElaboration.localOccurrences checked.val start) =
          some items)
    (wiresExact : (context.extend start).Exact start)
    (bindersCover : binders.Covers start)
    (binderEnumeration :
      Diagram.ConcreteElaboration.BinderContext.Enumeration
        checked.val binders start)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (localEnv :
      Fin (Diagram.ConcreteElaboration.exactScopeWires
        checked.val start).length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (denotes :
      denoteItemSeq model named
        (Diagram.ConcreteElaboration.extendedEnvironment context start
          outerEnv localEnv)
        relEnv items) :
    ∃ result : Diagram.Splice.CompilerTraceResult checked route context binders
        (fuel + 1)
        (Diagram.ConcreteElaboration.finishRegion checked.val context start
          items),
      ∃ holeEnv : Fin result.witness.toFocus.holeWires → model.Carrier,
        ∃ holeRelEnv :
            RelEnv model.Carrier result.witness.toFocus.holeRels,
          denoteRegion model named holeEnv holeRelEnv
            result.witness.toFocus.body := by
  have regionCompiled :
      Diagram.ConcreteElaboration.compileRegion? signature checked.val
          (fuel + 1) start context binders =
        some (Diagram.ConcreteElaboration.finishRegion checked.val context
          start items) := by
    simp [Diagram.ConcreteElaboration.compileRegion?, compiled]
  obtain ⟨result⟩ :=
    Diagram.Splice.compileRegion_route_context_complete checked route
      regionCompiled wiresExact bindersCover binderEnumeration
  have startDenotes :
      denoteRegion model named outerEnv relEnv
        (Diagram.ConcreteElaboration.finishRegion checked.val context start
          items) := by
    unfold Diagram.ConcreteElaboration.finishRegion
    simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
    refine ⟨localEnv, ?_⟩
    exact (denoteItemSeq_renameWires model named
      (Fin.cast
        (Diagram.ConcreteElaboration.WireContext.length_extend context start))
      (extendWireEnv outerEnv localEnv) relEnv items).mpr denotes
  have filledDenotes :
      denoteRegion model named outerEnv relEnv
        (result.witness.toFocus.context.fill
          result.witness.toFocus.body) := by
    rw [result.witness.toFocus.rebuild]
    exact startDenotes
  have focusZero : result.witness.toFocus.context.cutDepth = 0 :=
    regionRoute_cutDepth_unique result.trace.cutDepth routeZero
  exact ⟨result,
    result.witness.toFocus.context.denote_hole_of_cutDepth_zero model named
      outerEnv relEnv result.witness.toFocus.body focusZero filledDenotes⟩

/-- Recover the actual compiled item-sequence denotation from the terminal
body recorded by a compiler leaf. -/
theorem compilerLeaf_items_denote
    {checked : CheckedDiagram signature}
    {target : Fin checked.val.regionCount}
    {outer : Nat} {outerRels : RelCtx}
    {body : Region signature outer outerRels} {path : List Nat}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      checked.val target witness)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (holeEnv : Fin witness.toFocus.holeWires → model.Carrier)
    (holeRelEnv : RelEnv model.Carrier witness.toFocus.holeRels)
    (bodyDenotes :
      denoteRegion model named holeEnv holeRelEnv witness.toFocus.body) :
    ∃ localEnv :
        Fin (Diagram.ConcreteElaboration.exactScopeWires
          checked.val target).length → model.Carrier,
      denoteItemSeq model named
        (Diagram.ConcreteElaboration.extendedEnvironment
          leaf.inheritedWires target
          (holeEnv ∘ Fin.cast leaf.inheritedLength)
          localEnv)
        holeRelEnv leaf.items := by
  rw [leaf.bodyComputation, Region.castWiresEq_eq_renameWires] at bodyDenotes
  have finishDenotes :=
    (denoteRegion_renameWires model named
      (Fin.cast leaf.inheritedLength)
      holeEnv holeRelEnv
      (Diagram.ConcreteElaboration.finishRegion checked.val
        leaf.inheritedWires target leaf.items)).mp bodyDenotes
  unfold Diagram.ConcreteElaboration.finishRegion at finishDenotes
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires] at finishDenotes
  obtain ⟨localEnv, renamedItemsDenote⟩ := finishDenotes
  refine ⟨localEnv, ?_⟩
  exact (denoteItemSeq_renameWires model named
    (Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend
        leaf.inheritedWires target))
    (extendWireEnv (holeEnv ∘ Fin.cast leaf.inheritedLength) localEnv)
    holeRelEnv leaf.items).mp renamedItemsDenote

/-- Bubble-only compiler descent preserves the valuation of every wire
inherited at the start and exposes a denotation of the terminal compiled
items. -/
theorem trace_leaf_items_denote_preserving_inherited
    {checked : CheckedDiagram signature}
    {start target : Fin checked.val.regionCount} {path : List Nat}
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    {route : Diagram.Splice.RegionRoute checked.val start target path}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    {state : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      checked.val start (.here body)}
    (trace : Diagram.Splice.CompilerTrace signature checked.val route witness
      state)
    (routeZero : route.HasCutDepth 0)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin state.inheritedWires.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (bodyDenotes :
      denoteRegion model named
        (outerEnv ∘ Fin.cast state.inheritedLength.symm) relEnv body) :
    ∃ leafOuter : Fin trace.leaf.inheritedWires.length → model.Carrier,
      ∃ leafLocal :
          Fin (Diagram.ConcreteElaboration.exactScopeWires
            checked.val target).length → model.Carrier,
        ∃ leafRelEnv :
            RelEnv model.Carrier witness.toFocus.holeRels,
          leafOuter ∘ trace.inheritedIndex = outerEnv ∧
            denoteItemSeq model named
              (Diagram.ConcreteElaboration.extendedEnvironment
                trace.leaf.inheritedWires target leafOuter leafLocal)
              leafRelEnv trace.leaf.items := by
  have filledDenotes :
      denoteRegion model named
        (outerEnv ∘ Fin.cast state.inheritedLength.symm) relEnv
        (witness.toFocus.context.fill witness.toFocus.body) := by
    rw [witness.toFocus.rebuild]
    exact bodyDenotes
  have focusZero : witness.toFocus.context.cutDepth = 0 :=
    regionRoute_cutDepth_unique trace.cutDepth routeZero
  obtain ⟨holeEnv, holeRelEnv, outerAgrees, holeDenotes⟩ :=
    witness.toFocus.context.denote_hole_of_cutDepth_zero_with_outer
      model named (outerEnv ∘ Fin.cast state.inheritedLength.symm)
      relEnv witness.toFocus.body focusZero filledDenotes
  obtain ⟨leafLocal, leafItemsDenote⟩ :=
    compilerLeaf_items_denote trace.leaf model named holeEnv holeRelEnv
      holeDenotes
  let leafOuter : Fin trace.leaf.inheritedWires.length → model.Carrier :=
    holeEnv ∘ Fin.cast trace.leaf.inheritedLength
  have inheritedAgrees : leafOuter ∘ trace.inheritedIndex = outerEnv := by
    funext index
    change holeEnv
        (Fin.cast trace.leaf.inheritedLength (trace.inheritedIndex index)) =
      outerEnv index
    rw [trace.inheritedIndex_intrinsic index]
    have agreesAt :=
      congrFun outerAgrees (Fin.cast state.inheritedLength index)
    simpa [Function.comp_def] using agreesAt
  exact ⟨leafOuter, leafLocal, holeRelEnv, inheritedAgrees,
    leafItemsDenote⟩

/-- The terminal complete environment agrees with the starting inherited
environment at every pair of compiler indices naming the same concrete wire. -/
theorem trace_complete_environment_agrees
    {checked : CheckedDiagram signature}
    {start target : Fin checked.val.regionCount} {path : List Nat}
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    {route : Diagram.Splice.RegionRoute checked.val start target path}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    {state : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      checked.val start (.here body)}
    (trace : Diagram.Splice.CompilerTrace signature checked.val route witness
      state)
    (outerEnv : Fin state.inheritedWires.length → D)
    (leafOuter : Fin trace.leaf.inheritedWires.length → D)
    (leafLocal :
      Fin (Diagram.ConcreteElaboration.exactScopeWires
        checked.val target).length → D)
    (inheritedAgrees :
      leafOuter ∘ trace.inheritedIndex = outerEnv)
    (sourceIndex : Fin state.inheritedWires.length)
    (targetIndex : Fin (trace.leaf.inheritedWires.extend target).length)
    (sameWire :
      state.inheritedWires.get sourceIndex =
        (trace.leaf.inheritedWires.extend target).get targetIndex) :
    outerEnv sourceIndex =
      Diagram.ConcreteElaboration.extendedEnvironment
        trace.leaf.inheritedWires target leafOuter leafLocal targetIndex := by
  let inheritedTarget :
      Fin (trace.leaf.inheritedWires.extend target).length :=
    Fin.cast
      (Diagram.ConcreteElaboration.WireContext.length_extend
        trace.leaf.inheritedWires target).symm
      (Fin.castAdd
        (Diagram.ConcreteElaboration.exactScopeWires
          checked.val target).length
        (trace.inheritedIndex sourceIndex))
  have inheritedTargetGet :
      (trace.leaf.inheritedWires.extend target).get inheritedTarget =
        state.inheritedWires.get sourceIndex := by
    calc
      _ = trace.leaf.inheritedWires.get
          (trace.inheritedIndex sourceIndex) := by
            simp [inheritedTarget,
              Diagram.ConcreteElaboration.WireContext.extend]
      _ = _ := trace.inheritedIndex_get sourceIndex
  have targetEq : targetIndex = inheritedTarget := by
    apply Fin.ext
    exact (List.getElem_inj trace.leaf.wiresExact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        sameWire.symm.trans inheritedTargetGet.symm)
  subst targetIndex
  have agreesAt := congrFun inheritedAgrees sourceIndex
  rw [← agreesAt]
  simp [inheritedTarget,
    Diagram.ConcreteElaboration.extendedEnvironment,
    Diagram.ConcreteElaboration.WireContext.extend, extendWireEnv]

/-- A denoted compiler leaf together with exact agreement against the complete
wire environment at the ancestor site from which it was reached. -/
structure DenotedDescendantLeaf
    (checked : CheckedDiagram signature)
    (target : Fin checked.val.regionCount)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (sourceContext : Diagram.ConcreteElaboration.WireContext checked.val)
    (sourceEnv : Fin sourceContext.length → model.Carrier) where
  outer : Nat
  rels : RelCtx
  body : Region signature outer rels
  path : List Nat
  witness : VisualProof.Diagram.Region.ContextPath body path
  leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
    checked.val target witness
  outerEnv : Fin leaf.inheritedWires.length → model.Carrier
  localEnv :
    Fin (Diagram.ConcreteElaboration.exactScopeWires
      checked.val target).length → model.Carrier
  relEnv : RelEnv model.Carrier witness.toFocus.holeRels
  itemsDenote :
    denoteItemSeq model named
      (Diagram.ConcreteElaboration.extendedEnvironment
        leaf.inheritedWires target outerEnv localEnv)
      relEnv leaf.items
  agrees : ∀ sourceIndex targetIndex,
    sourceContext.get sourceIndex =
        (leaf.inheritedWires.extend target).get targetIndex →
      sourceEnv sourceIndex =
        Diagram.ConcreteElaboration.extendedEnvironment
          leaf.inheritedWires target outerEnv localEnv targetIndex

/-- Follow the already successful compiler computation down a bubble-only
route, retaining both the descendant item semantics and exact wire-value
agreement with the complete ancestor-site environment. -/
theorem denoted_descendant_leaf
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute checked.val start target path)
    (routeZero : route.HasCutDepth 0)
    {rels : RelCtx}
    (context : Diagram.ConcreteElaboration.WireContext checked.val)
    (binders : Diagram.ConcreteElaboration.BinderContext checked.val rels)
    (fuel : Nat)
    (items : ItemSeq signature (context.extend start).length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature checked.val
        (Diagram.ConcreteElaboration.compileRegion? signature checked.val fuel)
        (context.extend start) binders
        (Diagram.ConcreteElaboration.localOccurrences checked.val start) =
          some items)
    (wiresExact : (context.extend start).Exact start)
    (bindersCover : binders.Covers start)
    (binderEnumeration :
      Diagram.ConcreteElaboration.BinderContext.Enumeration
        checked.val binders start)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (localEnv :
      Fin (Diagram.ConcreteElaboration.exactScopeWires
        checked.val start).length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote :
      denoteItemSeq model named
        (Diagram.ConcreteElaboration.extendedEnvironment context start
          outerEnv localEnv)
        relEnv items) :
    Nonempty (DenotedDescendantLeaf checked target model named
      (context.extend start)
      (Diagram.ConcreteElaboration.extendedEnvironment context start
        outerEnv localEnv)) := by
  cases routeZero with
  | here =>
      let leaf :=
        VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
          checked.val start context binders fuel
            items compiled wiresExact bindersCover binderEnumeration
      refine ⟨{
        outer := context.length
        rels := rels
        body := Diagram.ConcreteElaboration.finishRegion checked.val context
          start items
        path := []
        witness := .here _
        leaf := leaf
        outerEnv := outerEnv
        localEnv := localEnv
        relEnv := relEnv
        itemsDenote := itemsDenote
        agrees := ?_
      }⟩
      intro sourceIndex targetIndex sameWire
      have indexEq : sourceIndex = targetIndex := by
        apply Fin.ext
        exact (List.getElem_inj wiresExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using sameWire)
      subst targetIndex
      rfl
  | @bubble start child target rest _ arity hparent position hposition tail
      childKind tailZero =>
          let itemPosition : Fin items.length :=
            Fin.cast
              (Diagram.ConcreteElaboration.compileOccurrencesWith?_length
                (Diagram.ConcreteElaboration.compileRegion? signature
                  checked.val fuel)
                (context.extend start) binders compiled).symm
              position
          have compiledOccurrence :=
            Diagram.ConcreteElaboration.compileOccurrencesWith?_get
              (Diagram.ConcreteElaboration.compileRegion? signature
                checked.val fuel)
              (context.extend start) binders compiled position
          have occurrenceGet :
              (Diagram.ConcreteElaboration.localOccurrences checked.val
                start).get position = .child child := by
            simpa only [List.get_eq_getElem] using indexOf?_sound hposition
          rw [occurrenceGet] at compiledOccurrence
          simp only [Diagram.ConcreteElaboration.compileOccurrenceWith?,
            childKind] at compiledOccurrence
          cases childCompiled :
              Diagram.ConcreteElaboration.compileRegion? signature checked.val
                fuel child (context.extend start)
                  (binders.push child arity) with
          | none =>
              simp [childCompiled] at compiledOccurrence
          | some childBody =>
              have itemEq :
                  items.get itemPosition = .bubble arity childBody := by
                simpa [itemPosition, childCompiled] using
                  compiledOccurrence.symm
              have itemDenote :=
                (denoteItemSeq_iff_get model named
                  (Diagram.ConcreteElaboration.extendedEnvironment context
                    start outerEnv localEnv)
                  relEnv items).mp itemsDenote itemPosition
              rw [itemEq] at itemDenote
              obtain ⟨relation, childBodyDenotes⟩ := itemDenote
              have childExact :
                  ((context.extend start).extend child).Exact child :=
                wiresExact.extend_child checked.property hparent
              have childCovers :
                  (binders.push child arity).Covers child :=
                Diagram.ConcreteElaboration.BinderContext.push_covers_bubble_child
                  bindersCover childKind
              let childEnumeration :=
                binderEnumeration.bubbleChild checked.property childKind
              obtain ⟨result⟩ :=
                Diagram.Splice.compileRegion_route_context_complete checked
                  tail childCompiled childExact childCovers childEnumeration
              let siteEnv :=
                Diagram.ConcreteElaboration.extendedEnvironment context start
                  outerEnv localEnv
              let stateOuter :
                  Fin result.state.inheritedWires.length → model.Carrier :=
                siteEnv ∘ Fin.cast
                  (congrArg List.length result.inherited_eq)
              let childRelEnv : RelEnv model.Carrier (arity :: rels) :=
                (relation, relEnv)
              have childBodyDenotes' :
                  denoteRegion model named
                    (stateOuter ∘
                      Fin.cast result.state.inheritedLength.symm)
                    childRelEnv childBody := by
                simpa [stateOuter, siteEnv, Function.comp_def] using
                  childBodyDenotes
              obtain ⟨leafOuter, leafLocal, leafRelEnv, inheritedAgrees,
                  leafItemsDenote⟩ :=
                trace_leaf_items_denote_preserving_inherited result.trace
                  tailZero model named stateOuter childRelEnv
                  childBodyDenotes'
              refine ⟨{
                outer := (context.extend start).length
                rels := arity :: rels
                body := childBody
                path := rest
                witness := result.witness
                leaf := result.trace.leaf
                outerEnv := leafOuter
                localEnv := leafLocal
                relEnv := leafRelEnv
                itemsDenote := leafItemsDenote
                agrees := ?_
              }⟩
              intro sourceIndex targetIndex sameWire
              let stateIndex : Fin result.state.inheritedWires.length :=
                Fin.cast (congrArg List.length result.inherited_eq).symm
                  sourceIndex
              have stateGet :
                  result.state.inheritedWires.get stateIndex =
                    (context.extend start).get sourceIndex := by
                exact list_get_cast result.inherited_eq
                  sourceIndex
              have stateSameWire :
                  result.state.inheritedWires.get stateIndex =
                    (result.trace.leaf.inheritedWires.extend target).get
                      targetIndex := stateGet.trans sameWire
              have agreesAt :=
                trace_complete_environment_agrees result.trace stateOuter
                  leafOuter leafLocal inheritedAgrees stateIndex targetIndex
                  stateSameWire
              simpa [stateOuter, stateIndex, siteEnv, Function.comp_def] using
                agreesAt

end CongruenceSoundness

end VisualProof.Rule
