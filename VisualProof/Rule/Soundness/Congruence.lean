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
    (model : Lambda.LambdaModel)
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
    (model : Lambda.LambdaModel)
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
    (model : Lambda.LambdaModel)
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
    (model : Lambda.LambdaModel)
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
    (model : Lambda.LambdaModel)
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
    (model : Lambda.LambdaModel)
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

/-- A denoted compiled term occurrence exposes its resolved output equation
and the complete resolved free-port environment. -/
theorem compiled_term_node_equation
    {checked : CheckedDiagram signature}
    {region : Fin checked.val.regionCount}
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels} {path : List Nat}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      checked.val region witness)
    (node : Fin checked.val.nodeCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : checked.val.nodes node = .term region freePorts term)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (leaf.inheritedWires.extend region).length → model.Carrier)
    (relEnv : RelEnv model.Carrier witness.toFocus.holeRels)
    (itemsDenote :
      denoteItemSeq model named env relEnv leaf.items) :
    ∃ output : Fin (leaf.inheritedWires.extend region).length,
      ∃ free :
          Fin freePorts →
            Fin (leaf.inheritedWires.extend region).length,
        Diagram.ConcreteElaboration.resolvePort? checked.val
            (leaf.inheritedWires.extend region) node .output = some output ∧
          Diagram.ConcreteElaboration.resolvePorts? checked.val
              (leaf.inheritedWires.extend region) node freePorts
                (fun index => .free index) = some free ∧
            env output = model.eval term (env ∘ free) := by
  have nodeMember :
      Diagram.ConcreteElaboration.LocalOccurrence.node node ∈
        Diagram.ConcreteElaboration.localOccurrences checked.val region := by
    rw [Diagram.ConcreteElaboration.mem_localOccurrences_node]
    rw [nodeShape]
    rfl
  obtain ⟨position, positionEq⟩ := indexOf?_complete nodeMember
  let itemPosition : Fin leaf.items.length :=
    Fin.cast
      (Diagram.ConcreteElaboration.compileOccurrencesWith?_length
        (Diagram.ConcreteElaboration.compileRegion? signature checked.val
          leaf.fuel)
        (leaf.inheritedWires.extend region) leaf.binders
        leaf.itemsComputation).symm
      position
  have compiledOccurrence :=
    Diagram.ConcreteElaboration.compileOccurrencesWith?_get
      (Diagram.ConcreteElaboration.compileRegion? signature checked.val
        leaf.fuel)
      (leaf.inheritedWires.extend region) leaf.binders
      leaf.itemsComputation position
  have occurrenceGet :
      (Diagram.ConcreteElaboration.localOccurrences checked.val region).get
          position =
        .node node := by
    simpa only [List.get_eq_getElem] using indexOf?_sound positionEq
  rw [occurrenceGet] at compiledOccurrence
  simp only [Diagram.ConcreteElaboration.compileOccurrenceWith?] at compiledOccurrence
  cases outputResult :
      Diagram.ConcreteElaboration.resolvePort? checked.val
        (leaf.inheritedWires.extend region) node .output with
  | none =>
      simp [Diagram.ConcreteElaboration.compileNode?, nodeShape,
        outputResult] at compiledOccurrence
  | some output =>
      cases freeResult :
          Diagram.ConcreteElaboration.resolvePorts? checked.val
            (leaf.inheritedWires.extend region) node freePorts
              (fun index => .free index) with
      | none =>
          simp [Diagram.ConcreteElaboration.compileNode?, nodeShape, outputResult,
            freeResult] at compiledOccurrence
      | some free =>
          have itemEq :
              leaf.items.get itemPosition =
                .equation output (term.mapFree free) := by
            simpa [itemPosition, Diagram.ConcreteElaboration.compileNode?,
              nodeShape, outputResult, freeResult] using compiledOccurrence.symm
          have itemDenote :=
            (denoteItemSeq_iff_get model named env relEnv leaf.items).mp
              itemsDenote itemPosition
          rw [itemEq] at itemDenote
          refine ⟨output, free, rfl, rfl, ?_⟩
          simpa [model.eval_mapFree, Function.comp_def] using itemDenote

theorem compiled_items_term_node_equation
    {checked : CheckedDiagram signature}
    {region : Fin checked.val.regionCount}
    (context : Diagram.ConcreteElaboration.WireContext checked.val)
    (binders : Diagram.ConcreteElaboration.BinderContext checked.val rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature checked.val
        (Diagram.ConcreteElaboration.compileRegion? signature checked.val fuel)
        context binders
        (Diagram.ConcreteElaboration.localOccurrences checked.val region) =
          some items)
    (wiresExact : context.Exact region)
    (node : Fin checked.val.nodeCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : checked.val.nodes node = .term region freePorts term)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote : denoteItemSeq model named env relEnv items) :
    ∃ output : Fin context.length,
      ∃ free : Fin freePorts → Fin context.length,
        Diagram.ConcreteElaboration.resolvePort? checked.val context node
            .output = some output ∧
          Diagram.ConcreteElaboration.resolvePorts? checked.val context node
              freePorts (fun index => .free index) = some free ∧
            env output = model.eval term (env ∘ free) := by
  have nodeMember :
      Diagram.ConcreteElaboration.LocalOccurrence.node node ∈
        Diagram.ConcreteElaboration.localOccurrences checked.val region := by
    rw [Diagram.ConcreteElaboration.mem_localOccurrences_node]
    rw [nodeShape]
    rfl
  obtain ⟨position, positionEq⟩ := indexOf?_complete nodeMember
  let itemPosition : Fin items.length :=
    Fin.cast
      (Diagram.ConcreteElaboration.compileOccurrencesWith?_length
        (Diagram.ConcreteElaboration.compileRegion? signature checked.val fuel)
        context binders compiled).symm
      position
  have compiledOccurrence :=
    Diagram.ConcreteElaboration.compileOccurrencesWith?_get
      (Diagram.ConcreteElaboration.compileRegion? signature checked.val fuel)
      context binders compiled position
  have occurrenceGet :
      (Diagram.ConcreteElaboration.localOccurrences checked.val region).get
          position =
        .node node := by
    simpa only [List.get_eq_getElem] using indexOf?_sound positionEq
  rw [occurrenceGet] at compiledOccurrence
  simp only [Diagram.ConcreteElaboration.compileOccurrenceWith?]
    at compiledOccurrence
  cases outputResult :
      Diagram.ConcreteElaboration.resolvePort? checked.val context node
        .output with
  | none =>
      simp [Diagram.ConcreteElaboration.compileNode?, nodeShape,
        outputResult] at compiledOccurrence
  | some output =>
      cases freeResult :
          Diagram.ConcreteElaboration.resolvePorts? checked.val context node
            freePorts (fun index => .free index) with
      | none =>
          simp [Diagram.ConcreteElaboration.compileNode?, nodeShape,
            outputResult, freeResult] at compiledOccurrence
      | some free =>
          have itemEq :
              items.get itemPosition = .equation output (term.mapFree free) := by
            simpa [itemPosition, Diagram.ConcreteElaboration.compileNode?,
              nodeShape, outputResult, freeResult] using
                compiledOccurrence.symm
          have itemDenote :=
            (denoteItemSeq_iff_get model named env relEnv items).mp
              itemsDenote itemPosition
          rw [itemEq] at itemDenote
          refine ⟨output, free, rfl, rfl, ?_⟩
          simpa [model.eval_mapFree, Function.comp_def] using itemDenote

structure CompiledCongruenceEquation
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (context : Diagram.ConcreteElaboration.WireContext input.val)
    (model : Lambda.LambdaModel)
    (env : Fin context.length → model.Carrier) where
  firstIndex : Fin context.length
  secondIndex : Fin context.length
  firstWire : context.get firstIndex = payload.firstOutput
  secondWire : context.get secondIndex = payload.secondOutput
  valuesEqual : env firstIndex = env secondIndex

theorem compiled_items_congruence_equation
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (context : Diagram.ConcreteElaboration.WireContext input.val)
    (binders : Diagram.ConcreteElaboration.BinderContext input.val rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature input.val
        (Diagram.ConcreteElaboration.compileRegion? signature input.val fuel)
        context binders
        (Diagram.ConcreteElaboration.localOccurrences input.val
          payload.region) =
          some items)
    (wiresExact : context.Exact payload.region)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote : denoteItemSeq model named env relEnv items) :
    Nonempty (CompiledCongruenceEquation payload context model env) := by
  obtain ⟨firstIndex, firstFree, firstResolved, firstFreeResolved,
      firstEquation⟩ :=
    compiled_items_term_node_equation context binders fuel items compiled
      wiresExact first payload.firstFreePorts payload.firstTerm
      payload.firstNode model named env relEnv itemsDenote
  obtain ⟨secondIndex, secondFree, secondResolved, secondFreeResolved,
      secondEquation⟩ :=
    compiled_items_term_node_equation context binders fuel items compiled
      wiresExact second payload.secondFreePorts payload.secondTerm
      payload.secondNode model named env relEnv itemsDenote
  have aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        env (firstFree left) = env (secondFree right) := by
    intro left right shared
    obtain ⟨firstWire, firstOccurs, firstGet⟩ :=
      Diagram.ConcreteElaboration.resolvePort?_sound
        (sequenceFin_sound firstFreeResolved left)
    obtain ⟨secondWire, secondOccurs, secondGet⟩ :=
      Diagram.ConcreteElaboration.resolvePort?_sound
        (sequenceFin_sound secondFreeResolved right)
    have wireEq : firstWire = secondWire :=
      payload.shared_port_alignment left right firstWire secondWire shared
        firstOccurs secondOccurs
    have indexEq : firstFree left = secondFree right := by
      apply Fin.ext
      exact (List.getElem_inj wiresExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using
          firstGet.trans (wireEq.trans secondGet.symm))
    rw [indexEq]
  obtain ⟨commonEnv, firstEnvEq, secondEnvEq⟩ :=
    payload.exists_common_environment
      (env ∘ firstFree) (env ∘ secondFree) aligned
  have termValuesEqual :
      model.eval payload.firstTerm (env ∘ firstFree) =
        model.eval payload.secondTerm (env ∘ secondFree) := by
    rw [← firstEnvEq, ← secondEnvEq]
    exact payload.eval_eq model commonEnv
  obtain ⟨firstWire, firstOccurs, firstGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound firstResolved
  obtain ⟨secondWire, secondOccurs, secondGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound secondResolved
  have firstWireEq : firstWire = payload.firstOutput :=
    Diagram.ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint
      firstOccurs payload.firstOutput_occurs
  have secondWireEq : secondWire = payload.secondOutput :=
    Diagram.ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint
      secondOccurs payload.secondOutput_occurs
  exact ⟨{
    firstIndex := firstIndex
    secondIndex := secondIndex
    firstWire := firstGet.trans firstWireEq
    secondWire := secondGet.trans secondWireEq
    valuesEqual := firstEquation.trans
      (termValuesEqual.trans secondEquation.symm)
  }⟩

/-- The two certified congruent term occurrences evaluate to the same value
inside any denoted compiler leaf for their common region.  The resolved output
indices are retained together with their concrete-wire identities so that the
equality can be transported back to an ancestor join context. -/
structure LeafCongruenceEquation
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels} {path : List Nat}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val payload.region witness)
    (model : Lambda.LambdaModel)
    (outerEnv : Fin leaf.inheritedWires.length → model.Carrier)
    (localEnv :
      Fin (Diagram.ConcreteElaboration.exactScopeWires
        input.val payload.region).length → model.Carrier) where
  firstIndex : Fin (leaf.inheritedWires.extend payload.region).length
  secondIndex : Fin (leaf.inheritedWires.extend payload.region).length
  firstResolved :
    Diagram.ConcreteElaboration.resolvePort? input.val
      (leaf.inheritedWires.extend payload.region) first .output =
        some firstIndex
  secondResolved :
    Diagram.ConcreteElaboration.resolvePort? input.val
      (leaf.inheritedWires.extend payload.region) second .output =
        some secondIndex
  firstWire :
    (leaf.inheritedWires.extend payload.region).get firstIndex =
      payload.firstOutput
  secondWire :
    (leaf.inheritedWires.extend payload.region).get secondIndex =
      payload.secondOutput
  valuesEqual :
    Diagram.ConcreteElaboration.extendedEnvironment
        leaf.inheritedWires payload.region outerEnv localEnv firstIndex =
      Diagram.ConcreteElaboration.extendedEnvironment
        leaf.inheritedWires payload.region outerEnv localEnv secondIndex

theorem denoted_leaf_congruence_equation
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels} {path : List Nat}
    {witness : VisualProof.Diagram.Region.ContextPath body path}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val payload.region witness)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin leaf.inheritedWires.length → model.Carrier)
    (localEnv :
      Fin (Diagram.ConcreteElaboration.exactScopeWires
        input.val payload.region).length → model.Carrier)
    (relEnv : RelEnv model.Carrier witness.toFocus.holeRels)
    (itemsDenote :
      denoteItemSeq model named
        (Diagram.ConcreteElaboration.extendedEnvironment
          leaf.inheritedWires payload.region outerEnv localEnv)
        relEnv leaf.items) :
    Nonempty (LeafCongruenceEquation payload leaf model outerEnv localEnv) := by
  let env :=
    Diagram.ConcreteElaboration.extendedEnvironment
      leaf.inheritedWires payload.region outerEnv localEnv
  obtain ⟨firstIndex, firstFree, firstResolved, firstFreeResolved,
      firstEquation⟩ :=
    compiled_term_node_equation leaf first payload.firstFreePorts
      payload.firstTerm payload.firstNode model named env relEnv itemsDenote
  obtain ⟨secondIndex, secondFree, secondResolved, secondFreeResolved,
      secondEquation⟩ :=
    compiled_term_node_equation leaf second payload.secondFreePorts
      payload.secondTerm payload.secondNode model named env relEnv itemsDenote
  have aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        env (firstFree left) = env (secondFree right) := by
    intro left right shared
    have firstPortResolved :=
      sequenceFin_sound firstFreeResolved left
    have secondPortResolved :=
      sequenceFin_sound secondFreeResolved right
    obtain ⟨firstWire, firstOccurs, firstGet⟩ :=
      Diagram.ConcreteElaboration.resolvePort?_sound firstPortResolved
    obtain ⟨secondWire, secondOccurs, secondGet⟩ :=
      Diagram.ConcreteElaboration.resolvePort?_sound secondPortResolved
    have wireEq : firstWire = secondWire :=
      payload.shared_port_alignment left right firstWire secondWire shared
        firstOccurs secondOccurs
    have indexEq : firstFree left = secondFree right := by
      apply Fin.ext
      exact
        (List.getElem_inj leaf.wiresExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            firstGet.trans (wireEq.trans secondGet.symm))
    rw [indexEq]
  obtain ⟨commonEnv, firstEnvEq, secondEnvEq⟩ :=
    payload.exists_common_environment
      (env ∘ firstFree) (env ∘ secondFree) aligned
  have termValuesEqual :
      model.eval payload.firstTerm (env ∘ firstFree) =
        model.eval payload.secondTerm (env ∘ secondFree) := by
    rw [← firstEnvEq, ← secondEnvEq]
    exact payload.eval_eq model commonEnv
  obtain ⟨firstWire, firstOccurs, firstGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound firstResolved
  obtain ⟨secondWire, secondOccurs, secondGet⟩ :=
    Diagram.ConcreteElaboration.resolvePort?_sound secondResolved
  have firstWireEq : firstWire = payload.firstOutput :=
    Diagram.ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint
      firstOccurs payload.firstOutput_occurs
  have secondWireEq : secondWire = payload.secondOutput :=
    Diagram.ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint
      secondOccurs payload.secondOutput_occurs
  refine ⟨{
    firstIndex := firstIndex
    secondIndex := secondIndex
    firstResolved := firstResolved
    secondResolved := secondResolved
    firstWire := ?_
    secondWire := ?_
    valuesEqual := firstEquation.trans (termValuesEqual.trans secondEquation.symm)
  }⟩
  · exact firstGet.trans firstWireEq
  · exact secondGet.trans secondWireEq

/-- A bubble-only compiler route from the absorbed-wire scope to the two term
nodes turns their certified equation into equality of the retained and
absorbed wire values in the complete source environment at the join site. -/
theorem congruence_joined_values_of_zero_route
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val
      (input.val.wires inner).scope payload.region path)
    (routeZero : route.HasCutDepth 0)
    {rels : RelCtx}
    (context : Diagram.ConcreteElaboration.WireContext input.val)
    (binders : Diagram.ConcreteElaboration.BinderContext input.val rels)
    (fuel : Nat)
    (items : ItemSeq signature
      (context.extend (input.val.wires inner).scope).length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature input.val
        (Diagram.ConcreteElaboration.compileRegion? signature input.val fuel)
        (context.extend (input.val.wires inner).scope) binders
        (Diagram.ConcreteElaboration.localOccurrences input.val
          (input.val.wires inner).scope) =
          some items)
    (wiresExact :
      (context.extend (input.val.wires inner).scope).Exact
        (input.val.wires inner).scope)
    (bindersCover : binders.Covers (input.val.wires inner).scope)
    (binderEnumeration :
      Diagram.ConcreteElaboration.BinderContext.Enumeration
        input.val binders (input.val.wires inner).scope)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (localEnv :
      Fin (Diagram.ConcreteElaboration.exactScopeWires input.val
        (input.val.wires inner).scope).length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote :
      denoteItemSeq model named
        (Diagram.ConcreteElaboration.extendedEnvironment context
          (input.val.wires inner).scope outerEnv localEnv)
        relEnv items) :
    ∀ outerIndex innerIndex,
      (context.extend (input.val.wires inner).scope).get outerIndex = outer →
      (context.extend (input.val.wires inner).scope).get innerIndex = inner →
      Diagram.ConcreteElaboration.extendedEnvironment context
          (input.val.wires inner).scope outerEnv localEnv outerIndex =
        Diagram.ConcreteElaboration.extendedEnvironment context
          (input.val.wires inner).scope outerEnv localEnv innerIndex := by
  obtain ⟨descendant⟩ :=
    denoted_descendant_leaf input route routeZero context binders fuel items
      compiled wiresExact bindersCover binderEnumeration model named outerEnv
      localEnv relEnv itemsDenote
  obtain ⟨equation⟩ :=
    denoted_leaf_congruence_equation payload descendant.leaf model named
      descendant.outerEnv descendant.localEnv descendant.relEnv
      descendant.itemsDenote
  intro outerIndex innerIndex outerGet innerGet
  rcases outputs with firstSecond | secondFirst
  · rcases firstSecond with ⟨rfl, rfl⟩
    have firstAgrees :=
      descendant.agrees outerIndex equation.firstIndex
        (outerGet.trans equation.firstWire.symm)
    have secondAgrees :=
      descendant.agrees innerIndex equation.secondIndex
        (innerGet.trans equation.secondWire.symm)
    exact firstAgrees.trans (equation.valuesEqual.trans secondAgrees.symm)
  · rcases secondFirst with ⟨rfl, rfl⟩
    have secondAgrees :=
      descendant.agrees outerIndex equation.secondIndex
        (outerGet.trans equation.secondWire.symm)
    have firstAgrees :=
      descendant.agrees innerIndex equation.firstIndex
        (innerGet.trans equation.firstWire.symm)
    exact secondAgrees.trans (equation.valuesEqual.symm.trans firstAgrees.symm)

theorem congruence_inner_scope_zero_route
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput)) :
    ∃ path,
      ∃ route : Diagram.Splice.RegionRoute input.val
          (input.val.wires inner).scope payload.region path,
        route.HasCutDepth 0 := by
  have innerEncloses :
      input.val.Encloses (input.val.wires inner).scope payload.region := by
    rcases outputs with firstSecond | secondFirst
    · rcases firstSecond with ⟨rfl, rfl⟩
      have encloses :=
        input.property.wire_scopes_enclose payload.secondOutput
          { node := second, port := .output } payload.secondOutput_occurs
      simpa [payload.secondNode] using encloses
    · rcases secondFirst with ⟨rfl, rfl⟩
      have encloses :=
        input.property.wire_scopes_enclose payload.firstOutput
          { node := first, port := .output } payload.firstOutput_occurs
      simpa [payload.firstNode] using encloses
  obtain ⟨path, ⟨route⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses input.val
      (input.val.wires inner).scope payload.region innerEncloses
  obtain ⟨depth, routeDepth⟩ :=
    route.hasCutDepth_exists input.property
  have sameDepth :
      concreteCutDepth input.val (input.val.wires inner).scope =
        concreteCutDepth input.val payload.region := by
    rcases outputs with firstSecond | secondFirst
    · rcases firstSecond with ⟨rfl, rfl⟩
      exact payload.secondScopeDepth
    · rcases secondFirst with ⟨rfl, rfl⟩
      exact payload.firstScopeDepth
  have depthZero :=
    route_cutDepth_zero_of_equal input route depth routeDepth sameDepth
  subst depth
  exact ⟨path, route, routeDepth⟩

theorem congruence_joined_values_from_exact_context
    {input : Diagram.CheckedDiagram signature}
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    {target : Fin input.val.regionCount}
    (targetEq : target = payload.region)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val
      (input.val.wires inner).scope target path)
    (routeZero : route.HasCutDepth 0)
    (context : Diagram.ConcreteElaboration.WireContext input.val)
    (binders : Diagram.ConcreteElaboration.BinderContext input.val rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled :
      Diagram.ConcreteElaboration.compileOccurrencesWith? signature input.val
        (Diagram.ConcreteElaboration.compileRegion? signature input.val fuel)
        context binders
        (Diagram.ConcreteElaboration.localOccurrences input.val
          (input.val.wires inner).scope) =
          some items)
    (wiresExact : context.Exact (input.val.wires inner).scope)
    (bindersCover : binders.Covers (input.val.wires inner).scope)
    (binderEnumeration :
      Diagram.ConcreteElaboration.BinderContext.Enumeration input.val binders
        (input.val.wires inner).scope)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote : denoteItemSeq model named env relEnv items) :
    ∀ outerIndex innerIndex,
      context.get outerIndex = outer →
      context.get innerIndex = inner →
      env outerIndex = env innerIndex := by
  cases routeZero with
  | here =>
      have compiled' :
          Diagram.ConcreteElaboration.compileOccurrencesWith? signature
              input.val
              (Diagram.ConcreteElaboration.compileRegion? signature input.val
                fuel)
              context binders
              (Diagram.ConcreteElaboration.localOccurrences input.val
                payload.region) =
            some items := by
        simpa [← targetEq] using compiled
      have wiresExact' : context.Exact payload.region := by
        simpa [← targetEq] using wiresExact
      obtain ⟨equation⟩ :=
        compiled_items_congruence_equation payload context binders fuel items
          compiled' wiresExact' model named env relEnv itemsDenote
      intro outerIndex innerIndex outerGet innerGet
      rcases outputs with firstSecond | secondFirst
      · rcases firstSecond with ⟨rfl, rfl⟩
        have outerEq : outerIndex = equation.firstIndex := by
          apply Fin.ext
          exact (List.getElem_inj wiresExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              outerGet.trans equation.firstWire.symm)
        have innerEq : innerIndex = equation.secondIndex := by
          apply Fin.ext
          exact (List.getElem_inj wiresExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              innerGet.trans equation.secondWire.symm)
        simpa [outerEq, innerEq] using equation.valuesEqual
      · rcases secondFirst with ⟨rfl, rfl⟩
        have outerEq : outerIndex = equation.secondIndex := by
          apply Fin.ext
          exact (List.getElem_inj wiresExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              outerGet.trans equation.secondWire.symm)
        have innerEq : innerIndex = equation.firstIndex := by
          apply Fin.ext
          exact (List.getElem_inj wiresExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              innerGet.trans equation.firstWire.symm)
        simpa [outerEq, innerEq] using equation.valuesEqual.symm
  | @bubble start child target rest _ arity hparent position hposition tail
      childKind tailZero =>
      subst target
      let itemPosition : Fin items.length :=
        Fin.cast
          (Diagram.ConcreteElaboration.compileOccurrencesWith?_length
            (Diagram.ConcreteElaboration.compileRegion? signature input.val
              fuel)
            context binders compiled).symm
          position
      have compiledOccurrence :=
        Diagram.ConcreteElaboration.compileOccurrencesWith?_get
          (Diagram.ConcreteElaboration.compileRegion? signature input.val fuel)
          context binders compiled position
      have occurrenceGet :
          (Diagram.ConcreteElaboration.localOccurrences input.val
            (input.val.wires inner).scope).get position =
            .child child := by
        simpa only [List.get_eq_getElem] using indexOf?_sound hposition
      rw [occurrenceGet] at compiledOccurrence
      simp only [Diagram.ConcreteElaboration.compileOccurrenceWith?,
        childKind] at compiledOccurrence
      cases childCompiled :
          Diagram.ConcreteElaboration.compileRegion? signature input.val fuel
            child context (binders.push child arity) with
      | none =>
          simp [childCompiled] at compiledOccurrence
      | some childBody =>
          have itemEq : items.get itemPosition = .bubble arity childBody := by
            simpa [itemPosition, childCompiled] using compiledOccurrence.symm
          have itemDenote :=
            (denoteItemSeq_iff_get model named env relEnv items).mp itemsDenote
              itemPosition
          rw [itemEq] at itemDenote
          obtain ⟨relation, childBodyDenotes⟩ := itemDenote
          have childExact : (context.extend child).Exact child :=
            wiresExact.extend_child input.property hparent
          have childCovers :
              (binders.push child arity).Covers child :=
            Diagram.ConcreteElaboration.BinderContext.push_covers_bubble_child
              bindersCover childKind
          let childEnumeration :=
            binderEnumeration.bubbleChild input.property childKind
          obtain ⟨result⟩ :=
            Diagram.Splice.compileRegion_route_context_complete input tail
              childCompiled childExact childCovers childEnumeration
          let stateOuter :
              Fin result.state.inheritedWires.length → model.Carrier :=
            env ∘ Fin.cast (congrArg List.length result.inherited_eq)
          let childRelEnv : RelEnv model.Carrier (arity :: rels) :=
            (relation, relEnv)
          have childBodyDenotes' :
              denoteRegion model named
                (stateOuter ∘ Fin.cast result.state.inheritedLength.symm)
                childRelEnv childBody := by
            simpa [stateOuter, Function.comp_def] using childBodyDenotes
          obtain ⟨leafOuter, leafLocal, leafRelEnv, inheritedAgrees,
              leafItemsDenote⟩ :=
            trace_leaf_items_denote_preserving_inherited result.trace tailZero
              model named stateOuter childRelEnv childBodyDenotes'
          obtain ⟨equation⟩ :=
            denoted_leaf_congruence_equation payload result.trace.leaf model
              named leafOuter leafLocal leafRelEnv leafItemsDenote
          have agrees : ∀ sourceIndex targetIndex,
              context.get sourceIndex =
                  (result.trace.leaf.inheritedWires.extend payload.region).get
                    targetIndex →
                env sourceIndex =
                  Diagram.ConcreteElaboration.extendedEnvironment
                    result.trace.leaf.inheritedWires payload.region leafOuter
                    leafLocal targetIndex := by
            intro sourceIndex targetIndex sameWire
            let stateIndex : Fin result.state.inheritedWires.length :=
              Fin.cast (congrArg List.length result.inherited_eq).symm
                sourceIndex
            have stateGet :
                result.state.inheritedWires.get stateIndex =
                  context.get sourceIndex :=
              list_get_cast result.inherited_eq sourceIndex
            have stateSameWire :
                result.state.inheritedWires.get stateIndex =
                  (result.trace.leaf.inheritedWires.extend payload.region).get
                    targetIndex :=
              stateGet.trans sameWire
            have agreesAt :=
              trace_complete_environment_agrees result.trace stateOuter
                leafOuter leafLocal inheritedAgrees stateIndex targetIndex
                stateSameWire
            simpa [stateOuter, stateIndex, Function.comp_def] using agreesAt
          intro outerIndex innerIndex outerGet innerGet
          rcases outputs with firstSecond | secondFirst
          · rcases firstSecond with ⟨rfl, rfl⟩
            have firstAgrees :=
              agrees outerIndex equation.firstIndex
                (outerGet.trans equation.firstWire.symm)
            have secondAgrees :=
              agrees innerIndex equation.secondIndex
                (innerGet.trans equation.secondWire.symm)
            exact firstAgrees.trans
              (equation.valuesEqual.trans secondAgrees.symm)
          · rcases secondFirst with ⟨rfl, rfl⟩
            have secondAgrees :=
              agrees outerIndex equation.secondIndex
                (outerGet.trans equation.secondWire.symm)
            have firstAgrees :=
              agrees innerIndex equation.firstIndex
                (innerGet.trans equation.firstWire.symm)
            exact secondAgrees.trans
              (equation.valuesEqual.symm.trans firstAgrees.symm)

noncomputable def semanticSimulation
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    (distinct : outer ≠ inner)
    (ordered :
      input.val.Encloses (input.val.wires outer).scope
        (input.val.wires inner).scope)
    (targetWellFormed :
      (WireJoinSoundness.Target input.val outer inner).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      (WireJoinSoundness.Target input.val outer inner) model named := {
  WireJoinSoundness.simulation
    (OpenProofState.asCheckedOpen {
      diagram := input
      boundary := boundary
      boundary_root_scoped := sourceRoot
    })
    outer inner distinct ordered targetWellFormed model named with
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext witness sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    change ∀ relEnv,
      Diagram.ConcreteElaboration.DirectionalLocalTransport direction
        sourceContext targetContext region region
        (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
          witness.indexMap)
        model named relEnv
        (sourceItems.renameRelations
          (fun relation => relation))
        targetItems
    rw [ItemSeq.renameRelations_id]
    change Diagram.ConcreteElaboration.ItemSeqSimulation model named direction
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (witness.extend input.property ordered region sourceExact
          targetExact).indexMap)
      (sourceItems.renameRelations
        (fun relation => relation))
      targetItems at itemSemantics
    rw [ItemSeq.renameRelations_id] at itemSemantics
    cases direction with
    | backward =>
        refine Diagram.ConcreteElaboration.directionalLocalTransport_of_agreement
          .backward sourceContext targetContext region region
          (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
            witness.indexMap)
          (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
            (witness.extend input.property ordered region sourceExact
              targetExact).indexMap)
          model named sourceItems targetItems ?_ itemSemantics
        intro sourceOuter targetOuter outerAgrees targetLocal
        rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          at outerAgrees
        refine ⟨WireJoinSoundness.sourceLocalOfTarget witness input.property
          ordered region sourceExact targetExact targetOuter targetLocal, ?_⟩
        rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact witness.extendedEnvironment_backward input.property ordered
          region sourceExact targetExact sourceOuter targetOuter outerAgrees
          targetLocal
    | forward =>
        intro relEnv sourceOuter targetOuter outerAgrees sourceLocal
          sourceDenotes
        rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          at outerAgrees
        by_cases away :
            region ≠ (input.val.wires inner).scope
        · let targetLocal :=
            WireJoinSoundness.targetLocalOfSource input.val outer inner distinct
              region away sourceLocal
          have completeAgrees :
              Diagram.ConcreteElaboration.extendedEnvironment sourceContext
                  region sourceOuter sourceLocal =
                Diagram.ConcreteElaboration.extendedEnvironment targetContext
                    region targetOuter targetLocal ∘
                  (witness.extend input.property ordered region sourceExact
                    targetExact).indexMap :=
            witness.extendedEnvironment_forward input.property ordered region
              away sourceExact targetExact sourceOuter targetOuter outerAgrees
              sourceLocal
          refine ⟨targetLocal, itemSemantics
            (Diagram.ConcreteElaboration.extendedEnvironment sourceContext
              region sourceOuter sourceLocal)
            (Diagram.ConcreteElaboration.extendedEnvironment targetContext
              region targetOuter targetLocal)
            relEnv ?_ sourceDenotes⟩
          rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          exact completeAgrees
        · have siteEq : region = (input.val.wires inner).scope :=
            Classical.not_not.mp away
          subst region
          obtain ⟨path, route, routeZero⟩ :=
            congruence_inner_scope_zero_route payload outer inner outputs
          have joinedValues :=
            congruence_joined_values_of_zero_route payload outer inner outputs
              route routeZero sourceContext sourceBinders fuelSource sourceItems
              sourceCompiled sourceExact sourceBindersCover sourceEnumeration
              model named sourceOuter sourceLocal relEnv sourceDenotes
          obtain ⟨targetLocal, completeAgrees⟩ :=
            wireJoin_site_forward_selection input.val input.property outer inner
              distinct ordered sourceContext targetContext witness
              (input.val.wires inner).scope sourceExact targetExact sourceOuter
              targetOuter outerAgrees sourceLocal joinedValues
          refine ⟨targetLocal, itemSemantics
            (Diagram.ConcreteElaboration.extendedEnvironment sourceContext
              (input.val.wires inner).scope sourceOuter sourceLocal)
            (Diagram.ConcreteElaboration.extendedEnvironment targetContext
              (input.val.wires inner).scope targetOuter targetLocal)
            relEnv ?_ sourceDenotes⟩
          rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          exact completeAgrees
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      witness atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular nodeMapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    have nodeEq : sourceNode = targetNode :=
      Diagram.ConcreteElaboration.LocalOccurrence.node.inj nodeMapped
    subst targetNode
    apply Diagram.ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      model named direction sourceContext targetContext
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        witness.indexMap)
      sourceBinders sourceBinders
      (Diagram.ConcreteElaboration.identityRelationRenaming sourceRels)
      sourceNode sourceNode id id
    · cases nodeShape : input.val.nodes sourceNode <;>
        simp [WireJoinSoundness.target_nodes, nodeShape, id]
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      exact WireJoinSoundness.resolvedPorts_related input.val outer inner
        distinct targetWellFormed sourceContext targetContext witness targetNodup
        sourceNode port sourceIndex targetIndex sourceResolved targetResolved
    · intro atomRegion binder arity sourceRelation nodeShape binderLookup
      simpa [Diagram.ConcreteElaboration.identityRelationRenaming] using
        binderLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext witness sourceBinders targetBinders atRegion
      focused
    exact False.elim focused
}

noncomputable def rootContext
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    (distinct : outer ≠ inner)
    (ordered :
      input.val.Encloses (input.val.wires outer).scope
        (input.val.wires inner).scope)
    (targetWellFormed :
      (WireJoinSoundness.Target input.val outer inner).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (orientation : Orientation) :
    let source : OpenProofState signature := {
      diagram := input
      boundary := boundary
      boundary_root_scoped := sourceRoot
    }
    let simulation := semanticSimulation input payload boundary sourceRoot
      outer inner outputs distinct ordered targetWellFormed model named
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation (WireJoinSoundness.direction orientation)
      source.asCheckedOpen.val.exposedWires
      source.asCheckedOpen.val.hiddenWires
      (WireJoinSoundness.targetOpenRaw source.asCheckedOpen.val outer inner
        distinct).exposedWires
      (WireJoinSoundness.targetOpenRaw source.asCheckedOpen.val outer inner
        distinct).hiddenWires := by
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let sourceOpen := source.asCheckedOpen
  let simulation := semanticSimulation input payload boundary sourceRoot
    outer inner outputs distinct ordered targetWellFormed model named
  refine {
    outer := Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
      (WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct)
    context := WireJoinSoundness.rootWitness sourceOpen outer inner distinct
      ordered targetWellFormed
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused
      exact False.elim focused
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular allowed sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    change Diagram.ConcreteElaboration.ItemSeqSimulation model named
      (WireJoinSoundness.direction orientation)
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (WireJoinSoundness.rootWitness sourceOpen outer inner distinct ordered
          targetWellFormed).indexMap)
      (sourceItems.renameRelations (fun relation => relation))
      targetItems at itemSemantics
    rw [ItemSeq.renameRelations_id] at itemSemantics
    change Diagram.ConcreteElaboration.DirectionalRootTransport
      (WireJoinSoundness.direction orientation)
      sourceOpen.val.exposedWires sourceOpen.val.hiddenWires
      (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner distinct).exposedWires
      (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner distinct).hiddenWires
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct))
      model named (sourceItems.renameRelations (fun relation => relation))
      targetItems
    rw [ItemSeq.renameRelations_id]
    intro sourceOuter targetOuter relEnv outerAgrees
    rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      at outerAgrees
    cases orientation with
    | backward =>
        intro targetHidden targetDenotes
        let sourceHidden :=
          WireJoinSoundness.sourceHiddenOfTarget sourceOpen outer inner distinct
            ordered targetWellFormed targetOuter targetHidden
        have completeAgrees :=
          WireJoinSoundness.rootEnvironment_backward sourceOpen outer inner
            distinct ordered targetWellFormed sourceOuter targetOuter
            outerAgrees targetHidden
        refine ⟨sourceHidden, itemSemantics
          (Diagram.ConcreteElaboration.rootEnvironment
            sourceOpen.val.exposedWires sourceOpen.val.hiddenWires sourceOuter
            sourceHidden)
          (Diagram.ConcreteElaboration.rootEnvironment
            (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner distinct).exposedWires
            (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner distinct).hiddenWires
            targetOuter targetHidden)
          relEnv ?_ targetDenotes⟩
        rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact completeAgrees
    | forward =>
        intro sourceHidden sourceDenotes
        by_cases rootNe :
            sourceOpen.val.diagram.root ≠
              (sourceOpen.val.diagram.wires inner).scope
        · let targetHidden :=
            WireJoinSoundness.targetHiddenOfSource sourceOpen outer inner
              distinct rootNe sourceHidden
          have completeAgrees :=
            WireJoinSoundness.rootEnvironment_forward sourceOpen outer inner
              distinct ordered targetWellFormed rootNe sourceOuter targetOuter
              outerAgrees sourceHidden
          refine ⟨targetHidden, itemSemantics
            (Diagram.ConcreteElaboration.rootEnvironment
              sourceOpen.val.exposedWires sourceOpen.val.hiddenWires sourceOuter
              sourceHidden)
            (Diagram.ConcreteElaboration.rootEnvironment
              (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner
                distinct).exposedWires
              (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner
                distinct).hiddenWires
              targetOuter targetHidden)
            relEnv ?_ sourceDenotes⟩
          rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          exact completeAgrees
        · have rootEq :
              sourceOpen.val.diagram.root =
                (sourceOpen.val.diagram.wires inner).scope :=
            Classical.not_not.mp rootNe
          obtain ⟨path, route, routeZero⟩ :=
            congruence_inner_scope_zero_route payload outer inner outputs
          have sourceExact :
              Diagram.ConcreteElaboration.WireContext.Exact
                sourceOpen.val.rootWires
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.Splice.openRootWires_exact sourceOpen
          have sourceCover :
              Diagram.ConcreteElaboration.BinderContext.empty.Covers
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.ConcreteElaboration.BinderContext.empty_covers_root
              input.property
          have sourceEnumeration :
              Diagram.ConcreteElaboration.BinderContext.Enumeration input.val
                Diagram.ConcreteElaboration.BinderContext.empty
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.ConcreteElaboration.BinderContext.Enumeration.empty
              input.val
          have sourceCompiled' :
              Diagram.ConcreteElaboration.compileOccurrencesWith? signature
                  input.val
                  (Diagram.ConcreteElaboration.compileRegion? signature
                    input.val input.val.regionCount)
                  sourceOpen.val.rootWires
                  Diagram.ConcreteElaboration.BinderContext.empty
                  (Diagram.ConcreteElaboration.localOccurrences input.val
                    (input.val.wires inner).scope) =
                some sourceItems := by
            have rootEq' :
                input.val.root = (input.val.wires inner).scope := by
              simpa [sourceOpen, source] using rootEq
            rw [← rootEq']
            simpa [sourceOpen, source, OpenConcreteDiagram.rootWires] using
              sourceCompiled
          have joinedValues :=
            congruence_joined_values_from_exact_context payload outer inner
              outputs rfl route routeZero sourceOpen.val.rootWires
              Diagram.ConcreteElaboration.BinderContext.empty
              input.val.regionCount sourceItems sourceCompiled' sourceExact
              sourceCover sourceEnumeration model named
              (Diagram.ConcreteElaboration.rootEnvironment
                sourceOpen.val.exposedWires sourceOpen.val.hiddenWires
                sourceOuter sourceHidden)
              relEnv sourceDenotes
          obtain ⟨targetHidden, completeAgrees⟩ :=
            wireJoin_root_forward_selection sourceOpen outer inner distinct
              ordered targetWellFormed sourceOuter targetOuter outerAgrees
              sourceHidden joinedValues
          refine ⟨targetHidden, itemSemantics
            (Diagram.ConcreteElaboration.rootEnvironment
              sourceOpen.val.exposedWires sourceOpen.val.hiddenWires sourceOuter
              sourceHidden)
            (Diagram.ConcreteElaboration.rootEnvironment
              (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner
                distinct).exposedWires
              (WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner
                distinct).hiddenWires
              targetOuter targetHidden)
            relEnv ?_ sourceDenotes⟩
          rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
          exact completeAgrees
  · intro atRoot distinguished
    exact False.elim distinguished

private theorem boundaryWitness
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    (distinct : outer ≠ inner)
    (ordered :
      input.val.Encloses (input.val.wires outer).scope
        (input.val.wires inner).scope)
    (targetWellFormed :
      (WireJoinSoundness.Target input.val outer inner).WellFormed signature)
    (orientation : Orientation)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin boundary.length → model.Carrier) :
    let source : OpenProofState signature := {
      diagram := input
      boundary := boundary
      boundary_root_scoped := sourceRoot
    }
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      (WireJoinSoundness.direction orientation) source.asCheckedOpen.elaborate
      (WireJoinSoundness.targetOpen source.asCheckedOpen outer inner distinct
        ordered targetWellFormed).elaborate
      (Diagram.ConcreteElaboration.ContextIndexRelation.forwardMap
        (WireJoinSoundness.exposedMap source.asCheckedOpen.val outer inner
          distinct))
      model named sourceArgs
      (sourceArgs ∘ Fin.cast
        (WireJoinSoundness.boundaryLengthEq source.asCheckedOpen.val outer inner
          distinct)) := by
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let sourceOpen := source.asCheckedOpen
  dsimp only
  cases orientation with
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment sourceOpen.elaborate
          model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘
          WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct
        agrees := by
          intro sourcePosition
          let targetPosition := Fin.cast
            (WireJoinSoundness.boundaryLengthEq sourceOpen.val outer inner
              distinct).symm sourcePosition
          have classEq :=
            WireJoinSoundness.boundaryClass_map sourceOpen.val outer inner
              distinct targetPosition
          have positionEq :
              Fin.cast
                  (WireJoinSoundness.boundaryLengthEq sourceOpen.val outer inner
                    distinct)
                  targetPosition =
                sourcePosition := by
            apply Fin.ext
            rfl
          rw [positionEq] at classEq
          change targetAssignment.classes
              (WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct
                (sourceOpen.val.boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          rw [← classEq]
          have targetAgrees := targetAssignment.agrees targetPosition
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      have fiberConstant : ∀ left right,
          WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct left =
              WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct
                right →
            sourceAssignment.classes left =
              sourceAssignment.classes right := by
        by_cases rootNe :
            sourceOpen.val.diagram.root ≠
              (sourceOpen.val.diagram.wires inner).scope
        · intro left right mapped
          exact congrArg sourceAssignment.classes
            (WireJoinSoundness.exposedMap_injective_of_root_ne sourceOpen outer
              inner distinct rootNe mapped)
        · have rootEq :
              sourceOpen.val.diagram.root =
                (sourceOpen.val.diagram.wires inner).scope :=
            Classical.not_not.mp rootNe
          obtain ⟨items, hidden, itemsCompiled, itemsDenote⟩ :=
            open_body_denote_root_items sourceOpen model named
              sourceAssignment.classes sourceDenotes
          obtain ⟨path, route, routeZero⟩ :=
            congruence_inner_scope_zero_route payload outer inner outputs
          have exactAtSite :
              Diagram.ConcreteElaboration.WireContext.Exact
                sourceOpen.val.rootWires
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.Splice.openRootWires_exact sourceOpen
          have coverAtSite :
              Diagram.ConcreteElaboration.BinderContext.empty.Covers
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.ConcreteElaboration.BinderContext.empty_covers_root
              input.property
          have enumerationAtSite :
              Diagram.ConcreteElaboration.BinderContext.Enumeration input.val
                Diagram.ConcreteElaboration.BinderContext.empty
                (sourceOpen.val.diagram.wires inner).scope := by
            rw [← rootEq]
            exact Diagram.ConcreteElaboration.BinderContext.Enumeration.empty
              input.val
          have compiledAtSite :
              Diagram.ConcreteElaboration.compileOccurrencesWith? signature
                  input.val
                  (Diagram.ConcreteElaboration.compileRegion? signature
                    input.val input.val.regionCount)
                  sourceOpen.val.rootWires
                  Diagram.ConcreteElaboration.BinderContext.empty
                  (Diagram.ConcreteElaboration.localOccurrences input.val
                    (input.val.wires inner).scope) =
                some items := by
            have rootEq' :
                input.val.root = (input.val.wires inner).scope := by
              simpa [sourceOpen, source] using rootEq
            rw [← rootEq']
            simpa [sourceOpen, source] using itemsCompiled
          have joinedValues :=
            congruence_joined_values_from_exact_context payload outer inner
              outputs rfl route routeZero sourceOpen.val.rootWires
              Diagram.ConcreteElaboration.BinderContext.empty
              input.val.regionCount items compiledAtSite exactAtSite
              coverAtSite enumerationAtSite model named
              (Diagram.ConcreteElaboration.rootEnvironment
                sourceOpen.val.exposedWires sourceOpen.val.hiddenWires
                sourceAssignment.classes hidden)
              (PUnit.unit : RelEnv model.Carrier []) itemsDenote
          exact exposedMap_fiber_constant_of_joined_values sourceOpen outer
            inner distinct sourceAssignment.classes hidden joinedValues
      let targetClasses :=
        quotientEnvironment
          (WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct)
          (WireJoinSoundness.exposedMap_surjective sourceOpen.val outer inner
            distinct)
          sourceAssignment.classes
      have classesAgree :
          sourceAssignment.classes =
            targetClasses ∘
              WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct :=
        quotientEnvironment_agrees
          (WireJoinSoundness.exposedMap sourceOpen.val outer inner distinct)
          (WireJoinSoundness.exposedMap_surjective sourceOpen.val outer inner
            distinct)
          sourceAssignment.classes fiberConstant
      let targetAssignment : BoundaryAssignment
          (WireJoinSoundness.targetOpen sourceOpen outer inner distinct ordered
            targetWellFormed).elaborate model.Carrier := {
        args := sourceArgs ∘ Fin.cast
          (WireJoinSoundness.boundaryLengthEq sourceOpen.val outer inner
            distinct)
        classes := targetClasses
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast
            (WireJoinSoundness.boundaryLengthEq sourceOpen.val outer inner
              distinct) targetPosition
          have classEq :=
            WireJoinSoundness.boundaryClass_map sourceOpen.val outer inner
              distinct targetPosition
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          rw [sourceArgsEq] at sourceAgrees
          change targetClasses
              ((WireJoinSoundness.targetOpenRaw sourceOpen.val outer inner
                distinct).boundaryClass targetPosition) =
            sourceArgs sourcePosition
          rw [classEq]
          exact (congrFun classesAgree
            (sourceOpen.val.boundaryClass sourcePosition)).symm.trans
              sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      rw [Diagram.ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      exact classesAgree

private theorem orderedReceipt_sound
    (context : ProofContext signature)
    (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount)
    (payload : CongruencePayload input first second)
    (outer inner : Fin input.val.wireCount)
    (outputs :
      (outer = payload.firstOutput ∧ inner = payload.secondOutput) ∨
        (outer = payload.secondOutput ∧ inner = payload.firstOutput))
    (receipt : StepReceipt input)
    (realizes : receipt.Realizes
      (WireJoinSoundness.Target input.val outer inner)
      (joinWireProvenance input.val outer inner)
      (joinWireInterfaceTransport input.val outer inner))
    (distinct : outer ≠ inner)
    (ordered :
      input.val.Encloses (input.val.wires outer).scope
        (input.val.wires inner).scope) :
    SuccessfulReceiptSound context orientation input
      (.congruenceJoin first second payload) receipt := by
  have targetWellFormed :
      (WireJoinSoundness.Target input.val outer inner).WellFormed signature :=
    realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped transport =>
      WireJoinSoundness.targetOpen
        (OpenProofState.asCheckedOpen {
          diagram := input
          boundary := boundary
          boundary_root_scoped := sourceRoot
        })
        outer inner distinct ordered targetWellFormed)
    (operationalIso := fun boundary sourceRoot mapped transport => by
      apply realizes.operationalIso_to_rawResultOpen transport
        (boundary.map
          (WireJoinSoundness.wireMap input.val outer inner distinct))
      have expected := realizes.transportBoundary_expected transport
      have rawEq :=
        WireJoinSoundness.interface_transportBoundary_eq_map input.val outer
          inner distinct boundary _ expected
      simpa [rawEq] using expected)
  intro boundary sourceRoot mapped transport valid args
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target :=
    WireJoinSoundness.targetOpen source.asCheckedOpen outer inner distinct
      ordered targetWellFormed
  let model := Lambda.canonicalModel
  let named := Theory.interpretDefinitions context.definitions
  let simulation := semanticSimulation input payload boundary sourceRoot outer
    inner outputs distinct ordered targetWellFormed model named
  let forwardRoot := rootContext input payload boundary sourceRoot outer inner
    outputs distinct ordered targetWellFormed model named .forward
  let backwardRoot := rootContext input payload boundary sourceRoot outer inner
    outputs distinct ordered targetWellFormed model named .backward
  have forwardAllowed :
      simulation.Allowed .forward input.val.root := by
    trivial
  have backwardAllowed :
      simulation.Allowed .backward input.val.root := by
    trivial
  have forwardBoundary :=
    boundaryWitness input payload boundary sourceRoot outer inner outputs
      distinct ordered targetWellFormed .forward model named args
  have backwardBoundary :=
    boundaryWitness input payload boundary sourceRoot outer inner outputs
      distinct ordered targetWellFormed .backward model named args
  have forwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model named simulation .forward forwardRoot
      forwardAllowed args
      (args ∘ Fin.cast
        (WireJoinSoundness.boundaryLengthEq source.asCheckedOpen.val outer inner
          distinct))
      forwardBoundary
  have backwardSemantic :=
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model named simulation .backward backwardRoot
      backwardAllowed args
      (args ∘ Fin.cast
        (WireJoinSoundness.boundaryLengthEq source.asCheckedOpen.val outer inner
          distinct))
      backwardBoundary
  dsimp only
  unfold DirectedEntailment
  constructor
  · intro sourceDenotes
    have targetDenotes := forwardSemantic sourceDenotes
    simpa [source, target, model, named] using targetDenotes
  · intro targetDenotes
    apply backwardSemantic
    simpa [source, target, model, named] using targetDenotes

private theorem applyCongruenceJoin_realizes_first
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (receipt : StepReceipt input)
    (ordered :
      input.val.Encloses (input.val.wires payload.firstOutput).scope
        (input.val.wires payload.secondOutput).scope)
    (happly : Rule.applyCongruenceJoin input payload = .ok receipt) :
    receipt.Realizes
      (WireJoinSoundness.Target input.val payload.firstOutput
        payload.secondOutput)
      (joinWireProvenance input.val payload.firstOutput payload.secondOutput)
      (joinWireInterfaceTransport input.val payload.firstOutput
        payload.secondOutput) := by
  have realizes := Rule.applyCongruenceJoin_realizes happly
  unfold Rule.congruenceJoinRaw Rule.congruenceJoinWireProvenance
    Rule.congruenceJoinInterfaceTransport at realizes
  have planEq :
      Rule.congruenceJoinPlan input payload = {
        raw := WireJoinSoundness.Target input.val payload.firstOutput
          payload.secondOutput
        provenance :=
          joinWireProvenance input.val payload.firstOutput payload.secondOutput
        interface :=
          joinWireInterfaceTransport input.val payload.firstOutput
            payload.secondOutput
      } := by
    simp [Rule.congruenceJoinPlan, ordered]
  rw [planEq] at realizes
  exact realizes

private theorem applyCongruenceJoin_realizes_second
    (input : Diagram.CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : CongruencePayload input first second)
    (receipt : StepReceipt input)
    (ordered :
      ¬ input.val.Encloses (input.val.wires payload.firstOutput).scope
        (input.val.wires payload.secondOutput).scope)
    (happly : Rule.applyCongruenceJoin input payload = .ok receipt) :
    receipt.Realizes
      (WireJoinSoundness.Target input.val payload.secondOutput
        payload.firstOutput)
      (joinWireProvenance input.val payload.secondOutput payload.firstOutput)
      (joinWireInterfaceTransport input.val payload.secondOutput
        payload.firstOutput) := by
  have realizes := Rule.applyCongruenceJoin_realizes happly
  unfold Rule.congruenceJoinRaw Rule.congruenceJoinWireProvenance
    Rule.congruenceJoinInterfaceTransport at realizes
  have planEq :
      Rule.congruenceJoinPlan input payload = {
        raw := WireJoinSoundness.Target input.val payload.secondOutput
          payload.firstOutput
        provenance :=
          joinWireProvenance input.val payload.secondOutput payload.firstOutput
        interface :=
          joinWireInterfaceTransport input.val payload.secondOutput
            payload.firstOutput
      } := by
    simp [Rule.congruenceJoinPlan, ordered]
  rw [planEq] at realizes
  exact realizes

theorem applyCongruenceJoin_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount)
    (payload : CongruencePayload input first second)
    (receipt : StepReceipt input)
    (happly : Rule.applyCongruenceJoin input payload = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.congruenceJoin first second payload) receipt := by
  by_cases ordered :
      input.val.Encloses (input.val.wires payload.firstOutput).scope
        (input.val.wires payload.secondOutput).scope
  · have orderedRealizes : receipt.Realizes
        (WireJoinSoundness.Target input.val payload.firstOutput
          payload.secondOutput)
        (joinWireProvenance input.val payload.firstOutput payload.secondOutput)
        (joinWireInterfaceTransport input.val payload.firstOutput
          payload.secondOutput) := by
      exact applyCongruenceJoin_realizes_first input payload receipt ordered
        happly
    exact orderedReceipt_sound context orientation input first second payload
      payload.firstOutput payload.secondOutput
      (Or.inl ⟨rfl, rfl⟩) receipt orderedRealizes
      payload.outputsDistinct ordered
  · have reverseOrdered :
        input.val.Encloses (input.val.wires payload.secondOutput).scope
          (input.val.wires payload.firstOutput).scope := by
      have firstEncloses :
          input.val.Encloses (input.val.wires payload.firstOutput).scope
            payload.region := by
        have scope :=
          input.property.wire_scopes_enclose payload.firstOutput
            { node := first, port := .output } payload.firstOutput_occurs
        simpa [payload.firstNode] using scope
      have secondEncloses :
          input.val.Encloses (input.val.wires payload.secondOutput).scope
            payload.region := by
        have scope :=
          input.property.wire_scopes_enclose payload.secondOutput
            { node := second, port := .output } payload.secondOutput_occurs
        simpa [payload.secondNode] using scope
      exact (input.val.enclosingRegions_comparable secondEncloses
        firstEncloses).resolve_right ordered
    have orderedRealizes : receipt.Realizes
        (WireJoinSoundness.Target input.val payload.secondOutput
          payload.firstOutput)
        (joinWireProvenance input.val payload.secondOutput payload.firstOutput)
        (joinWireInterfaceTransport input.val payload.secondOutput
          payload.firstOutput) := by
      exact applyCongruenceJoin_realizes_second input payload receipt ordered
        happly
    exact orderedReceipt_sound context orientation input first second payload
      payload.secondOutput payload.firstOutput
      (Or.inr ⟨rfl, rfl⟩) receipt orderedRealizes
      (fun equality => payload.outputsDistinct equality.symm) reverseOrdered

end CongruenceSoundness

end VisualProof.Rule
