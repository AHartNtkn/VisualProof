import VisualProof.Rule.Soundness.Comprehension.InstantiationDropNodeCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Compile the copied diagram while omitting exactly the processed atoms that
the executor's final compaction removes. -/
def compileSurvivorRegion?
    (signature : List Nat)
    (state : InstantiationState origin parameterCount proxyCount) :
    Nat → (region : Fin state.diagram.val.regionCount) →
      (context : ConcreteElaboration.WireContext state.diagram.val) →
      ConcreteElaboration.BinderContext state.diagram.val rels →
      Option (Region signature context.length rels)
  | 0, _, _, _ => none
  | fuel + 1, region, context, binders => do
      let extended := context.extend region
      let items ← ConcreteElaboration.compileOccurrencesWith? signature
        state.diagram.val (compileSurvivorRegion? signature state fuel)
        extended binders
        ((ConcreteElaboration.localOccurrences state.diagram.val region).filter
          (dropOccurrenceSurvives state))
      pure (ConcreteElaboration.finishRegion state.diagram.val context region
        items)

/-- A single surviving occurrence compiles identically before and after dense
node compaction, provided recursive child compilation does. -/
theorem drop_compileOccurrence_origin
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount)
    (dropRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : ConcreteElaboration.WireContext state.diagram.val) →
      ConcreteElaboration.BinderContext state.diagram.val rels →
      Option (Region signature context.length rels))
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : ConcreteElaboration.WireContext state.diagram.val) →
      ConcreteElaboration.BinderContext state.diagram.val rels →
      Option (Region signature context.length rels))
    (recurse_eq : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels),
      dropRecurse region context binders =
        sourceRecurse region context binders)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
    (occurrence : ConcreteElaboration.LocalOccurrence
      (dropInstantiationAtomsRaw state).regionCount
      (dropInstantiationAtomsRaw state).nodeCount) :
    ConcreteElaboration.compileOccurrenceWith? signature
        (dropInstantiationAtomsRaw state) dropRecurse context binders
        occurrence =
      ConcreteElaboration.compileOccurrenceWith? signature state.diagram.val
        sourceRecurse context binders (dropOccurrenceOrigin state occurrence) := by
  cases occurrence with
  | node node =>
      exact drop_compileNode_origin state context binders node
  | child child =>
      cases hregion : state.diagram.val.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          rfl
      | cut parent =>
          simp only [ConcreteElaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          exact congrArg (fun result => result.bind fun body =>
            some (Item.cut body))
            (recurse_eq child context binders)
      | bubble parent arity =>
          simp only [ConcreteElaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          exact congrArg (fun result => result.bind fun body =>
            some (Item.bubble arity body))
            (recurse_eq child context (binders.push child arity))

/-- Pointwise occurrence equality lifts to the ordered conjunction compiler
without changing item order or inserting a wire renaming. -/
theorem drop_compileOccurrences_origin
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount)
    (dropRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : ConcreteElaboration.WireContext state.diagram.val) →
      ConcreteElaboration.BinderContext state.diagram.val rels →
      Option (Region signature context.length rels))
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : ConcreteElaboration.WireContext state.diagram.val) →
      ConcreteElaboration.BinderContext state.diagram.val rels →
      Option (Region signature context.length rels))
    (recurse_eq : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels),
      dropRecurse region context binders =
        sourceRecurse region context binders)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (binders : ConcreteElaboration.BinderContext state.diagram.val rels)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      (dropInstantiationAtomsRaw state).regionCount
      (dropInstantiationAtomsRaw state).nodeCount)) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (dropInstantiationAtomsRaw state) dropRecurse context binders
        occurrences =
      ConcreteElaboration.compileOccurrencesWith? signature state.diagram.val
        sourceRecurse context binders
          (occurrences.map (dropOccurrenceOrigin state)) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence tail ih =>
      simp only [ConcreteElaboration.compileOccurrencesWith?, List.map_cons]
      rw [drop_compileOccurrence_origin state dropRecurse sourceRecurse
        recurse_eq context binders occurrence, ih]
      rfl

@[simp] theorem drop_exactScopeWires
    (state : InstantiationState origin parameterCount proxyCount)
    (region : Fin state.diagram.val.regionCount) :
    ConcreteElaboration.exactScopeWires (dropInstantiationAtomsRaw state)
        region =
      ConcreteElaboration.exactScopeWires state.diagram.val region := by
  rfl

@[simp] theorem drop_finishRegion
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (items : ItemSeq signature (context.extend region).length rels) :
    ConcreteElaboration.finishRegion (dropInstantiationAtomsRaw state)
        context region items =
      ConcreteElaboration.finishRegion state.diagram.val context region
        items := by
  rfl

/-- The authoritative compiler on the compacted executor result is exactly
the survivor-view compiler on the copied diagram. -/
theorem drop_compileRegion_eq_survivor
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels),
      ConcreteElaboration.compileRegion? signature
          (dropInstantiationAtomsRaw state) fuel region context binders =
        compileSurvivorRegion? signature state fuel region context binders := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region context binders
      rfl
  | succ fuel ih =>
      intro region context binders
      unfold ConcreteElaboration.compileRegion? compileSurvivorRegion?
      dsimp only
      change (ConcreteElaboration.compileOccurrencesWith? signature
          (dropInstantiationAtomsRaw state)
          (ConcreteElaboration.compileRegion? signature
            (dropInstantiationAtomsRaw state) fuel)
          (context.extend region) binders
          (ConcreteElaboration.localOccurrences
            (dropInstantiationAtomsRaw state) region)).bind
            (fun items => some (ConcreteElaboration.finishRegion
              (dropInstantiationAtomsRaw state) context region items)) =
        (ConcreteElaboration.compileOccurrencesWith? signature
          state.diagram.val (compileSurvivorRegion? signature state fuel)
          (context.extend region) binders
          ((ConcreteElaboration.localOccurrences state.diagram.val
            region).filter (dropOccurrenceSurvives state))).bind
            (fun items => some (ConcreteElaboration.finishRegion
              state.diagram.val context region items))
      have compiled := drop_compileOccurrences_origin state
        (ConcreteElaboration.compileRegion? signature
          (dropInstantiationAtomsRaw state) fuel)
        (compileSurvivorRegion? signature state fuel)
        (fun child childContext childBinders =>
          ih child childContext childBinders)
        (context.extend region) binders
        (ConcreteElaboration.localOccurrences
          (dropInstantiationAtomsRaw state) region)
      rw [dropInstantiationAtomsRaw_localOccurrences_origin state region]
        at compiled
      cases hdrop : ConcreteElaboration.compileOccurrencesWith? signature
          (dropInstantiationAtomsRaw state)
          (ConcreteElaboration.compileRegion? signature
            (dropInstantiationAtomsRaw state) fuel)
          (context.extend region) binders
          (ConcreteElaboration.localOccurrences
            (dropInstantiationAtomsRaw state) region) with
      | none =>
          rw [hdrop] at compiled
          have hsource := compiled.symm
          rw [hsource]
          rfl
      | some items =>
          rw [hdrop] at compiled
          have hsource := compiled.symm
          rw [hsource]
          change some (ConcreteElaboration.finishRegion
            (dropInstantiationAtomsRaw state) context region items) =
              some (ConcreteElaboration.finishRegion state.diagram.val
                context region items)
          exact congrArg some (drop_finishRegion state context region items)

end InstantiationSemantic

end VisualProof.Rule
