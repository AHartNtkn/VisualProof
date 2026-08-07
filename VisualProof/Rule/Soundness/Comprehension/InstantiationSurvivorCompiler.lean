import VisualProof.Rule.Soundness.Comprehension.InstantiationDropNodeCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Compile the copied diagram while omitting exactly the processed atoms that
the executor's final compaction removes. -/
def compileSurvivorRegion?
    (state : InstantiationState origin parameterCount proxyCount) :
    Nat → (region : Fin state.diagram.val.regionCount) →
      (context : Concrete.Elaboration.WireContext state.diagram.val) →
      Concrete.Elaboration.BinderContext state.diagram.val rels →
      Option (Region  context.length rels)
  | 0, _, _, _ => none
  | fuel + 1, region, context, binders => do
      let extended := context.extend region
      let items ← Concrete.Elaboration.compileOccurrencesWith?
        state.diagram.val (compileSurvivorRegion?  state fuel)
        extended binders
        ((Concrete.Elaboration.localOccurrences state.diagram.val region).filter
          (dropOccurrenceSurvives state))
      pure (Concrete.Elaboration.finishRegion state.diagram.val context region
        items)

/-- A single surviving occurrence compiles identically before and after dense
node compaction, provided recursive child compilation does. -/
theorem drop_compileOccurrence_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (dropRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : Concrete.Elaboration.WireContext state.diagram.val) →
      Concrete.Elaboration.BinderContext state.diagram.val rels →
      Option (Region  context.length rels))
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : Concrete.Elaboration.WireContext state.diagram.val) →
      Concrete.Elaboration.BinderContext state.diagram.val rels →
      Option (Region  context.length rels))
    (recurse_eq : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels),
      dropRecurse region context binders =
        sourceRecurse region context binders)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      (dropInstantiationAtomsRaw state).regionCount
      (dropInstantiationAtomsRaw state).nodeCount) :
    Concrete.Elaboration.compileOccurrenceWith?
        (dropInstantiationAtomsRaw state) dropRecurse context binders
        occurrence =
      Concrete.Elaboration.compileOccurrenceWith?  state.diagram.val
        sourceRecurse context binders (dropOccurrenceOrigin state occurrence) := by
  cases occurrence with
  | node node =>
      exact drop_compileNode_origin state context binders node
  | child child =>
      cases hregion : state.diagram.val.regions child with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          rfl
      | cut parent =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          exact congrArg (fun result => result.bind fun body =>
            some (Item.cut body))
            (recurse_eq child context binders)
      | bubble parent arity =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?,
            InstantiationDrop.raw_regions, hregion, dropOccurrenceOrigin]
          exact congrArg (fun result => result.bind fun body =>
            some (Item.bubble arity body))
            (recurse_eq child context (binders.push child arity))

/-- Pointwise occurrence equality lifts to the ordered conjunction compiler
without changing item order or inserting a wire renaming. -/
theorem drop_compileOccurrences_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (dropRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : Concrete.Elaboration.WireContext state.diagram.val) →
      Concrete.Elaboration.BinderContext state.diagram.val rels →
      Option (Region  context.length rels))
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin state.diagram.val.regionCount) →
      (context : Concrete.Elaboration.WireContext state.diagram.val) →
      Concrete.Elaboration.BinderContext state.diagram.val rels →
      Option (Region  context.length rels))
    (recurse_eq : ∀ {rels : RelCtx}
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels),
      dropRecurse region context binders =
        sourceRecurse region context binders)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binders : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      (dropInstantiationAtomsRaw state).regionCount
      (dropInstantiationAtomsRaw state).nodeCount)) :
    Concrete.Elaboration.compileOccurrencesWith?
        (dropInstantiationAtomsRaw state) dropRecurse context binders
        occurrences =
      Concrete.Elaboration.compileOccurrencesWith?  state.diagram.val
        sourceRecurse context binders
          (occurrences.map (dropOccurrenceOrigin state)) := by
  induction occurrences with
  | nil => rfl
  | cons occurrence tail ih =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?, List.map_cons]
      rw [drop_compileOccurrence_origin state dropRecurse sourceRecurse
        recurse_eq context binders occurrence, ih]
      rfl

@[simp] theorem drop_exactScopeWires
    (state : InstantiationState origin parameterCount proxyCount)
    (region : Fin state.diagram.val.regionCount) :
    Concrete.Elaboration.exactScopeWires (dropInstantiationAtomsRaw state)
        region =
      Concrete.Elaboration.exactScopeWires state.diagram.val region := by
  rfl

@[simp] theorem drop_finishRegion
    (state : InstantiationState origin parameterCount proxyCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (region : Fin state.diagram.val.regionCount)
    (items : ItemSeq  (context.extend region).length rels) :
    Concrete.Elaboration.finishRegion (dropInstantiationAtomsRaw state)
        context region items =
      Concrete.Elaboration.finishRegion state.diagram.val context region
        items := by
  rfl

/-- The authoritative compiler on the compacted executor result is exactly
the survivor-view compiler on the copied diagram. -/
theorem drop_compileRegion_eq_survivor
    (state : InstantiationState origin parameterCount proxyCount) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : Concrete.Elaboration.WireContext state.diagram.val)
      (binders : Concrete.Elaboration.BinderContext state.diagram.val rels),
      Concrete.Elaboration.compileRegion?
          (dropInstantiationAtomsRaw state) fuel region context binders =
        compileSurvivorRegion?  state fuel region context binders := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region context binders
      rfl
  | succ fuel ih =>
      intro region context binders
      unfold Concrete.Elaboration.compileRegion? compileSurvivorRegion?
      dsimp only
      change (Concrete.Elaboration.compileOccurrencesWith?
          (dropInstantiationAtomsRaw state)
          (Concrete.Elaboration.compileRegion?
            (dropInstantiationAtomsRaw state) fuel)
          (context.extend region) binders
          (Concrete.Elaboration.localOccurrences
            (dropInstantiationAtomsRaw state) region)).bind
            (fun items => some (Concrete.Elaboration.finishRegion
              (dropInstantiationAtomsRaw state) context region items)) =
        (Concrete.Elaboration.compileOccurrencesWith?
          state.diagram.val (compileSurvivorRegion?  state fuel)
          (context.extend region) binders
          ((Concrete.Elaboration.localOccurrences state.diagram.val
            region).filter (dropOccurrenceSurvives state))).bind
            (fun items => some (Concrete.Elaboration.finishRegion
              state.diagram.val context region items))
      have compiled := drop_compileOccurrences_origin state
        (Concrete.Elaboration.compileRegion?
          (dropInstantiationAtomsRaw state) fuel)
        (compileSurvivorRegion?  state fuel)
        (fun child childContext childBinders =>
          ih child childContext childBinders)
        (context.extend region) binders
        (Concrete.Elaboration.localOccurrences
          (dropInstantiationAtomsRaw state) region)
      rw [dropInstantiationAtomsRaw_localOccurrences_origin state region]
        at compiled
      cases hdrop : Concrete.Elaboration.compileOccurrencesWith?
          (dropInstantiationAtomsRaw state)
          (Concrete.Elaboration.compileRegion?
            (dropInstantiationAtomsRaw state) fuel)
          (context.extend region) binders
          (Concrete.Elaboration.localOccurrences
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
          change some (Concrete.Elaboration.finishRegion
            (dropInstantiationAtomsRaw state) context region items) =
              some (Concrete.Elaboration.finishRegion state.diagram.val
                context region items)
          exact congrArg some (drop_finishRegion state context region items)

/-- Root and local item compilation on the densely compacted executor graph
is exactly survivor-item compilation on the pre-compaction state.  This is
the item-sequence form needed by the authoritative open-root compiler. -/
theorem drop_compileOccurrences_eq_survivor
    (state : InstantiationState origin parameterCount proxyCount)
    (fuel : Nat)
    (region : Fin state.diagram.val.regionCount)
    (context : Concrete.Elaboration.WireContext state.diagram.val)
    (binders : Concrete.Elaboration.BinderContext state.diagram.val rels) :
    Concrete.Elaboration.compileOccurrencesWith?
        (dropInstantiationAtomsRaw state)
        (Concrete.Elaboration.compileRegion?
          (dropInstantiationAtomsRaw state) fuel)
        context binders
        (Concrete.Elaboration.localOccurrences
          (dropInstantiationAtomsRaw state) region) =
      Concrete.Elaboration.compileOccurrencesWith?  state.diagram.val
        (compileSurvivorRegion?  state fuel) context binders
        ((Concrete.Elaboration.localOccurrences state.diagram.val region).filter
          (dropOccurrenceSurvives state)) := by
  have compiled := drop_compileOccurrences_origin state
    (Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw state) fuel)
    (compileSurvivorRegion?  state fuel)
    (fun child childContext childBinders =>
      drop_compileRegion_eq_survivor state fuel child childContext childBinders)
    context binders
    (Concrete.Elaboration.localOccurrences
      (dropInstantiationAtomsRaw state) region)
  rw [dropInstantiationAtomsRaw_localOccurrences_origin state region]
    at compiled
  exact compiled

end InstantiationSemantic

end VisualProof.Rule
