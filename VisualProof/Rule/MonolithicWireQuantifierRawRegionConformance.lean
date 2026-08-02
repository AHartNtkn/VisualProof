import VisualProof.Rule.MonolithicWireQuantifierRawRegionTrace
import VisualProof.Rule.MonolithicWireQuantifierRawOriginAtlas

namespace VisualProof

namespace MonolithicWireQuantifier

open ConcreteWireQuantifier

section RawRegionConformance

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

namespace RelationJoinRawOriginAtlas

open ConcreteWireQuantifier.RelationJoinConstructionTrace

/-- Prefix-local origin of a copied content region.  The content root is the
retained source site; every non-root region remains occurrence-local. -/
def prefixContentRegionOrigin
    (steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content))
    (occurrence : Fin steps.length)
    (region : content.val.diagram.RegionId) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps :=
  if root : region = content.val.diagram.root then
    .inl (steps.get occurrence).sourceRegion
  else
    .inr ⟨occurrence, ⟨region, root⟩⟩

/-- Construction-derived exact region row for a prefix origin. -/
def expectedPrefixRegionData
    (steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)) :
    RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
      (content := content) steps →
      RelationJoinRawRegionData
        (RelationJoinPrefixRegionOrigin (source := source) (dying := dying)
          (content := content) steps)
  | .inl region =>
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (.inl parent)
  | .inr ⟨occurrence, region⟩ =>
      match content.val.diagram.regions region.1 with
      | .sheet => .sheet
      | .cut parent =>
          .cut (prefixContentRegionOrigin steps occurrence parent)

theorem expectedPrefixRegionData_lift
    {steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)}
    (step : VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps) :
    expectedPrefixRegionData (steps ++ [step])
        (prefixRegionOriginLift step origin) =
      match expectedPrefixRegionData steps origin with
      | .sheet => .sheet
      | .cut parent =>
          .cut
            (prefixRegionOriginLift step parent) := by
  cases origin with
  | inl region =>
      cases data : source.val.regions region <;>
        simp [expectedPrefixRegionData, data,
          prefixRegionOriginLift]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, region⟩
      cases data : content.val.diagram.regions region.1 with
      | sheet =>
          simp [expectedPrefixRegionData, data, prefixContentRegionOrigin,
            prefixRegionOriginLift]
      | cut parent =>
          by_cases root : parent = content.val.diagram.root <;>
            simp [expectedPrefixRegionData, data, prefixContentRegionOrigin,
              prefixRegionOriginLift, root]

theorem expectedPrefixRegionData_fresh
    {steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)}
    (step : VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)
    (region : { region : content.val.diagram.RegionId //
      region ≠ content.val.diagram.root }) :
    expectedPrefixRegionData (steps ++ [step])
        (prefixRegionFreshOrigin step region) =
      match content.val.diagram.regions region.1 with
      | .sheet => .sheet
      | .cut parent =>
          .cut
            (if root : parent = content.val.diagram.root then
              .inl step.sourceRegion
            else
              prefixRegionFreshOrigin step ⟨parent, root⟩) := by
  cases data : content.val.diagram.regions region.1 <;>
    simp [expectedPrefixRegionData, data, prefixContentRegionOrigin,
      prefixRegionFreshOrigin]

end RelationJoinRawOriginAtlas

namespace ConcreteWireQuantifier.RelationJoinConstructionTrace

open RelationJoinRawOriginAtlas

/-- One landed prefix region has its exact construction-derived row.  A cut
row carries the landing of its neutral parent origin. -/
def PrefixRegionRowExact {args : List Sig}
    {steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : VisualProof.ConcreteWireQuantifier.RelationJoinConstructionTrace
      source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps)
    (target : final.val.RegionId) : Prop :=
  PrefixRegionLands trace origin target ∧
    match expectedPrefixRegionData steps origin with
    | .sheet => final.val.regions target = .sheet
    | .cut parentOrigin =>
        ∃ parentTarget, final.val.regions target = .cut parentTarget ∧
          PrefixRegionLands trace parentOrigin parentTarget

theorem prefixRegionLands_row_exact {args : List Sig}
    {steps : List (VisualProof.ConcreteWireQuantifier.RelationJoinStep
      source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId} {finalScope : final.val.RegionId}
    (trace : VisualProof.ConcreteWireQuantifier.RelationJoinConstructionTrace
      source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) steps)
    (target : final.val.RegionId)
    (landing : PrefixRegionLands trace origin target) :
    PrefixRegionRowExact trace origin target := by
  induction trace with
  | nil =>
      cases origin with
      | inl region =>
          rcases landing with ⟨sourceRegion, originExact, targetExact⟩
          have regionExact : region = sourceRegion :=
            Sum.inl.inj originExact
          subst sourceRegion
          subst target
          refine ⟨⟨region, rfl, rfl⟩, ?_⟩
          cases data : source.val.regions region with
          | sheet => simpa [expectedPrefixRegionData, data]
          | cut parent =>
              simp only [expectedPrefixRegionData, data]
              exact ⟨parent, rfl, parent, rfl, rfl⟩
      | inr occurrence => exact Fin.elim0 occurrence.1
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst_vars
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      rcases landing with prior | fresh
      · rcases prior with
          ⟨priorOrigin, priorTarget, priorLanding, rfl, rfl⟩
        have priorRow := induction priorOrigin priorTarget priorLanding
        refine ⟨Or.inl ⟨priorOrigin, priorTarget, priorLanding, rfl, rfl⟩, ?_⟩
        rw [expectedPrefixRegionData_lift]
        rcases priorRow with ⟨_, priorData⟩
        cases expected : expectedPrefixRegionData _ priorOrigin with
        | sheet =>
            rw [expected] at priorData
            exact step.checkedPriorRegion_sheet _ priorData
        | cut parentOrigin =>
            rw [expected] at priorData
            obtain ⟨parentTarget, targetData, parentLanding⟩ := priorData
            exact ⟨step.checkedPriorRegion parentTarget,
              step.checkedPriorRegion_cut _ _ targetData,
              Or.inl ⟨parentOrigin, parentTarget, parentLanding, rfl, rfl⟩⟩
      · rcases fresh with ⟨region, rfl, rfl⟩
        refine ⟨Or.inr ⟨region, rfl, rfl⟩, ?_⟩
        rw [expectedPrefixRegionData_fresh]
        cases data : content.val.diagram.regions region.1 with
        | sheet =>
            exact step.checkedFragmentRegion_sheet region.1 region.2 data
        | cut parent =>
            by_cases root : parent = content.val.diagram.root
            · simp only [root, dif_pos]
              refine ⟨step.checkedFragmentRegion parent,
                step.checkedFragmentRegion_cut region.1 parent region.2 data,
                ?_⟩
              rw [root, step.checkedFragmentRegion_root_eq_checkedRegionImage]
              exact prefixRegionLands_source _ step.sourceRegion
            · simp only [dif_neg root]
              exact ⟨step.checkedFragmentRegion parent,
                step.checkedFragmentRegion_cut region.1 parent region.2 data,
                Or.inr ⟨⟨parent, root⟩, rfl, rfl⟩⟩

/-- Final exhausted-wire deletion transports the exact prefix row without
changing its neutral origin or parent relation. -/
def PlainPrefixRegionRowExact
    (result : VisualProof.ConcreteWireQuantifier.RelationJoinResult
      source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) result.steps)
    (target : result.plainFinal.val.RegionId) : Prop :=
  plainPrefixRegionLands result origin target ∧
    match expectedPrefixRegionData result.steps origin with
    | .sheet => result.plainFinal.val.regions target = .sheet
    | .cut parentOrigin =>
        ∃ parentTarget, result.plainFinal.val.regions target = .cut parentTarget ∧
          plainPrefixRegionLands result parentOrigin parentTarget

theorem plainPrefixRegionLands_row_exact
    (result : VisualProof.ConcreteWireQuantifier.RelationJoinResult
      source dying content parameters)
    (origin : RelationJoinPrefixRegionOrigin (source := source)
      (dying := dying) (content := content) result.steps)
    (target : result.plainFinal.val.RegionId)
    (landing : plainPrefixRegionLands result origin target) :
    PlainPrefixRegionRowExact result origin target := by
  rcases landing with ⟨bound, boundLanding, rfl⟩
  have boundRow := prefixRegionLands_row_exact result.construction_trace
    origin bound boundLanding
  refine ⟨⟨bound, boundLanding, rfl⟩, ?_⟩
  rcases boundRow with ⟨_, boundData⟩
  cases expected : expectedPrefixRegionData result.steps origin with
  | sheet =>
      rw [expected] at boundData
      exact result.plainBoundRegionImage_sheet bound boundData
  | cut parentOrigin =>
      rw [expected] at boundData
      obtain ⟨parentBound, data, parentLanding⟩ := boundData
      exact ⟨result.plainBoundRegionImage parentBound,
        result.plainBoundRegionImage_cut bound parentBound data,
        ⟨parentBound, parentLanding, rfl⟩⟩

end ConcreteWireQuantifier.RelationJoinConstructionTrace

namespace RelationJoinRawOriginAtlas

theorem expectedPrefixRegionData_result
    (result : VisualProof.ConcreteWireQuantifier.RelationJoinResult
      source dying content parameters)
    (origin : RelationJoinRawRegionOrigin result) :
    expectedPrefixRegionData result.steps origin =
      expectedRegionData result origin := by
  cases origin with
  | inl region =>
      cases data : source.val.regions region <;>
        simp [expectedPrefixRegionData, expectedRegionData, data]
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, region⟩
      cases data : content.val.diagram.regions region.1 <;>
        simp [expectedPrefixRegionData, expectedRegionData,
          prefixContentRegionOrigin, contentRegionOrigin, data]

/-- Every atlas region row, including every occurrence-local copied region,
has exactly the construction-derived sheet/cut data and neutral parent
origin. -/
theorem ofResult_region_exact
    (result : VisualProof.ConcreteWireQuantifier.RelationJoinResult
      source dying content parameters)
    (origin : RelationJoinRawRegionOrigin result) :
    (match result.plainFinal.val.regions
        ((ofResult result).regionEquiv.symm origin) with
      | .sheet => RelationJoinRawRegionData.sheet
      | .cut parent =>
          RelationJoinRawRegionData.cut
            ((ofResult result).regionEquiv parent)) =
      expectedRegionData result origin := by
  have landing := ofResult_region_inverse_lands result origin
  have row :=
    ConcreteWireQuantifier.RelationJoinConstructionTrace.plainPrefixRegionLands_row_exact
      result origin _ landing
  rcases row with ⟨_, rowData⟩
  have expectedExact := expectedPrefixRegionData_result result origin
  cases expected : expectedPrefixRegionData result.steps origin with
  | sheet =>
      rw [expected] at rowData
      rw [← expectedExact, expected, rowData]
  | cut parentOrigin =>
      rw [expected] at rowData
      obtain ⟨parentTarget, targetData, parentLanding⟩ := rowData
      have parentExact := ofResult_region_exact_of_landing result parentLanding
      rw [← expectedExact, expected, targetData]
      simpa using congrArg RelationJoinRawRegionData.cut parentExact

end RelationJoinRawOriginAtlas

end RawRegionConformance

end MonolithicWireQuantifier

end VisualProof
