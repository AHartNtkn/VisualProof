import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

/-- The scope of a surviving source wire also survives abstraction. -/
theorem wireScope_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    trace.domains.regions.survives (input.val.wires wire).scope = true := by
  apply (region_survives_iff input occurrences _).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, scopeSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at scopeSelected
  have internal : wire ∈
      (occurrences.get index).selection.internalWires :=
    ((occurrences.get index).selection.mem_internalWires wire).2
      (Or.inl (((occurrences.get index).selection.mem_selectedRegions _).1
        scopeSelected))
  exact ((wire_survives_iff input occurrences wire).1 survives) (by
    rw [abstractionWires, List.mem_flatMap]
    exact ⟨occurrences.get index, List.get_mem _ _, internal⟩)

/-- Exact wire-scope transport implemented by the raw abstraction executor. -/
theorem targetWire_scope
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    (trace.diagram.wires (trace.targetWire wire survives)).scope =
      trace.targetRegion (input.val.wires wire).scope
        (trace.wireScope_survives wire survives) := by
  have scopeSurvives := trace.wireScope_survives wire survives
  have result := trace.abstractWire?_targetWire wire survives
  rw [trace.domains.regions.index?_index _ scopeSurvives] at result
  have equal := Option.some.inj result
  simpa only [targetRegion] using congrArg CWire.scope equal.symm

theorem targetWire_origin_index
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (compact : Fin trace.domains.wires.count) :
    trace.targetWire (trace.domains.wires.origin compact)
        (trace.domains.wires.origin_survives compact) = compact := by
  unfold targetWire
  exact trace.domains.wires.index_origin compact

/-- Lexical context evidence for abstraction.  Every target wire has its
certified surviving source origin in the source context.  Source contexts may
contain additional wires deleted inside focused occurrence bodies. -/
structure ContextWitness
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram) : Prop where
  origin_mem : ∀ wire, wire ∈ targetContext →
    trace.domains.wires.origin wire ∈ sourceContext

namespace ContextWitness

def empty
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    ContextWitness trace [] [] where
  origin_mem := by simp

noncomputable def sourceIndex
    (witness : ContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) : Fin sourceContext.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (witness.origin_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_lookup
    (witness : ContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.lookup?
        (trace.domains.wires.origin (targetContext.get targetIndex)) =
      some (witness.sourceIndex targetIndex) :=
  Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
    (witness.origin_mem (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_get
    (witness : ContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.get (witness.sourceIndex targetIndex) =
      trace.domains.wires.origin (targetContext.get targetIndex) :=
  ConcreteElaboration.WireContext.lookup?_sound
    (witness.sourceIndex_lookup targetIndex)

noncomputable def indexRelation
    (witness : ContextWitness trace sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  ConcreteElaboration.ContextIndexRelation.backwardMap witness.sourceIndex

noncomputable def targetEnvironment
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceEnvironment : Fin sourceContext.length → D) :
    Fin targetContext.length → D :=
  sourceEnvironment ∘ witness.sourceIndex

theorem targetEnvironment_agrees
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceEnvironment : Fin sourceContext.length → D) :
    witness.indexRelation.EnvironmentsAgree sourceEnvironment
      (witness.targetEnvironment sourceEnvironment) := by
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    _ _ _).2
  rfl

/-- Transport a context witness across an extension equality without changing
the represented target wires. -/
def castTarget
    (witness : ContextWitness trace sourceContext targetContext)
    {otherTarget : ConcreteElaboration.WireContext trace.diagram}
    (equal : otherTarget = targetContext) :
    ContextWitness trace sourceContext otherTarget := by
  subst otherTarget
  exact witness

theorem castTarget_agrees
    (witness : ContextWitness trace sourceContext targetContext)
    {otherTarget : ConcreteElaboration.WireContext trace.diagram}
    (equal : otherTarget = targetContext)
    (sourceEnvironment : Fin sourceContext.length → D)
    (targetEnvironment : Fin targetContext.length → D)
    (agreement : witness.indexRelation.EnvironmentsAgree sourceEnvironment
      targetEnvironment) :
    (witness.castTarget equal).indexRelation.EnvironmentsAgree
      sourceEnvironment
      (fun index => targetEnvironment
        (Fin.cast (congrArg List.length equal) index)) := by
  subst otherTarget
  simpa [castTarget] using agreement

/-- Extend the origin relation through a surviving source region. Exact local
wires correspond by compact scope injectivity. -/
def extend
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {trace : AbstractionRawTrace input wrap comprehension occurrences raw}
    {sourceContext : ConcreteElaboration.WireContext input.val}
    {targetContext : ConcreteElaboration.WireContext trace.diagram}
    (witness : ContextWitness trace sourceContext targetContext)
    (region : Fin input.val.regionCount)
    (regionSurvives : trace.domains.regions.survives region = true) :
    ContextWitness trace (sourceContext.extend region)
      (targetContext.extend (trace.regionMap region)) where
  origin_mem := by
    intro targetWire targetMember
    rw [ConcreteElaboration.WireContext.extend] at targetMember ⊢
    rcases List.mem_append.mp targetMember with outer | hlocal
    · exact List.mem_append_left _ (witness.origin_mem targetWire outer)
    · apply List.mem_append_right sourceContext
      apply (ConcreteElaboration.mem_exactScopeWires input.val region _).2
      have targetScope :=
        (ConcreteElaboration.mem_exactScopeWires trace.diagram
          (trace.regionMap region) targetWire).1 hlocal
      let original := trace.domains.wires.origin targetWire
      have originalSurvives :
          trace.domains.wires.survives original = true :=
        trace.domains.wires.origin_survives targetWire
      have mapped : trace.targetWire original originalSurvives = targetWire :=
        trace.targetWire_origin_index targetWire
      have scopeTransport := trace.targetWire_scope original originalSurvives
      rw [mapped, targetScope] at scopeTransport
      rw [trace.regionMap_of_survives region regionSurvives] at scopeTransport
      exact trace.targetRegion_injective scopeTransport.symm

end ContextWitness

end AbstractionRawTrace

end VisualProof.Rule
