import VisualProof.Rule.Soundness
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

/-- Relate exposed classes when they contain the same ordered boundary
position.  The relation is intentionally many-to-many: unequal alias
partitions may relate several fine classes to one coarse class. -/
def orderedBoundaryRelation
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity) :
    Diagram.ConcreteElaboration.ContextIndexRelation
      source.externalClasses target.externalClasses where
  Rel sourceClass targetClass :=
    ∃ position : Fin sourceArity,
      source.boundary position = sourceClass ∧
        target.boundary (Fin.cast sameArity position) = targetClass

/-- Construct the coarse-or-fine target boundary assignment only after the
active source denotation has produced it through the local implication. -/
theorem proofDependentBoundaryWitness_forward
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (localLaw : denoteOpen model named source sourceArgs →
      denoteOpen model named target
        (sourceArgs ∘ Fin.cast sameArity.symm)) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .forward source target (orderedBoundaryRelation source target sameArity)
      model named sourceArgs (sourceArgs ∘ Fin.cast sameArity.symm) := by
  intro sourceAssignment sourceArgsEq sourceBody
  obtain ⟨targetAssignment, targetArgsEq, targetBody⟩ :=
    localLaw ⟨sourceAssignment, sourceArgsEq, sourceBody⟩
  refine ⟨targetAssignment, targetArgsEq, ?_⟩
  intro sourceClass targetClass related
  obtain ⟨position, rfl, rfl⟩ := related
  calc
    sourceAssignment.classes (source.boundary position) =
        sourceAssignment.args position := sourceAssignment.agrees position
    _ = sourceArgs position := congrFun sourceArgsEq position
    _ = (sourceArgs ∘ Fin.cast sameArity.symm)
        (Fin.cast sameArity position) := by
          congr 1
    _ = targetAssignment.args (Fin.cast sameArity position) :=
      (congrFun targetArgsEq (Fin.cast sameArity position)).symm
    _ = targetAssignment.classes
        (target.boundary (Fin.cast sameArity position)) :=
      (targetAssignment.agrees (Fin.cast sameArity position)).symm

/-- Backward simulation is the exact active-target dual: the source
assignment is chosen only after target denotation has justified it. -/
theorem proofDependentBoundaryWitness_backward
    (source : OpenDiagram signature sourceArity)
    (target : OpenDiagram signature targetArity)
    (sameArity : sourceArity = targetArity)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin sourceArity → model.Carrier)
    (localLaw : denoteOpen model named target
        (sourceArgs ∘ Fin.cast sameArity.symm) →
      denoteOpen model named source sourceArgs) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .backward source target (orderedBoundaryRelation source target sameArity)
      model named sourceArgs (sourceArgs ∘ Fin.cast sameArity.symm) := by
  intro targetAssignment targetArgsEq targetBody
  obtain ⟨sourceAssignment, sourceArgsEq, sourceBody⟩ :=
    localLaw ⟨targetAssignment, targetArgsEq, targetBody⟩
  refine ⟨sourceAssignment, sourceArgsEq, ?_⟩
  intro sourceClass targetClass related
  obtain ⟨position, rfl, rfl⟩ := related
  calc
    sourceAssignment.classes (source.boundary position) =
        sourceAssignment.args position := sourceAssignment.agrees position
    _ = sourceArgs position := congrFun sourceArgsEq position
    _ = (sourceArgs ∘ Fin.cast sameArity.symm)
        (Fin.cast sameArity position) := by
          congr 1
    _ = targetAssignment.args (Fin.cast sameArity position) :=
      (congrFun targetArgsEq (Fin.cast sameArity position)).symm
    _ = targetAssignment.classes
        (target.boundary (Fin.cast sameArity position)) :=
      (targetAssignment.agrees (Fin.cast sameArity position)).symm

namespace StrictAliasPartitionExamples

/-- Two ordered boundary positions remain distinct structurally, while the
active body proves their semantic values equal. -/
def equalityFineBoundary : OpenDiagram [] 2 where
  externalClasses := 2
  boundary := id
  boundary_surjective := fun external => ⟨external, rfl⟩
  body := .mk 0 (.cons (.equation 1 (.port 0)) .nil)

/-- Active denotation, rather than an unconditional premise, supplies the
equality needed to inhabit the strictly coarser aliased boundary. -/
theorem equalityFineBoundary_entails_aliased
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    denoteOpen model named equalityFineBoundary args →
      denoteOpen model named aliasedBinaryBoundaryExample args := by
  rintro ⟨sourceAssignment, rfl, sourceLocal, sourceItems⟩
  have sourceEquality : sourceAssignment.args 0 =
      sourceAssignment.args 1 := by
    have itemEquality :
        sourceAssignment.classes (equalityFineBoundary.boundary 1) =
          sourceAssignment.classes (equalityFineBoundary.boundary 0) := by
      change sourceAssignment.classes (equalityFineBoundary.boundary 1) =
        sourceAssignment.classes (equalityFineBoundary.boundary 0)
      calc
        _ = model.eval (.port (0 : Fin 2)) sourceAssignment.classes := by
          simpa [equalityFineBoundary] using sourceItems.1
        _ = _ := by
          simpa [equalityFineBoundary] using
            model.eval_port (0 : Fin 2) sourceAssignment.classes
    exact (sourceAssignment.agrees 0).symm |>.trans
      (itemEquality.symm.trans (sourceAssignment.agrees 1))
  obtain ⟨targetAssignment, htargetArgs⟩ :=
    (boundaryAssignment_iff_aliasConsistent
      aliasedBinaryBoundaryExample sourceAssignment.args).2
        ((aliasedBinaryBoundaryExample_consistency_iff _).2 sourceEquality)
  exact ⟨targetAssignment, htargetArgs, Fin.elim0, True.intro⟩

example (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .forward
      equalityFineBoundary aliasedBinaryBoundaryExample
      (orderedBoundaryRelation equalityFineBoundary
        aliasedBinaryBoundaryExample rfl)
      model named args args := by
  exact proofDependentBoundaryWitness_forward equalityFineBoundary
    aliasedBinaryBoundaryExample rfl model named args
      (equalityFineBoundary_entails_aliased model named args)

example (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier [])
    (args : Fin 2 → model.Carrier) :
    Diagram.ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      .backward
      aliasedBinaryBoundaryExample equalityFineBoundary
      (orderedBoundaryRelation aliasedBinaryBoundaryExample
        equalityFineBoundary rfl)
      model named args args := by
  exact proofDependentBoundaryWitness_backward aliasedBinaryBoundaryExample
    equalityFineBoundary rfl model named args
      (equalityFineBoundary_entails_aliased model named args)

end StrictAliasPartitionExamples

/-- The compiler-simulation direction induced by replay orientation. -/
def replaySimulationDirection : Orientation →
    Diagram.ConcreteElaboration.SimulationDirection
  | .forward => .forward
  | .backward => .backward

/-- The representative position chosen for an exposed pattern class carries
exactly that exposed wire. -/
theorem spliceExposedPosition_sound
    (layout : Diagram.Splice.Input.PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.pattern.val.boundary.get (layout.exposedPosition external) =
      input.pattern.val.exposedWires.get external := by
  let exposed := input.pattern.val.exposedWires.get external
  let boundary := input.pattern.val.boundary
  have hsome : (indexOf? boundary exposed).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact (OpenConcreteDiagram.mem_exposedWires _ _).1
      (List.get_mem _ _)
  have hlookup : indexOf? boundary exposed = some
      ((indexOf? boundary exposed).get hsome) := by
    obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
    exact hfound.trans (congrArg some
      (Option.get_of_eq_some hsome hfound).symm)
  have hsound := indexOf?_sound hlookup
  simpa only [Diagram.Splice.Input.PlugLayout.exposedPosition, exposed,
    boundary] using hsound

/-- The canonical intrinsic boundary substitution induced by a concrete
splice input. Its argument vector is positional, while its class map quotients
exactly the repeated boundary identities declared by the open pattern. -/
def splicePatternAttachmentAssignment
    (input : Diagram.Splice.Input signature) :
    BoundaryAssignment input.pattern.elaborate
      (Fin input.wireQuotient.count) where
  args position := input.quotientWire (input.attachment position)
  classes external := input.plugLayout.exposedAttachment external
  agrees := by
    intro position
    change input.quotientWire
        (input.attachment
          (input.plugLayout.exposedPosition
            (input.pattern.val.boundaryClass position))) =
      input.quotientWire (input.attachment position)
    apply input.equalBoundary_quotientWire_eq
    exact (spliceExposedPosition_sound input.plugLayout
      (input.pattern.val.boundaryClass position)).trans
        (input.pattern.val.boundaryClass_sound position)

/-- A compiled pattern body after canonical attachment substitution denotes
the original open pattern at exactly the positional host attachment values.
Repeated boundary positions are handled by `splicePatternAttachmentAssignment`, so
no injectivity premise is introduced. -/
theorem denote_pattern_substitution
    (input : Diagram.Splice.Input signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin input.wireQuotient.count → model.Carrier) :
    denoteRegion (relCtx := []) model named env PUnit.unit
        (input.pattern.elaborate.substituteBoundary
          (splicePatternAttachmentAssignment input)) ↔
      input.pattern.denote model named
        (env ∘ (splicePatternAttachmentAssignment input).args) := by
  exact input.pattern.elaborate.denote_substituteBoundary
    (splicePatternAttachmentAssignment input) model named env

/-- The registered forward side of a theorem payload inherits exactly the
schema implication.  Equality of checked open diagrams is recovered from the
serialized value equalities, so no second theorem-validity authority is
introduced. -/
theorem theoremPayload_forward_local
    (schema : TheoremSchema signature)
    (payload : TheoremPayload input selection hostArgs)
    (registered : theoremSidesMatch schema .forward payload)
    (named : NamedEnv Lambda.Individual signature)
    (valid : schema.Valid named)
    (args : Fin payload.source.val.boundary.length → Lambda.Individual) :
    payload.source.denote Lambda.canonicalModel named args →
      payload.target.denote Lambda.canonicalModel named
        (args ∘ Fin.cast payload.sameBoundaryArity.symm) := by
  rcases payload with ⟨source, target, payloadArity, occurrence⟩
  rcases schema with ⟨left, right, schemaArity⟩
  change source.val = left.val ∧ target.val = right.val at registered
  have hleft : left = source := Subtype.ext registered.1.symm
  have hright : right = target := Subtype.ext registered.2.symm
  subst left
  subst right
  simpa using valid args

/-- A registered reverse citation consumes the same schema implication in the
opposite local presentation: its target is the valid left side and its source
is the entailed right side.  Context polarity later supplies the operational
direction. -/
theorem theoremPayload_backward_local
    (schema : TheoremSchema signature)
    (payload : TheoremPayload input selection hostArgs)
    (registered : theoremSidesMatch schema .reverse payload)
    (named : NamedEnv Lambda.Individual signature)
    (valid : schema.Valid named)
    (args : Fin payload.target.val.boundary.length → Lambda.Individual) :
    payload.target.denote Lambda.canonicalModel named args →
      payload.source.denote Lambda.canonicalModel named
        (args ∘ Fin.cast payload.sameBoundaryArity) := by
  rcases payload with ⟨source, target, payloadArity, occurrence⟩
  rcases schema with ⟨left, right, schemaArity⟩
  change source.val = right.val ∧ target.val = left.val at registered
  have hleft : left = target := Subtype.ext registered.2.symm
  have hright : right = source := Subtype.ext registered.1.symm
  subst left
  subst right
  simpa using valid args

/-- A single local implication has exactly the four contextual directions
accepted by theorem citation.  The executable direction chooses which side is
present before replacement; replay orientation chooses which whole-diagram
implication must be proved.  `citationPolarity` is precisely the condition
that makes those choices agree with cut contravariance. -/
theorem contextualizeCitation
    (orientation : Orientation) (direction : Direction)
    (context : DiagramContext signature outerWires siteWires outerRels hostRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (siteWires + hostLocal) hostRels)
    (left right : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (siteWires + hostLocal))
    (relationMap : RelationRenaming patternRels hostRels)
    (polarity : citationPolarity orientation direction context.cutDepth)
    (localLaw : ∀ holeRelEnv patternEnv,
      denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) left →
        denoteRegion model named patternEnv
          (RelEnv.pullback relationMap holeRelEnv) right) :
    let before := match direction with
      | .forward => context.fill
          (Region.spliceAt hostLocal hostItems left wireMap relationMap)
      | .reverse => context.fill
          (Region.spliceAt hostLocal hostItems right wireMap relationMap)
    let after := match direction with
      | .forward => context.fill
          (Region.spliceAt hostLocal hostItems right wireMap relationMap)
      | .reverse => context.fill
          (Region.spliceAt hostLocal hostItems left wireMap relationMap)
    DirectedImplication orientation
      (denoteRegion model named env rels before)
      (denoteRegion model named env rels after) := by
  cases orientation <;> cases direction <;>
    simp only [citationPolarity, DirectedImplication] at polarity ⊢
  · exact context.fill_spliceAt_mono_even model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_odd model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_odd model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw
  · exact context.fill_spliceAt_mono_even model named env rels hostLocal
      hostItems left right wireMap relationMap polarity localLaw

end VisualProof.Rule
