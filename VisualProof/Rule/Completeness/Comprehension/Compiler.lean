import VisualProof.Rule.Completeness.Comprehension.Telescope

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Compiler

/-- Compile one complete selected-application layer through formal
application. Boundary and equality compilation prepare the authoritative
instantiation endpoint to the exact all-sites transform endpoint; this theorem
owns the mandatory primitive at the comprehension binder's home occurrence. -/
theorem itemsFormal
    {outer localBefore localAfter before after : List Sig}
    {pattern : OpenDiagram
      (before ++ .rel (before ++ after) :: after)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (before ++ .rel (before ++ after) :: after) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).sourceKeep
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).selected
        source result)
    (sites : ItemsSites (Leaf.Formal.operation before after) PUnit.unit
      evidence)
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil result)
      (.mk
        (localBefore ++
          .rel (before ++ .rel (before ++ after) :: after) :: localAfter)
        source))
    (prepare : ∀ output : ExactEdit
      (Transform.ItemsEdit (Leaf.Formal.operation before after)
        (Leaf.Formal.rootFrame outer localBefore localAfter before after)
        PUnit.unit source)
      (fun edit => edit.run),
      request.Preparation
        (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
          output.endpoint)) :
    request.Result := by
  exact items (operation := Leaf.Formal.operation before after)
    (frame := Leaf.Formal.rootFrame outer localBefore localAfter before after)
    PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Formal.Applies.Description outer := {
            before := before
            after := after
            localBefore := localBefore
            localAfter := localAfter
            items := source
            itemsEdit := edit
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          let supplied := prepare {
            edit := edit
            endpoint := staged
            run_eq := runEq
          }
          let preparation : request.Preparation description.target :=
            stagedEq ▸ supplied
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source : Region outer) = description.source := by
            rfl
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source)
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch preparation.prepared := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Formal.Local
            inject := fun step => Step.formalApplication step
            preparedCanonical := preparation.preparedCanonical
            preparedExternalTwoEnded :=
              preparation.preparedExternalTwoEnded
            rawPreparedCanonical := preparation.rawPreparedCanonical
            rawPreparedExternalTwoEnded :=
              preparation.rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparation.preparedIso
            pendingIso := pendingIso
            localStep := .abstractFormal (.mk description)
            preparation := preparation.telescope
          }
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

/-- Compile one complete selected-application layer through identity leaf.
Boundary and equality compilation prepare the authoritative instantiation
endpoint to the exact all-sites transform endpoint; this theorem owns the
mandatory primitive at the comprehension binder's home occurrence. -/
theorem itemsIdentity
    {outer localBefore localAfter : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram (List.replicate arity signature)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).sourceKeep
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).selected
        source result)
    (sites : ItemsSites (Leaf.Identity.operation signature arity) PUnit.unit
      evidence)
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil result)
      (.mk
        (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
        source))
    (prepare : ∀ output : ExactEdit
      (Transform.ItemsEdit (Leaf.Identity.operation signature arity)
        (Leaf.Identity.rootFrame outer localBefore localAfter signature arity)
        PUnit.unit source)
      (fun edit => edit.run),
      request.Preparation
        (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
          output.endpoint)) :
    request.Result := by
  exact items (operation := Leaf.Identity.operation signature arity)
    (frame := Leaf.Identity.rootFrame outer localBefore localAfter signature
      arity)
    PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Identity.Leaves.Description outer := {
            signature := signature
            arity := arity
            localBefore := localBefore
            localAfter := localAfter
            items := source
            itemsEdit := edit
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          let supplied := prepare {
            edit := edit
            endpoint := staged
            run_eq := runEq
          }
          let preparation : request.Preparation description.target :=
            stagedEq ▸ supplied
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                source : Region outer) = description.source := by
            rfl
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                source)
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch preparation.prepared := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Identity.Local
            inject := fun step => Step.identityLeaf step
            preparedCanonical := preparation.preparedCanonical
            preparedExternalTwoEnded :=
              preparation.preparedExternalTwoEnded
            rawPreparedCanonical := preparation.rawPreparedCanonical
            rawPreparedExternalTwoEnded :=
              preparation.rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparation.preparedIso
            pendingIso := pendingIso
            localStep := .abstractIdentity (.mk description)
            preparation := preparation.telescope
          }
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

namespace PatternCompiler

/-- Exact singleton-atom decomposition at an existing pattern item. The
boundary/equality phases may choose the formal position only by proving that
the atom's argument list is precisely the remaining boundary. -/
structure FormalShape
    {patternWires atomArguments : List Sig}
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) where
  before : List Sig
  after : List Sig
  formal : Var patternWires (.rel (before ++ after))
  retained : Vars patternWires (before ++ after)
  head_eq : HEq head formal
  ports_eq : HEq ports retained
  boundaryWire : Vars patternWires
    (before ++ .rel (before ++ after) :: after)
  boundary_eq : boundaryWire =
    Argument.Projection.Vars.insertAt before formal retained
  boundarySurjective : ∀ wire : Fin patternWires.length,
    ∃ position : Fin
      (before ++ .rel (before ++ after) :: after).length,
      (boundaryWire.get position).index = wire
  canonical : (Region.singleton (.atom head ports)).Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire
    (Region.singleton (.atom head ports))

/-- The exact open singleton atom selected by a formal leaf decomposition. -/
def FormalShape.pattern
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    (shape : FormalShape head ports) :
    OpenDiagram
      (shape.before ++ .rel (shape.before ++ shape.after) :: shape.after) := {
  external := patternWires
  boundaryWire := shape.boundaryWire
  boundarySurjective := shape.boundarySurjective
  body := Region.singleton (.atom head ports)
  canonical := shape.canonical
  externalTwoEnded := shape.externalTwoEnded
}

/-- Caller-owned exact all-sites evidence for one singleton formal pattern.
The final primitive is intentionally absent: `compile` below fixes it to
`itemsFormal`. -/
structure FormalPhase
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    (shape : FormalShape head ports) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq
    (outer ++ (localBefore ++
      .rel (shape.before ++
        .rel (shape.before ++ shape.after) :: shape.after) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      shape.pattern
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after).sourceKeep
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after).selected
      source result
  sites : ItemsSites (Leaf.Formal.operation shape.before shape.after)
    PUnit.unit evidence
  request : Telescope.Request
    (Region.adjoinAt (localBefore ++ localAfter) .nil result)
    (.mk
      (localBefore ++
        .rel (shape.before ++
          .rel (shape.before ++ shape.after) :: shape.after) :: localAfter)
      source)
  prepare : ∀ output : ExactEdit
    (Transform.ItemsEdit (Leaf.Formal.operation shape.before shape.after)
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after)
      PUnit.unit source)
    (fun edit => edit.run),
    request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        output.endpoint)

/-- The singleton-atom branch fixes the final phase to FormalApplication. -/
theorem FormalPhase.compile
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {shape : FormalShape head ports}
    (phase : FormalPhase shape) : phase.request.Result := by
  exact itemsFormal phase.evidence phase.sites phase.request phase.prepare

/-- Exact singleton-identity decomposition at an existing pattern item. -/
structure IdentityShape
    {patternWires : List Sig}
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var patternWires signature) where
  boundaryWire : Vars patternWires (List.replicate arity signature)
  boundary_eq : boundaryWire = Leaf.Identity.Vars.fromFn ports
  boundarySurjective : ∀ wire : Fin patternWires.length,
    ∃ position : Fin (List.replicate arity signature).length,
      (boundaryWire.get position).index = wire
  canonical :
    (Region.singleton (.identity signature arity ports)).Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire
    (Region.singleton (.identity signature arity ports))

/-- The exact open singleton identity selected by an identity leaf
decomposition. -/
def IdentityShape.pattern
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    (shape : IdentityShape signature arity ports) :
    OpenDiagram (List.replicate arity signature) := {
  external := patternWires
  boundaryWire := shape.boundaryWire
  boundarySurjective := shape.boundarySurjective
  body := Region.singleton (.identity signature arity ports)
  canonical := shape.canonical
  externalTwoEnded := shape.externalTwoEnded
}

/-- Caller-owned exact all-sites evidence for one singleton identity pattern.
The final primitive is intentionally absent: `compile` below fixes it to
`itemsIdentity`. -/
structure IdentityPhase
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    (shape : IdentityShape signature arity ports) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq
    (outer ++ (localBefore ++
      .rel (List.replicate arity signature) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      shape.pattern
      (Leaf.Identity.rootFrame outer localBefore localAfter signature
        arity).sourceKeep
      (Leaf.Identity.rootFrame outer localBefore localAfter signature
        arity).selected
      source result
  sites : ItemsSites (Leaf.Identity.operation signature arity)
    PUnit.unit evidence
  request : Telescope.Request
    (Region.adjoinAt (localBefore ++ localAfter) .nil result)
    (.mk
      (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
      source)
  prepare : ∀ output : ExactEdit
    (Transform.ItemsEdit (Leaf.Identity.operation signature arity)
      (Leaf.Identity.rootFrame outer localBefore localAfter signature arity)
      PUnit.unit source)
    (fun edit => edit.run),
    request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        output.endpoint)

/-- The singleton-identity branch fixes the final phase to IdentityLeaf. -/
theorem IdentityPhase.compile
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    {shape : IdentityShape signature arity ports}
    (phase : IdentityPhase shape) : phase.request.Result := by
  exact itemsIdentity phase.evidence phase.sites phase.request phase.prepare

/-- One exact strict compiler goal. Its public fields preserve the actual
region indices of the request, so a structural plan cannot exchange a child
result for one about different endpoints. -/
structure Goal where
  holeWires : List Sig
  instantiated : Region holeWires
  pending : Region holeWires
  request : Telescope.Request instantiated pending

/-- Package an existing exact request without changing any endpoint. -/
def Goal.ofRequest
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Telescope.Request instantiated pending) : Goal := {
  holeWires := holeWires
  instantiated := instantiated
  pending := pending
  request := request
}

/-- The strict result belonging to an exact packaged request. -/
def Goal.Result (goal : Goal) : Prop :=
  goal.request.Result

/-- The exact goal stored by the established blank phase. -/
def nilGoal {wires : List Sig} (phase : Compiler.NilPhase wires) : Goal :=
  .ofRequest phase.request

/-- The exact goal stored by a singleton formal phase. -/
def FormalPhase.goal
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {shape : FormalShape head ports}
    (phase : FormalPhase shape) : Goal :=
  .ofRequest phase.request

/-- The exact goal stored by a singleton identity phase. -/
def IdentityPhase.goal
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    {shape : IdentityShape signature arity ports}
    (phase : IdentityPhase shape) : Goal :=
  .ofRequest phase.request

/-- The exact goal for a constructor-preparation segment. Its pending and
final endpoints are definitionally the supplied prepared region and its
continuation is reflexive, so it contains no caller-selected derivation. -/
noncomputable def Goal.exact
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (polarityEq : context.polarity = polarity)
    (instantiated prepared : Region holeWires)
    (instantiatedCanonical : (context.fill instantiated).Canonical)
    (instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill instantiated))
    (preparedCanonical : (context.fill prepared).Canonical)
    (preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill prepared)) : Goal :=
  .ofRequest {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity instantiated prepared))
      (match polarity with
      | .positive => instantiatedCanonical
      | .negative => preparedCanonical)
      (match polarity with
      | .positive => instantiatedExternalTwoEnded
      | .negative => preparedExternalTwoEnded)
    endpoint := prepared
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity instantiated prepared)
      (match polarity with
      | .positive => instantiatedCanonical
      | .negative => preparedCanonical)
      (match polarity with
      | .positive => instantiatedExternalTwoEnded
      | .negative => preparedExternalTwoEnded)
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := preparedCanonical
    pendingExternalTwoEnded := preparedExternalTwoEnded
    endpointCanonical := preparedCanonical
    endpointExternalTwoEnded := preparedExternalTwoEnded
    continuation := Telescope.refl polarity interface context
      preparedCanonical preparedExternalTwoEnded polarityEq
  }

/-- Consume the strict result of an exact goal as its optional telescope
segment. -/
theorem Goal.exactResult
    {boundary holeWires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external holeWires}
    {polarityEq : context.polarity = polarity}
    {instantiated prepared : Region holeWires}
    {instantiatedCanonical : (context.fill instantiated).Canonical}
    {instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill instantiated)}
    {preparedCanonical : (context.fill prepared).Canonical}
    {preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill prepared)}
    (result : (Goal.exact polarity interface context polarityEq instantiated
      prepared instantiatedCanonical instantiatedExternalTwoEnded
      preparedCanonical preparedExternalTwoEnded).Result) :
    Telescope polarity interface context instantiated prepared
      instantiatedCanonical instantiatedExternalTwoEnded preparedCanonical
      preparedExternalTwoEnded := by
  exact Telescope.Compiles.toTelescope polarity interface context
    instantiatedCanonical instantiatedExternalTwoEnded preparedCanonical
    preparedExternalTwoEnded polarityEq result

/-- The exact child goal for the current request's preparation segment. -/
noncomputable abbrev Goal.preparation
    (target : Goal)
    (prepared : Region target.holeWires)
    (preparedCanonical :
      (target.request.occurrence.context.fill prepared).Canonical)
    (preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      target.request.occurrence.interface.boundaryWire
      (target.request.occurrence.context.fill prepared)) : Goal :=
  Goal.exact target.request.polarity target.request.occurrence.interface
    target.request.occurrence.context target.request.continuation.1
    target.instantiated prepared target.request.instantiatedCanonical
    target.request.instantiatedExternalTwoEnded preparedCanonical
    preparedExternalTwoEnded

/-- Consume the strict result of the current request's exact preparation
goal. -/
theorem Goal.preparationResult
    {target : Goal}
    {prepared : Region target.holeWires}
    {preparedCanonical :
      (target.request.occurrence.context.fill prepared).Canonical}
    {preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      target.request.occurrence.interface.boundaryWire
      (target.request.occurrence.context.fill prepared)}
    (result : (Goal.preparation target prepared preparedCanonical
      preparedExternalTwoEnded).Result) :
    Telescope target.request.polarity target.request.occurrence.interface
      target.request.occurrence.context target.instantiated prepared
      target.request.instantiatedCanonical
      target.request.instantiatedExternalTwoEnded preparedCanonical
      preparedExternalTwoEnded := by
  exact Goal.exactResult result

/-- Exact consecutive preparation segments compose in logical order for both
occurrence polarities. -/
private theorem telescopeTrans
    {boundary holeWires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external holeWires}
    {first middle last : Region holeWires}
    {firstCanonical : (context.fill first).Canonical}
    {firstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill first)}
    {middleCanonical : (context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill middle)}
    {lastCanonical : (context.fill last).Canonical}
    {lastExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill last)}
    (head : Telescope polarity interface context first middle
      firstCanonical firstExternalTwoEnded middleCanonical
      middleExternalTwoEnded)
    (tail : Telescope polarity interface context middle last
      middleCanonical middleExternalTwoEnded lastCanonical
      lastExternalTwoEnded) :
    Telescope polarity interface context first last firstCanonical
      firstExternalTwoEnded lastCanonical lastExternalTwoEnded := by
  cases polarity with
  | positive => exact ⟨head.1, head.2.trans tail.2⟩
  | negative => exact ⟨head.1, tail.2.trans head.2⟩

/-- Evidence for one primitive at a fixed local-rule family. It contains the
exact staged and raw endpoints, validity, presentation isomorphisms, and
preparation, but deliberately contains neither a `Step` injection nor a
compiled result. -/
structure PrimitivePhase (localRule : LocalRule) (goal : Goal) where
  staged : Region goal.holeWires
  rawPrepared : Region goal.holeWires
  rawPending : Region goal.holeWires
  preparation : goal.request.Preparation rawPrepared
  rawPendingCanonical :
    (goal.request.occurrence.context.fill rawPending).Canonical
  rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPending)
  pendingIso : RegionIso (WireEquiv.refl goal.holeWires)
    goal.pending rawPending
  localStep : localRule rawPrepared rawPending
  stagedIso : RegionIso (WireEquiv.refl goal.holeWires)
    staged rawPrepared

/-- Internal conversion of fixed-family phase evidence to the mandatory
primitive core. Public structural plans below never receive this injection. -/
private theorem compilePrimitive
    {localRule : LocalRule}
    {goal : Goal}
    (inject : ∀ {stepBoundary : List Sig}
      {stepSource stepTarget : OpenDiagram stepBoundary},
      Contextual localRule stepSource stepTarget →
        Step stepSource stepTarget)
    (phase : PrimitivePhase localRule goal) : goal.Result := by
  let branch : goal.request.Branch phase.preparation.prepared := {
    rawPrepared := phase.rawPrepared
    rawPending := phase.rawPending
    localRule := localRule
    inject := inject
    preparedCanonical := phase.preparation.preparedCanonical
    preparedExternalTwoEnded :=
      phase.preparation.preparedExternalTwoEnded
    rawPreparedCanonical := phase.preparation.rawPreparedCanonical
    rawPreparedExternalTwoEnded :=
      phase.preparation.rawPreparedExternalTwoEnded
    rawPendingCanonical := phase.rawPendingCanonical
    rawPendingExternalTwoEnded := phase.rawPendingExternalTwoEnded
    preparedIso := phase.preparation.preparedIso
    pendingIso := phase.pendingIso
    localStep := phase.localStep
    preparation := phase.preparation.telescope
  }
  exact (Telescope.Request.Discharge.primitive branch phase.stagedIso).compile

/-- Fixed CutShape local family. -/
abbrev CutLocal : LocalRule :=
  fun before after => symmetric Content.Cut.Local before after

/-- Fixed ParallelShape local family. -/
abbrev ParallelLocal : LocalRule :=
  fun before after => symmetric Content.Parallel.Local before after

/-- Fixed Arity local family. -/
abbrev ArityLocal : LocalRule :=
  fun before after => symmetric Arity.Local before after

/-- Fixed ArgumentPermutation local family. -/
abbrev PermutationLocal : LocalRule :=
  fun before after => symmetric ArgumentPermutation.Local before after

/-- Fixed ArgumentDuplicate local family. -/
abbrev DuplicateLocal : LocalRule :=
  fun before after => symmetric Argument.Duplicate.Local before after

/-- Fixed directed ArgumentProjection local family. -/
abbrev ProjectionLocal : LocalRule := Argument.Projection.Local

/-- Exact evidence for one CutShape phase. -/
abbrev CutPhase (goal : Goal) := PrimitivePhase CutLocal goal

/-- Exact evidence for one ParallelShape phase. -/
abbrev ParallelPhase (goal : Goal) := PrimitivePhase ParallelLocal goal

/-- Exact evidence for one Arity phase. -/
abbrev ArityPhase (goal : Goal) := PrimitivePhase ArityLocal goal

/-- Exact evidence for one ArgumentPermutation phase. -/
abbrev PermutationPhase (goal : Goal) := PrimitivePhase PermutationLocal goal

/-- Exact evidence for one ArgumentDuplicate phase. -/
abbrev DuplicatePhase (goal : Goal) := PrimitivePhase DuplicateLocal goal

/-- Exact evidence for one directed ArgumentProjection phase. -/
abbrev ProjectionPhase (goal : Goal) := PrimitivePhase ProjectionLocal goal

/-- Cut phases always inject the fixed CutShape primitive. -/
theorem CutPhase.compile (phase : CutPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.cutShape step) phase

/-- Parallel phases always inject the fixed ParallelShape primitive. -/
theorem ParallelPhase.compile (phase : ParallelPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.parallelShape step) phase

/-- Arity phases always inject the fixed Arity primitive. -/
theorem ArityPhase.compile (phase : ArityPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.arity step) phase

/-- Permutation phases always inject the fixed ArgumentPermutation
primitive. -/
theorem PermutationPhase.compile
    (phase : PermutationPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.argumentPermutation step) phase

/-- Duplication phases always inject the fixed ArgumentDuplicate primitive. -/
theorem DuplicatePhase.compile
    (phase : DuplicatePhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.argumentDuplicate step) phase

/-- Projection phases always inject the fixed directed ArgumentProjection
primitive. -/
theorem ProjectionPhase.compile
    (phase : ProjectionPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.argumentProjection step) phase

/-- The fixed endpoint data for one exact primitive. The preparation
telescope is deliberately absent; structural recursion must supply it from
the preceding child result. -/
private structure PrimitiveTarget (localRule : LocalRule) (goal : Goal) where
  rawPrepared : Region goal.holeWires
  rawPending : Region goal.holeWires
  rawPreparedCanonical :
    (goal.request.occurrence.context.fill rawPrepared).Canonical
  rawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPrepared)
  rawPendingCanonical :
    (goal.request.occurrence.context.fill rawPending).Canonical
  rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPending)
  pendingIso : RegionIso (WireEquiv.refl goal.holeWires)
    goal.pending rawPending
  localStep : localRule rawPrepared rawPending

/-- Install the child-produced telescope into an exact primitive target. -/
private noncomputable def PrimitiveTarget.phase
    {localRule : LocalRule} {goal : Goal}
    (target : PrimitiveTarget localRule goal)
    (telescope : Telescope goal.request.polarity
      goal.request.occurrence.interface goal.request.occurrence.context
      goal.instantiated target.rawPrepared
      goal.request.instantiatedCanonical
      goal.request.instantiatedExternalTwoEnded target.rawPreparedCanonical
      target.rawPreparedExternalTwoEnded) : PrimitivePhase localRule goal := {
  staged := target.rawPrepared
  rawPrepared := target.rawPrepared
  rawPending := target.rawPending
  preparation := {
    prepared := target.rawPrepared
    preparedCanonical := target.rawPreparedCanonical
    preparedExternalTwoEnded := target.rawPreparedExternalTwoEnded
    rawPreparedCanonical := target.rawPreparedCanonical
    rawPreparedExternalTwoEnded := target.rawPreparedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := telescope
  }
  rawPendingCanonical := target.rawPendingCanonical
  rawPendingExternalTwoEnded := target.rawPendingExternalTwoEnded
  pendingIso := target.pendingIso
  localStep := target.localStep
  stagedIso := RegionIso.refl _
}

/-- Exact CutShape annotation at an existing cut constructor. The relational
description fixes both raw endpoints; the remaining fields prove validity and
the actual pending presentation. -/
structure CutTarget (target : Goal) where
  description : Content.Cut.Wrap.Description target.holeWires
  preparedCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.source

/-- A cut plan's child goal is definitionally the exact segment from the
parent's instantiated endpoint to the CutShape target. -/
inductive CutPlan : Goal → Goal → Type
  | mk {target : Goal} (cut : CutTarget target) :
      CutPlan
        (Goal.preparation target cut.description.target
          cut.preparedCanonical cut.preparedExternalTwoEnded)
        target

/-- Consume the exact child telescope and close the parent only through the
backward CutShape primitive. -/
theorem CutPlan.compile
    (plan : CutPlan source target)
    (result : source.Result) : target.Result := by
  cases plan with
  | mk cut =>
      let primitive : PrimitiveTarget CutLocal target := {
        rawPrepared := cut.description.target
        rawPending := cut.description.source
        rawPreparedCanonical := cut.preparedCanonical
        rawPreparedExternalTwoEnded := cut.preparedExternalTwoEnded
        rawPendingCanonical := cut.pendingCanonical
        rawPendingExternalTwoEnded := cut.pendingExternalTwoEnded
        pendingIso := cut.pendingIso
        localStep := Or.inr (.wrap (.mk cut.description))
      }
      exact CutPhase.compile
        (primitive.phase (Goal.preparationResult result))

/-- Exact ParallelShape annotation for one existing item-sequence
conjunction. `afterHead` is the actual endpoint shared definitionally by the
two consecutive child goals. -/
structure ParallelTarget (target : Goal) where
  description : Content.Parallel.Split.Description target.holeWires
  afterHead : Region target.holeWires
  afterHeadCanonical :
    (target.request.occurrence.context.fill afterHead).Canonical
  afterHeadExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill afterHead)
  preparedCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.source

/-- A parallel plan fixes the head and tail to consecutive exact segments;
neither child may select a different start, middle, or final prepared
endpoint. -/
inductive ParallelPlan : Goal → Goal → Goal → Type
  | mk {target : Goal} (parallel : ParallelTarget target) :
      ParallelPlan
        (Goal.exact target.request.polarity
          target.request.occurrence.interface
          target.request.occurrence.context target.request.continuation.1
          target.instantiated parallel.afterHead
          target.request.instantiatedCanonical
          target.request.instantiatedExternalTwoEnded
          parallel.afterHeadCanonical parallel.afterHeadExternalTwoEnded)
        (Goal.exact target.request.polarity
          target.request.occurrence.interface
          target.request.occurrence.context target.request.continuation.1
          parallel.afterHead parallel.description.target
          parallel.afterHeadCanonical parallel.afterHeadExternalTwoEnded
          parallel.preparedCanonical parallel.preparedExternalTwoEnded)
        target

/-- Compose both actual child telescope results and close only through the
backward ParallelShape primitive. -/
theorem ParallelPlan.compile
    (plan : ParallelPlan head tail target)
    (headResult : head.Result)
    (tailResult : tail.Result) : target.Result := by
  cases plan with
  | mk parallel =>
      let preparation := telescopeTrans
        (Goal.exactResult headResult) (Goal.exactResult tailResult)
      let primitive : PrimitiveTarget ParallelLocal target := {
        rawPrepared := parallel.description.target
        rawPending := parallel.description.source
        rawPreparedCanonical := parallel.preparedCanonical
        rawPreparedExternalTwoEnded := parallel.preparedExternalTwoEnded
        rawPendingCanonical := parallel.pendingCanonical
        rawPendingExternalTwoEnded := parallel.pendingExternalTwoEnded
        pendingIso := parallel.pendingIso
        localStep := Or.inr (.split (.mk parallel.description))
      }
      exact ParallelPhase.compile (primitive.phase preparation)

/-- Exact Arity annotation for one pattern-local wire. Its relational
description uses `Arity.operation`, whose selected-site output contains the
fresh local argument and its unary identity pin and whose selected-pin branch
is supplied by the current target relation. -/
structure ArityTarget (target : Goal) where
  description : Arity.Shift.Description target.holeWires
  preparedCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.source

/-- Each Arity step consumes exactly the preparation goal ending at its
`Shift.Description.target`. -/
inductive ArityStep : Goal → Goal → Type
  | mk {target : Goal} (arity : ArityTarget target) :
      ArityStep
        (Goal.preparation target arity.description.target
          arity.preparedCanonical arity.preparedExternalTwoEnded)
        target

/-- Consume one exact child segment and close only through backward Arity. -/
theorem ArityStep.compile
    (step : ArityStep source target)
    (result : source.Result) : target.Result := by
  cases step with
  | mk arity =>
      let primitive : PrimitiveTarget ArityLocal target := {
        rawPrepared := arity.description.target
        rawPending := arity.description.source
        rawPreparedCanonical := arity.preparedCanonical
        rawPreparedExternalTwoEnded := arity.preparedExternalTwoEnded
        rawPendingCanonical := arity.pendingCanonical
        rawPendingExternalTwoEnded := arity.pendingExternalTwoEnded
        pendingIso := arity.pendingIso
        localStep := Or.inr (.shift (.mk arity.description))
      }
      exact ArityPhase.compile
        (primitive.phase (Goal.preparationResult result))

/-- A finite zero-or-more chain of fixed Arity phases between exact goals. -/
inductive ArityPlan : Goal → Goal → Type
  | nil (goal : Goal) : ArityPlan goal goal
  | cons {source middle target : Goal}
      (head : ArityStep source middle)
      (tail : ArityPlan middle target) : ArityPlan source target

/-- Interpret every Arity phase in sequence; the zero case preserves the
same exact request index. -/
def ArityPlan.compile
    (plan : ArityPlan source target)
    (result : source.Result) : target.Result :=
  match plan with
  | .nil _ => result
  | .cons head tail =>
      tail.compile (head.compile result)

/-- Exact boundary-reordering annotation. -/
structure PermutationTarget (target : Goal) where
  description : ArgumentPermutation.Permutes.Description target.holeWires
  preparedCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.source

/-- Boundary reordering consumes the exact segment ending at the permuted
relation presentation. -/
inductive PermutationStep : Goal → Goal → Type 1
  | mk {target : Goal} (permutation : PermutationTarget target) :
      PermutationStep
        (Goal.preparation target permutation.description.target
          permutation.preparedCanonical
          permutation.preparedExternalTwoEnded)
        target

/-- Consume one exact segment and close only through backward
ArgumentPermutation. -/
theorem PermutationStep.compile
    (step : PermutationStep source target)
    (result : source.Result) : target.Result := by
  cases step with
  | mk permutation =>
      let primitive : PrimitiveTarget PermutationLocal target := {
        rawPrepared := permutation.description.target
        rawPending := permutation.description.source
        rawPreparedCanonical := permutation.preparedCanonical
        rawPreparedExternalTwoEnded :=
          permutation.preparedExternalTwoEnded
        rawPendingCanonical := permutation.pendingCanonical
        rawPendingExternalTwoEnded := permutation.pendingExternalTwoEnded
        pendingIso := permutation.pendingIso
        localStep := Or.inr (.permute (.mk permutation.description))
      }
      exact PermutationPhase.compile
        (primitive.phase (Goal.preparationResult result))

/-- Exact boundary-repetition annotation. -/
structure DuplicateTarget (target : Goal) where
  description : Argument.Duplicate.Duplicates.Description target.holeWires
  preparedCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.source

/-- Boundary repetition consumes the exact segment ending at the duplicated
relation presentation. -/
inductive DuplicateStep : Goal → Goal → Type
  | mk {target : Goal} (duplicate : DuplicateTarget target) :
      DuplicateStep
        (Goal.preparation target duplicate.description.target
          duplicate.preparedCanonical duplicate.preparedExternalTwoEnded)
        target

/-- Consume one exact segment and close only through backward
ArgumentDuplicate. -/
theorem DuplicateStep.compile
    (step : DuplicateStep source target)
    (result : source.Result) : target.Result := by
  cases step with
  | mk duplicate =>
      let primitive : PrimitiveTarget DuplicateLocal target := {
        rawPrepared := duplicate.description.target
        rawPending := duplicate.description.source
        rawPreparedCanonical := duplicate.preparedCanonical
        rawPreparedExternalTwoEnded := duplicate.preparedExternalTwoEnded
        rawPendingCanonical := duplicate.pendingCanonical
        rawPendingExternalTwoEnded := duplicate.pendingExternalTwoEnded
        pendingIso := duplicate.pendingIso
        localStep := Or.inr (.duplicate (.mk duplicate.description))
      }
      exact DuplicatePhase.compile
        (primitive.phase (Goal.preparationResult result))

/-- Exact boundary-omission annotation. The directed local description fixes
whether the current phase is an extension, uniform drop, or uniform
extension; no symmetric projection direction is invented by the compiler. -/
structure ProjectionTarget (target : Goal) where
  description : Argument.Projection.Local.Description target.holeWires
  preparedCanonical :
    (target.request.occurrence.context.fill description.source).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.source)
  pendingCanonical :
    (target.request.occurrence.context.fill description.target).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill description.target)
  pendingIso : RegionIso (WireEquiv.refl target.holeWires)
    target.pending description.target

/-- Boundary omission consumes the exact segment ending at the directed
projection source. -/
inductive ProjectionStep : Goal → Goal → Type
  | mk {target : Goal} (projection : ProjectionTarget target) :
      ProjectionStep
        (Goal.preparation target projection.description.source
          projection.preparedCanonical projection.preparedExternalTwoEnded)
        target

/-- Consume one exact segment and close only through directed
ArgumentProjection. -/
theorem ProjectionStep.compile
    (step : ProjectionStep source target)
    (result : source.Result) : target.Result := by
  cases step with
  | mk projection =>
      let primitive : PrimitiveTarget ProjectionLocal target := {
        rawPrepared := projection.description.source
        rawPending := projection.description.target
        rawPreparedCanonical := projection.preparedCanonical
        rawPreparedExternalTwoEnded := projection.preparedExternalTwoEnded
        rawPendingCanonical := projection.pendingCanonical
        rawPendingExternalTwoEnded := projection.pendingExternalTwoEnded
        pendingIso := projection.pendingIso
        localStep := .mk projection.description
      }
      exact ProjectionPhase.compile
        (primitive.phase (Goal.preparationResult result))

/-- A finite exact boundary-normalization chain. Every constructor names one
of the three required primitive families and shares its intermediate `Goal`
index definitionally with the next phase. -/
inductive BoundaryPlan : Goal → Goal → Type 1
  | nil (goal : Goal) : BoundaryPlan goal goal
  | permutation {source middle target : Goal}
      (head : PermutationStep source middle)
      (tail : BoundaryPlan middle target) : BoundaryPlan source target
  | duplicate {source middle target : Goal}
      (head : DuplicateStep source middle)
      (tail : BoundaryPlan middle target) : BoundaryPlan source target
  | projection {source middle target : Goal}
      (head : ProjectionStep source middle)
      (tail : BoundaryPlan middle target) : BoundaryPlan source target

/-- Interpret every exact boundary phase in order. -/
theorem BoundaryPlan.compile
    (plan : BoundaryPlan source target)
    (result : source.Result) : target.Result := by
  induction plan with
  | nil _ => exact result
  | permutation head _ induction =>
      exact induction (head.compile result)
  | duplicate head _ induction =>
      exact induction (head.compile result)
  | projection head _ induction =>
      exact induction (head.compile result)

mutual
  /-- Type-valued compiler evidence indexed by an existing region. -/
  inductive RegionPlan :
      {wires : List Sig} → Region wires → Goal → Type 1
    | mk
        {outer locals : List Sig}
        {items : ItemSeq (outer ++ locals)}
        {itemsGoal arityGoal target : Goal}
        (itemsPlan : ItemsPlan items itemsGoal)
        (arityPlan : ArityPlan itemsGoal arityGoal)
        (boundaryPlan : BoundaryPlan arityGoal target) :
        RegionPlan (.mk locals items) target

  /-- Type-valued compiler evidence indexed by an existing item sequence. -/
  inductive ItemsPlan :
      {wires : List Sig} → ItemSeq wires → Goal → Type 1
    | nil {wires : List Sig} (phase : Compiler.NilPhase wires) :
        ItemsPlan (.nil : ItemSeq wires) (nilGoal phase)
    | cons
        {wires : List Sig}
        {head : Item wires} {tail : ItemSeq wires}
        {headGoal tailGoal target : Goal}
        (headPlan : ItemPlan head headGoal)
        (tailPlan : ItemsPlan tail tailGoal)
        (parallel : ParallelPlan headGoal tailGoal target) :
        ItemsPlan (.cons head tail) target

  /-- Type-valued compiler evidence indexed by an existing item. Leaf
  constructors carry only their exact production phases. -/
  inductive ItemPlan : {wires : List Sig} → Item wires → Goal → Type 1
    | atom
        {patternWires atomArguments : List Sig}
        {head : Var patternWires (.rel atomArguments)}
        {ports : Vars patternWires atomArguments}
        (shape : FormalShape head ports)
        (phase : FormalPhase shape) :
        ItemPlan (.atom head ports) phase.goal
    | identity
        {patternWires : List Sig}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var patternWires signature}
        (shape : IdentityShape signature arity ports)
        (phase : IdentityPhase shape) :
        ItemPlan (.identity signature arity ports) phase.goal
    | cut
        {wires : List Sig} {body : Region wires}
        {childGoal target : Goal}
        (child : RegionPlan body childGoal)
        (cutPlan : CutPlan childGoal target) :
        ItemPlan (.cut body) target
end

mutual
  /-- Interpret an exact region plan. Structural callbacks produce evidence;
  this fold alone converts every phase into a compiler result. -/
  def regionResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : RegionPlan body goal) : goal.Result :=
    match plan with
    | .mk itemsPlan arityPlan boundaryPlan =>
        boundaryPlan.compile
          (arityPlan.compile (itemsResult itemsPlan))
  termination_by structural plan

  /-- Interpret an exact item-sequence plan. Nil is fixed to Ends and cons is
  fixed to ParallelShape. -/
  def itemsResult
      {wires : List Sig} {bodyItems : ItemSeq wires} {goal : Goal}
      (plan : ItemsPlan bodyItems goal) : goal.Result :=
    match plan with
    | .nil phase => phase.compile
    | .cons headPlan tailPlan parallel =>
        parallel.compile (itemResult headPlan) (itemsResult tailPlan)
  termination_by structural plan

  /-- Interpret an exact item plan. Every constructor fixes its primitive
  family and no annotation can supply a compiled result. -/
  def itemResult
      {wires : List Sig} {bodyItem : Item wires} {goal : Goal}
      (plan : ItemPlan bodyItem goal) : goal.Result :=
    match plan with
    | .atom _ phase => phase.compile
    | .identity _ phase => phase.compile
    | .cut child cutPlan =>
        cutPlan.compile (regionResult child)
  termination_by structural plan
end

/-- Production entry over one existing open pattern and its exact
syntax-indexed evidence plan. -/
theorem compile
    (pattern : OpenDiagram arguments)
    (plan : RegionPlan pattern.body goal) : goal.Result := by
  exact regionResult plan

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
