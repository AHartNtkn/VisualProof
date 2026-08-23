import VisualProof.Rule.Completeness.Reachability
import VisualProof.Rule.Comprehension.Relation

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive.Content

/-- The source endpoint of a logically positive phase, oriented at the
occurrence's current polarity. -/
def polaritySource (polarity : Polarity) (before after : α) : α :=
  match polarity with
  | .positive => before
  | .negative => after

/-- The target endpoint of a logically positive phase, oriented at the
occurrence's current polarity. -/
def polarityTarget (polarity : Polarity) (before after : α) : α :=
  match polarity with
  | .positive => after
  | .negative => before

/-- An actual-region continuation from a pending constructor binder to its
fully instantiated endpoint. Constructor-specific layers extend this
continuation with concrete occurrence-indexed derivations. -/
def Telescope
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (pending endpoint : Region holeWires)
    (pendingCanonical : (context.fill pending).Canonical)
    (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill pending))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint)) : Prop :=
  Derives polarity
    (exactOccurrence interface context
      (polaritySource polarity pending endpoint)
      (match polarity with
      | .positive => pendingCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => pendingExternalTwoEnded
      | .negative => endpointExternalTwoEnded))
    (polarityTarget polarity pending endpoint)
    (match polarity with
    | .positive => endpointCanonical
    | .negative => pendingCanonical)
    (match polarity with
    | .positive => endpointExternalTwoEnded
    | .negative => pendingExternalTwoEnded)

namespace Telescope


/-- A zero-length actual-region telescope. The caller supplies the polarity
agreement because polarity belongs to the concrete occurrence context. -/
theorem refl
    {boundary holeWires : List Sig}
    {region : Region holeWires}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (regionCanonical : (context.fill region).Canonical)
    (regionExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill region))
    (polarityEq : context.polarity = polarity) :
    Telescope polarity interface context region region
      regionCanonical regionExternalTwoEnded
      regionCanonical regionExternalTwoEnded := by
  cases polarity <;> exact ⟨polarityEq, .refl⟩

/-- The strict result of deriving a fully instantiated actual region through
all pending constructor binders to its exact endpoint. -/
def StrictDerives
    {boundary holeWires : List Sig}
    {instantiated endpoint : Region holeWires}
    {source : OpenDiagram boundary}
    (polarity : Polarity)
    (occurrence : Occurrence
      (polaritySource polarity instantiated endpoint) source)
    (instantiatedCanonical :
      (occurrence.context.fill instantiated).Canonical)
    (instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill instantiated))
    (endpointCanonical : (occurrence.context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill endpoint)) : Prop :=
  Relation.TransGen Step source
    (occurrence.interface.withBody
      (occurrence.context.fill
        (polarityTarget polarity instantiated endpoint))
      (match polarity with
      | .positive => endpointCanonical
      | .negative => instantiatedCanonical)
      (match polarity with
      | .positive => endpointExternalTwoEnded
      | .negative => instantiatedExternalTwoEnded))


/-- A strict derivation at the exact occurrence can be fed directly to
the next constructor as an optional telescope phase. -/
theorem StrictDerives.toTelescope
    {boundary holeWires : List Sig}
    {instantiated endpoint : Region holeWires}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (instantiatedCanonical : (context.fill instantiated).Canonical)
    (instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill instantiated))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarityEq : context.polarity = polarity)
    (derived : StrictDerives polarity
      (exactOccurrence interface context
        (polaritySource polarity instantiated endpoint)
        (match polarity with
        | .positive => instantiatedCanonical
        | .negative => endpointCanonical)
        (match polarity with
        | .positive => instantiatedExternalTwoEnded
        | .negative => endpointExternalTwoEnded))
      instantiatedCanonical instantiatedExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded) :
    Telescope polarity interface context instantiated endpoint
      instantiatedCanonical instantiatedExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded := by
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail _ step induction => exact .tail induction step
  exact ⟨polarityEq, optional derived⟩

/-- The actual-region data shared by every recursive proof branch. The
instantiated endpoint is authoritative; constructor-local evidence supplies
only the next prepared endpoint and primitive. -/
structure Request
    {holeWires : List Sig}
    (instantiated pending : Region holeWires) where
  boundary : List Sig
  source : OpenDiagram boundary
  endpoint : Region holeWires
  polarity : Polarity
  occurrence : Occurrence
    (polaritySource polarity instantiated endpoint) source
  instantiatedCanonical : (occurrence.context.fill instantiated).Canonical
  instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire
    (occurrence.context.fill instantiated)
  pendingCanonical : (occurrence.context.fill pending).Canonical
  pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire (occurrence.context.fill pending)
  endpointCanonical : (occurrence.context.fill endpoint).Canonical
  endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire (occurrence.context.fill endpoint)
  continuation : Telescope polarity occurrence.interface occurrence.context
    pending endpoint pendingCanonical pendingExternalTwoEnded
    endpointCanonical endpointExternalTwoEnded

/-- The one strict goal shared by all recursive evidence branches. -/
def Request.Result
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Request instantiated pending) : Prop :=
  StrictDerives request.polarity request.occurrence
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
    request.endpointCanonical request.endpointExternalTwoEnded

/-- Extend an actual-region telescope by one mandatory contextual primitive.
The optional preparation and continuation stay exact; isomorphisms are used
only at the primitive's concrete endpoints, where `Contextual` can absorb
them without pretending that an isomorphism is a derivation step. -/
theorem primitive
    {boundary holeWires : List Sig}
    {instantiated prepared pending endpoint : Region holeWires}
    {rawPrepared rawPending : Region holeWires}
    {source : OpenDiagram boundary}
    (localRule : LocalRule)
    (inject : ∀ {stepBoundary : List Sig}
      {stepSource stepTarget : OpenDiagram stepBoundary},
      Contextual localRule stepSource stepTarget → Step stepSource stepTarget)
    (polarity : Polarity)
    (occurrence : Occurrence
      (polaritySource polarity instantiated endpoint) source)
    (instantiatedCanonical :
      (occurrence.context.fill instantiated).Canonical)
    (instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill instantiated))
    (preparedCanonical : (occurrence.context.fill prepared).Canonical)
    (preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill prepared))
    (pendingCanonical : (occurrence.context.fill pending).Canonical)
    (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill pending))
    (endpointCanonical : (occurrence.context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill endpoint))
    (rawPreparedCanonical :
      (occurrence.context.fill rawPrepared).Canonical)
    (rawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill rawPrepared))
    (rawPendingCanonical : (occurrence.context.fill rawPending).Canonical)
    (rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill rawPending))
    (preparedIso : RegionIso (WireEquiv.refl holeWires)
      prepared rawPrepared)
    (pendingIso : RegionIso (WireEquiv.refl holeWires)
      pending rawPending)
    (localStep : localRule rawPrepared rawPending)
    (preparation : Telescope polarity occurrence.interface occurrence.context
      instantiated prepared instantiatedCanonical
      instantiatedExternalTwoEnded preparedCanonical
      preparedExternalTwoEnded)
    (continuation : Telescope polarity occurrence.interface occurrence.context
      pending endpoint pendingCanonical pendingExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded) :
    StrictDerives polarity occurrence instantiatedCanonical
      instantiatedExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded := by
  cases polarity with
  | positive =>
      let rawPreparedOccurrence : Occurrence rawPrepared
          (occurrence.interface.withBody
            (occurrence.context.fill prepared) preparedCanonical
            preparedExternalTwoEnded) := {
        interface := occurrence.interface
        context := occurrence.context
        sourceCanonical := rawPreparedCanonical
        sourceExternalTwoEnded := rawPreparedExternalTwoEnded
        host_iso := OpenDiagram.withBody_iso preparedCanonical
          rawPreparedCanonical preparedExternalTwoEnded
          rawPreparedExternalTwoEnded
          (DiagramContext.fillIso occurrence.context preparedIso)
      }
      have rawPendingTargetIso : OpenDiagramIso
          (occurrence.interface.withBody
            (occurrence.context.fill pending) pendingCanonical
            pendingExternalTwoEnded)
          (rawPreparedOccurrence.interface.withBody
            (rawPreparedOccurrence.context.fill rawPending)
            rawPendingCanonical rawPendingExternalTwoEnded) := by
        exact OpenDiagram.withBody_iso pendingCanonical rawPendingCanonical
          pendingExternalTwoEnded rawPendingExternalTwoEnded
          (DiagramContext.fillIso occurrence.context pendingIso)
      have localCore : Relation.TransGen Step
          (occurrence.interface.withBody
            (occurrence.context.fill prepared) preparedCanonical
            preparedExternalTwoEnded)
          (occurrence.interface.withBody
            (occurrence.context.fill pending) pendingCanonical
            pendingExternalTwoEnded) := by
        apply Relation.TransGen.single
        apply inject
        refine ⟨holeWires, rawPrepared, rawPending,
          rawPreparedOccurrence, rawPendingCanonical,
          rawPendingExternalTwoEnded, rawPendingTargetIso, ?_⟩
        change atPolarity occurrence.context.polarity localRule
          rawPrepared rawPending
        have polarityEq : occurrence.context.polarity = .positive := by
          exact preparation.1
        rw [polarityEq]
        exact localStep
      have exactCore := preparation.2.transGen localCore
      exact transGen_iso occurrence.host_iso.symm
        (exactCore.reflTransGen continuation.2) (OpenDiagramIso.refl _)
  | negative =>
      let rawPendingOccurrence : Occurrence rawPending
          (occurrence.interface.withBody
            (occurrence.context.fill pending) pendingCanonical
            pendingExternalTwoEnded) := {
        interface := occurrence.interface
        context := occurrence.context
        sourceCanonical := rawPendingCanonical
        sourceExternalTwoEnded := rawPendingExternalTwoEnded
        host_iso := OpenDiagram.withBody_iso pendingCanonical
          rawPendingCanonical pendingExternalTwoEnded
          rawPendingExternalTwoEnded
          (DiagramContext.fillIso occurrence.context pendingIso)
      }
      have rawPreparedTargetIso : OpenDiagramIso
          (occurrence.interface.withBody
            (occurrence.context.fill prepared) preparedCanonical
            preparedExternalTwoEnded)
          (rawPendingOccurrence.interface.withBody
            (rawPendingOccurrence.context.fill rawPrepared)
            rawPreparedCanonical rawPreparedExternalTwoEnded) := by
        exact OpenDiagram.withBody_iso preparedCanonical rawPreparedCanonical
          preparedExternalTwoEnded rawPreparedExternalTwoEnded
          (DiagramContext.fillIso occurrence.context preparedIso)
      have localCore : Relation.TransGen Step
          (occurrence.interface.withBody
            (occurrence.context.fill pending) pendingCanonical
            pendingExternalTwoEnded)
          (occurrence.interface.withBody
            (occurrence.context.fill prepared) preparedCanonical
            preparedExternalTwoEnded) := by
        apply Relation.TransGen.single
        apply inject
        refine ⟨holeWires, rawPending, rawPrepared,
          rawPendingOccurrence, rawPreparedCanonical,
          rawPreparedExternalTwoEnded, rawPreparedTargetIso, ?_⟩
        change atPolarity occurrence.context.polarity localRule
          rawPending rawPrepared
        have polarityEq : occurrence.context.polarity = .negative := by
          exact continuation.1
        rw [polarityEq]
        exact localStep
      have exactCore := continuation.2.transGen localCore
      exact transGen_iso occurrence.host_iso.symm
        (exactCore.reflTransGen preparation.2) (OpenDiagramIso.refl _)

/-- Exact preparation from the authoritative instantiation endpoint to one
constructor's raw transform endpoint. Boundary and equality derivation own
this evidence; the constructor that consumes it still owns its primitive. -/
structure Request.Preparation
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Request instantiated pending)
    (rawPrepared : Region holeWires) where
  prepared : Region holeWires
  preparedCanonical :
    (request.occurrence.context.fill prepared).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    request.occurrence.interface.boundaryWire
    (request.occurrence.context.fill prepared)
  rawPreparedCanonical :
    (request.occurrence.context.fill rawPrepared).Canonical
  rawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    request.occurrence.interface.boundaryWire
    (request.occurrence.context.fill rawPrepared)
  preparedIso : RegionIso (WireEquiv.refl holeWires)
    prepared rawPrepared
  telescope : Telescope request.polarity request.occurrence.interface
    request.occurrence.context instantiated prepared
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
    preparedCanonical preparedExternalTwoEnded

/-- Transport only the raw primitive endpoint of a preparation across a
structural presentation isomorphism. The actual prepared endpoint and its
telescope remain authoritative. -/
noncomputable def Request.Preparation.rawIso
    {holeWires : List Sig}
    {instantiated pending rawFirst rawSecond : Region holeWires}
    {request : Request instantiated pending}
    (prepare : request.Preparation rawFirst)
    (iso : RegionIso (WireEquiv.refl holeWires) rawFirst rawSecond) :
    request.Preparation rawSecond := by
  let filledIso := DiagramContext.fillIso request.occurrence.context iso
  have rawSecondCanonical :
      (request.occurrence.context.fill rawSecond).Canonical :=
    filledIso.canonical_iff.mp prepare.rawPreparedCanonical
  have nonemptyIff : ∀ {signature}
      (wire : Var request.occurrence.interface.external signature),
      (request.occurrence.context.fill rawFirst).incidencePaths
          wire.index.val ≠ [] ↔
        (request.occurrence.context.fill rawSecond).incidencePaths
          wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := filledIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]
    · rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]
  let firstEndpoint := request.occurrence.interface.withBody
    (request.occurrence.context.fill rawFirst) prepare.rawPreparedCanonical
      prepare.rawPreparedExternalTwoEnded
  have rawSecondExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill rawSecond) :=
    firstEndpoint.externalTwoEnded_of_nonempty_iff
      (request.occurrence.context.fill rawSecond) nonemptyIff
  exact {
    prepared := prepare.prepared
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := rawSecondCanonical
    rawPreparedExternalTwoEnded := rawSecondExternalTwoEnded
    preparedIso := prepare.preparedIso.trans iso
    telescope := prepare.telescope
  }

/-- Constructor-local evidence for one prepared actual endpoint. This record
is the sole boundary at which a leaf or compound constructor supplies its
primitive, endpoint validity, and exact presentation isomorphisms. -/
structure Request.Branch
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Request instantiated pending)
    (prepared : Region holeWires) where
  rawPrepared : Region holeWires
  rawPending : Region holeWires
  localRule : LocalRule
  inject : ∀ {stepBoundary : List Sig}
    {stepSource stepTarget : OpenDiagram stepBoundary},
    Contextual localRule stepSource stepTarget → Step stepSource stepTarget
  preparedCanonical : (request.occurrence.context.fill prepared).Canonical
  preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    request.occurrence.interface.boundaryWire
    (request.occurrence.context.fill prepared)
  rawPreparedCanonical :
    (request.occurrence.context.fill rawPrepared).Canonical
  rawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    request.occurrence.interface.boundaryWire
    (request.occurrence.context.fill rawPrepared)
  rawPendingCanonical :
    (request.occurrence.context.fill rawPending).Canonical
  rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    request.occurrence.interface.boundaryWire
    (request.occurrence.context.fill rawPending)
  preparedIso : RegionIso (WireEquiv.refl holeWires)
    prepared rawPrepared
  pendingIso : RegionIso (WireEquiv.refl holeWires)
    pending rawPending
  localStep : localRule rawPrepared rawPending
  preparation : Telescope request.polarity request.occurrence.interface
    request.occurrence.context instantiated prepared
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
    preparedCanonical preparedExternalTwoEnded

/-- Discharge the shared strict goal from one constructor-local branch. -/
theorem Request.Branch.derive
    {holeWires : List Sig}
    {instantiated pending prepared : Region holeWires}
    {request : Request instantiated pending}
    (branch : request.Branch prepared) : request.Result := by
  exact Telescope.primitive branch.localRule branch.inject request.polarity
    request.occurrence request.instantiatedCanonical
    request.instantiatedExternalTwoEnded branch.preparedCanonical
    branch.preparedExternalTwoEnded request.pendingCanonical
    request.pendingExternalTwoEnded request.endpointCanonical
    request.endpointExternalTwoEnded branch.rawPreparedCanonical
    branch.rawPreparedExternalTwoEnded branch.rawPendingCanonical
    branch.rawPendingExternalTwoEnded branch.preparedIso branch.pendingIso
    branch.localStep branch.preparation request.continuation

end Telescope


end VisualProof.Rule.Completeness.Comprehension
