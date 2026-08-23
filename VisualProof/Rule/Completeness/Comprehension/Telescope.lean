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

/-- A blank instantiation compiles through `Ends.spawn` and an arbitrary
actual-region continuation. The mandatory Ends phase remains visible as a
nonempty derivation in either polarity. -/
theorem blank
    {boundary holeWires : List Sig}
    {empty applied endpoint : Region holeWires}
    {source : OpenDiagram boundary}
    (polarity : Polarity)
    (spawn : Ends.Delete applied empty)
    (occurrence : Occurrence
      (polaritySource polarity empty endpoint) source)
    (emptyCanonical : (occurrence.context.fill empty).Canonical)
    (emptyExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill empty))
    (appliedCanonical : (occurrence.context.fill applied).Canonical)
    (appliedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill applied))
    (endpointCanonical : (occurrence.context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill endpoint))
    (continuation : Telescope polarity occurrence.interface occurrence.context
      applied endpoint appliedCanonical appliedExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded) :
    Relation.TransGen Step source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (polarityTarget polarity empty endpoint))
        (match polarity with
        | .positive => endpointCanonical
        | .negative => emptyCanonical)
        (match polarity with
        | .positive => endpointExternalTwoEnded
        | .negative => emptyExternalTwoEnded)) := by
  cases polarity with
  | positive =>
      have core :
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill empty) emptyCanonical
              emptyExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill applied) appliedCanonical
              appliedExternalTwoEnded) :=
        transGen_contextual Ends.Local
          (exactOccurrence occurrence.interface occurrence.context empty
            emptyCanonical emptyExternalTwoEnded)
          appliedCanonical appliedExternalTwoEnded continuation.1
          (.spawn spawn) Step.ends
      exact transGen_iso occurrence.host_iso.symm
        (core.reflTransGen continuation.2) (OpenDiagramIso.refl _)
  | negative =>
      have core :
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill applied) appliedCanonical
              appliedExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill empty) emptyCanonical
              emptyExternalTwoEnded) :=
        transGen_contextual Ends.Local
          (exactOccurrence occurrence.interface occurrence.context applied
            appliedCanonical appliedExternalTwoEnded)
          emptyCanonical emptyExternalTwoEnded continuation.1
          (.spawn spawn) Step.ends
      exact transGen_iso occurrence.host_iso.symm
        (continuation.2.transGen core) (OpenDiagramIso.refl _)

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

/-- The strict result of compiling a fully instantiated actual region through
all pending constructor binders to its exact endpoint. -/
def Compiles
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

/-- The established blank branch directly inhabits the strengthened derivation
goal, so every constructor shares `Compiles` without restating `blank`. -/
theorem Compiles.blank
    {boundary holeWires : List Sig}
    {empty applied endpoint : Region holeWires}
    {source : OpenDiagram boundary}
    (polarity : Polarity)
    (spawn : Ends.Delete applied empty)
    (occurrence : Occurrence
      (polaritySource polarity empty endpoint) source)
    (emptyCanonical : (occurrence.context.fill empty).Canonical)
    (emptyExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill empty))
    (appliedCanonical : (occurrence.context.fill applied).Canonical)
    (appliedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill applied))
    (endpointCanonical : (occurrence.context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill endpoint))
    (continuation : Telescope polarity occurrence.interface occurrence.context
      applied endpoint appliedCanonical appliedExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded) :
    Compiles polarity occurrence emptyCanonical emptyExternalTwoEnded
      endpointCanonical endpointExternalTwoEnded := by
  exact Telescope.blank polarity spawn occurrence emptyCanonical
    emptyExternalTwoEnded appliedCanonical appliedExternalTwoEnded
    endpointCanonical endpointExternalTwoEnded continuation

/-- A strict derivation at the exact occurrence can be fed directly to
the next constructor as an optional telescope phase. -/
theorem Compiles.toTelescope
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
    (compiled : Compiles polarity
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
  exact ⟨polarityEq, optional compiled⟩

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
  Compiles request.polarity request.occurrence
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
    request.endpointCanonical request.endpointExternalTwoEnded

/-- Extend an actual-region telescope by one mandatory contextual primitive.
The optional preparation and continuation stay exact; isomorphisms are used
only at the primitive's concrete endpoints, where `Contextual` can absorb
them without pretending that an isomorphism is a derivation step. -/
theorem compile
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
    Compiles polarity occurrence instantiatedCanonical
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
constructor's raw transform endpoint. Boundary and equality compilation own
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
theorem Request.Branch.compile
    {holeWires : List Sig}
    {instantiated pending prepared : Region holeWires}
    {request : Request instantiated pending}
    (branch : request.Branch prepared) : request.Result := by
  exact Telescope.compile branch.localRule branch.inject request.polarity
    request.occurrence request.instantiatedCanonical
    request.instantiatedExternalTwoEnded branch.preparedCanonical
    branch.preparedExternalTwoEnded request.pendingCanonical
    request.pendingExternalTwoEnded request.endpointCanonical
    request.endpointExternalTwoEnded branch.rawPreparedCanonical
    branch.rawPreparedExternalTwoEnded branch.rawPendingCanonical
    branch.rawPendingExternalTwoEnded branch.preparedIso branch.pendingIso
    branch.localStep branch.preparation request.continuation

/-- The blank constructor discharges a shared request through the established
blank theorem. -/
theorem Request.blank
    {holeWires : List Sig}
    {empty applied : Region holeWires}
    (request : Request empty applied)
    (spawn : Ends.Delete applied empty) : request.Result := by
  exact Compiles.blank request.polarity spawn request.occurrence
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
    request.pendingCanonical request.pendingExternalTwoEnded
    request.endpointCanonical request.endpointExternalTwoEnded
    request.continuation

/-- A constructor closes a shared request either with the established blank
phase or with one fully specified primitive branch. Both alternatives retain
the request's actual occurrence, polarity, validity, and final telescope. -/
inductive Request.Discharge
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Request instantiated pending)
    (staged : Region holeWires) : Type
  | blank
      (stagedIso : RegionIso (WireEquiv.refl holeWires)
        staged instantiated)
      (spawn : Ends.Delete pending instantiated) : request.Discharge staged
  | primitive {prepared : Region holeWires}
      (branch : request.Branch prepared)
      (stagedIso : RegionIso (WireEquiv.refl holeWires)
        staged branch.rawPrepared) : request.Discharge staged

/-- Every constructor discharge produces the strict shared result. -/
theorem Request.Discharge.compile
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    {request : Request instantiated pending}
    {staged : Region holeWires}
    (discharge : request.Discharge staged) : request.Result := by
  cases discharge with
  | blank _ spawn => exact request.blank spawn
  | primitive branch _ => exact branch.compile

end Telescope

open WirePrimitive

/-- An existing transform edit together with the exact staged region computed
by its authoritative `run`; no edit leaves the structural fold unaccounted. -/
structure ExactEdit
    {targetWires : List Sig}
    (Edit : Type)
    (run : Edit → Region targetWires) where
  edit : Edit
  endpoint : Region targetWires
  run_eq : run edit = endpoint

def ExactEdit.refl
    {targetWires : List Sig}
    {Edit : Type}
    {run : Edit → Region targetWires}
    (edit : Edit) : ExactEdit Edit run where
  edit := edit
  endpoint := run edit
  run_eq := rfl

theorem itemsEditNilRun
    {arguments common sourceWires targetWires : List Sig}
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : operation.Data frame}
    (edit : Transform.ItemsEdit operation frame data
      (.nil : ItemSeq sourceWires)) :
    edit.run = Region.blank targetWires := by
  cases edit
  rfl

/-! These witnesses live in `Type` only to make the demand for
`Operation.SiteData` explicit and to expose their genuine recursive shape to
Lean's termination checker. The authoritative `Instantiation` proof is the
index of every constructor; the witnesses carry no alternate source, result,
transform, or validity authority. In particular, no proposition is eliminated
to manufacture Type-valued site data. -/

mutual
  /-- Demand-driven selected-site evidence for one actual recursive region
result. It asks for site data only where the authoritative evidence contains a
selected application. -/
  inductive RegionSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : Region sourceWires} → {result : Region common} →
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
        pattern frame.sourceKeep frame.selected source result → Type
    | mk
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (common ++ locals)}
        {evidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern (frame.sourceKeep.appendRight locals)
            (frame.selected.appendLeft locals) items result}
        (sites : ItemsSites operation
          (operation.appendData frame data locals) evidence) :
        RegionSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            evidence)

  /-- Demand-driven selected-site evidence for an actual item sequence. -/
  inductive ItemsSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : ItemSeq sourceWires} → {result : Region common} →
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result → Type
    | nil
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (evidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern frame.sourceKeep frame.selected
            (.nil : ItemSeq sourceWires) (Region.blank common)) :
        ItemsSites operation data evidence
    | cons
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region common}
        {itemEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
            pattern frame.sourceKeep frame.selected item itemResult}
        {tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern frame.sourceKeep frame.selected tail tailResult}
        (itemSites : ItemSites operation data itemEvidence)
        (tailSites : ItemsSites operation data tailEvidence) :
        ItemsSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemEvidence tailEvidence)

  /-- Demand-driven selected-site evidence for one actual item. Nonselected
atoms and identities need no operation site data. -/
  inductive ItemSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : Item sourceWires} → {result : Region common} →
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        pattern frame.sourceKeep frame.selected source result → Type
    | atom
        {common sourceWires targetWires atomArguments : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports)
    | selectedAtom
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (ports : Vars common arguments)
        (siteData : operation.SiteData frame data ports) :
        ItemSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            ports)
    | identity
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports)
    | cut
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {body : Region sourceWires} {result : Region common}
        {evidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            pattern frame.sourceKeep frame.selected body result}
        (sites : RegionSites operation data evidence) :
        ItemSites operation data
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            evidence)
end

/-- Nil evidence never demands selected-site data, for any operation datum.
In particular this constructor accepts a uniform argument-projection datum
whose optional attachment is `none`. -/
def ItemsSites.ofNil
    {arguments common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    (data : operation.Data frame)
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected
        (.nil : ItemSeq sourceWires) (Region.blank common)) :
    ItemsSites operation data evidence := by
  exact .nil evidence

/-! `RegionResult`, `ItemsResult`, and `ItemResult` describe the simultaneous
layout of every selected site for one `Transform` primitive. Their recursive
shape therefore builds one exact edit; it does not introduce recursive
calculus steps or duplicate the surrounding telescope request. -/

mutual
  /-- Fold authoritative region evidence and its demand-driven sites into one
existing transform edit at its exact `run` endpoint. -/
  def regionEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Region sourceWires}
      {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      ExactEdit
        (Transform.RegionEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .mk childSites =>
        let childOutput := itemsEdit
          (operation.appendData frame data _) _ childSites
        {
          edit := .mk childOutput.edit
          endpoint := Region.adjoinAt _ .nil childOutput.endpoint
          run_eq := by
            simp only [Transform.RegionEdit.run]
            rw [childOutput.run_eq]
        }
  termination_by structural sites

  /-- Fold one authoritative item sequence into the same all-sites edit. -/
  def itemsEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : ItemSeq sourceWires}
      {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      ExactEdit
        (Transform.ItemsEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .nil _ => ExactEdit.refl .nil
    | .cons itemSites tailSites =>
        let itemOutput := itemEdit data _ itemSites
        let tailOutput := itemsEdit data _ tailSites
        {
          edit := .cons itemOutput.edit tailOutput.edit
          endpoint := itemOutput.endpoint.conjoin tailOutput.endpoint
          run_eq := by
            simp only [Transform.ItemsEdit.run]
            rw [itemOutput.run_eq, tailOutput.run_eq]
        }
  termination_by structural sites

  /-- Fold one authoritative item. Only its selected-atom branch consumes
operation-specific site data. -/
  def itemEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Item sourceWires}
      {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      ExactEdit
        (Transform.ItemEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .atom head ports => ExactEdit.refl (.atom head ports)
    | .selectedAtom ports siteData =>
        ExactEdit.refl (.selectedAtom ports siteData)
    | .identity signature arity ports =>
        ExactEdit.refl (.identity signature arity ports)
    | .cut childSites =>
        let childOutput := regionEdit data _ childSites
        {
          edit := .cut childOutput.edit
          endpoint := Region.singleton (.cut childOutput.endpoint)
          run_eq := by
            simp only [Transform.ItemEdit.run]
            rw [childOutput.run_eq]
        }
  termination_by structural sites
end

end VisualProof.Rule.Completeness.Comprehension
