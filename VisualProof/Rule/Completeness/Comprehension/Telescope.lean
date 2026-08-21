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

/-- The established blank branch directly inhabits the strengthened compiler
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

/-- A strict compiler result at the exact occurrence can be fed directly to
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

end Telescope

namespace Compiler

open WirePrimitive

/-- Constructor-specific data for every selected application site. This is
the only input needed to reuse the existing instantiation evidence as an
existing `Transform` edit; it introduces no parallel region or edit syntax. -/
abbrev SiteHandler
    (operation : Transform.Operation arguments) : Type :=
  ∀ {common sourceWires targetWires : List Sig}
    (frame : Transform.Frame arguments common sourceWires targetWires),
    (data : operation.Data frame) → (ports : Vars common arguments) →
      operation.SiteData frame data ports

mutual
  /-- Reuse recursive region-instantiation evidence as a transform edit for a
constructor whose selected sites are supplied by `site`. -/
  theorem regionTransform
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      (site : SiteHandler operation)
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Region sourceWires} {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
        pattern frame.sourceKeep
        frame.selected source result) :
      Nonempty (Transform.RegionEdit operation frame data source) := by
    cases evidence with
    | mk itemsResult =>
        obtain ⟨edit⟩ := itemsTransform site
          (operation.appendData frame data _) itemsResult
        exact ⟨Transform.RegionEdit.mk edit⟩

  /-- Reuse item-sequence instantiation evidence as the corresponding
constructor transform edit. -/
  theorem itemsTransform
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      (site : SiteHandler operation)
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep
        frame.selected source result) :
      Nonempty (Transform.ItemsEdit operation frame data source) := by
    cases evidence with
    | nil => exact ⟨Transform.ItemsEdit.nil⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemEdit⟩ := itemTransform site data itemEvidence
        obtain ⟨tailEdit⟩ := itemsTransform site data tailEvidence
        exact ⟨Transform.ItemsEdit.cons itemEdit tailEdit⟩

  /-- Reuse one item-instantiation witness as the corresponding constructor
transform edit. -/
  theorem itemTransform
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      (site : SiteHandler operation)
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Item sourceWires} {result : Region common}
      (evidence : _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        pattern frame.sourceKeep
        frame.selected source result) :
      Nonempty (Transform.ItemEdit operation frame data source) := by
    cases evidence with
    | atom head ports => exact ⟨Transform.ItemEdit.atom head ports⟩
    | selectedAtom ports =>
        exact ⟨Transform.ItemEdit.selectedAtom ports (site frame data ports)⟩
    | identity signature arity ports =>
        exact ⟨Transform.ItemEdit.identity signature arity ports⟩
    | cut bodyEvidence =>
        obtain ⟨bodyEdit⟩ := regionTransform site data bodyEvidence
        exact ⟨Transform.ItemEdit.cut bodyEdit⟩
end

end Compiler

end VisualProof.Rule.Completeness.Comprehension
