import VisualProof.Rule.Completeness.Reachability

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

end Telescope

end VisualProof.Rule.Completeness.Comprehension
