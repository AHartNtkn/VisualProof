import VisualProof.Rule.Soundness.Comprehension.AbstractionMaps

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace AbstractionRawTrace

/-- Survivor wire embedded into the proof-dependent raw result carrier. -/
def rawTargetWire
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount)
    (survives : trace.domains.wires.survives wire = true) :
    Fin raw.wireCount :=
  Fin.cast trace.raw_wireCount.symm (trace.targetWire wire survives)

theorem interface_image_survives
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount) (mapped : Fin raw.wireCount)
    (image : (comprehensionAbstractInterfaceTransport input wrap comprehension
      occurrences raw hraw).image? wire = some mapped) :
    trace.domains.wires.survives wire = true := by
  unfold comprehensionAbstractInterfaceTransport InterfaceTransport.survivors
    InterfaceTransport.rootFiltered at image
  dsimp only at image
  cases indexed : (abstractionDomains input occurrences).wires.index? wire with
  | none =>
      rw [indexed] at image
      simp only [Option.map_none, Option.bind_none] at image
      contradiction
  | some survivor =>
      change (abstractionDomains input occurrences).wires.survives wire = true
      exact ((abstractionDomains input occurrences).wires.index?_isSome_iff
        wire).1 (by
        simp [indexed])

theorem interface_image_eq_rawTargetWire
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin input.val.wireCount) (mapped : Fin raw.wireCount)
    (image : (comprehensionAbstractInterfaceTransport input wrap comprehension
      occurrences raw hraw).image? wire = some mapped) :
    mapped = trace.rawTargetWire wire
      (trace.interface_image_survives hraw wire mapped image) := by
  unfold comprehensionAbstractInterfaceTransport InterfaceTransport.survivors
    InterfaceTransport.rootFiltered at image
  dsimp only at image
  let survives := trace.interface_image_survives hraw wire mapped image
  have indexed := (abstractionDomains input occurrences).wires.index?_index
    wire survives
  rw [indexed] at image
  change (if (raw.wires
      (Fin.cast _ ((abstractionDomains input occurrences).wires.index wire
        survives))).scope = raw.root then
      some (Fin.cast _ ((abstractionDomains input occurrences).wires.index wire
        survives)) else none) = some mapped at image
  split at image <;> try contradiction
  simp only [Option.some.injEq] at image
  exact image.symm.trans (by
    apply Fin.ext
    rfl)

theorem transportedWire_survives
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (position : Fin boundary.length) :
    trace.domains.wires.survives (boundary.get position) = true := by
  let interface := comprehensionAbstractInterfaceTransport input wrap
    comprehension occurrences raw hraw
  have image := interface.transportBoundary_get transport position
  exact trace.interface_image_survives hraw _ _ image

theorem transportedWire_eq_rawTargetWire
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (position : Fin boundary.length) :
    mapped.get (Fin.cast
        ((comprehensionAbstractInterfaceTransport input wrap comprehension
          occurrences raw hraw).transportBoundary_length transport).symm
        position) =
      trace.rawTargetWire (boundary.get position)
        (trace.transportedWire_survives hraw boundary mapped transport
          position) := by
  let interface := comprehensionAbstractInterfaceTransport input wrap
    comprehension occurrences raw hraw
  have image := interface.transportBoundary_get transport position
  exact trace.interface_image_eq_rawTargetWire hraw _ _ image

end AbstractionRawTrace

end VisualProof.Rule
