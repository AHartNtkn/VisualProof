import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw

namespace VisualProof
namespace Reconstruction

/-- Compose occurrence removal's retained-wire index with one splice
attachment's stable host-wire carrier. Accepted replacement owners retain the
particular attachment; this lower operation carries no checker authority. -/
def removalSpliceWireImage?
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment
      removed.complement removed.site replacement)
    (wire : host.val.WireId) : Option attachment.diagram.WireId :=
  if retained : wire ∈ Removal.wires occurrence then
    some (attachment.hostWire
      (Removal.wireIndex occurrence wire retained))
  else
    none

/-- A retained host wire maps through its exact dense removal index. -/
theorem removalSpliceWireImage_of_mem
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment
      removed.complement removed.site replacement)
    (wire : host.val.WireId)
    (retained : wire ∈ Removal.wires occurrence) :
    removalSpliceWireImage? occurrence removed attachment wire =
      some (attachment.hostWire
        (Removal.wireIndex occurrence wire retained)) := by
  unfold removalSpliceWireImage?
  rw [dif_pos retained]
  apply congrArg some
  apply Fin.ext
  rfl

/-- A wire removed with the occurrence has no replacement target identity. -/
theorem removalSpliceWireImage_eq_none_of_not_mem
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment
      removed.complement removed.site replacement)
    (wire : host.val.WireId)
    (removedWire : wire ∉ Removal.wires occurrence) :
    removalSpliceWireImage? occurrence removed attachment wire = none := by
  simp [removalSpliceWireImage?, removedWire]

/-- Removal indices and splice host images are both injective on survivors. -/
theorem removalSpliceWireImage_injective
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment
      removed.complement removed.site replacement)
    {left right : host.val.WireId}
    {mapped : attachment.diagram.WireId}
    (leftMapped :
      removalSpliceWireImage? occurrence removed attachment left = some mapped)
    (rightMapped :
      removalSpliceWireImage? occurrence removed attachment right = some mapped) :
    left = right := by
  unfold removalSpliceWireImage? at leftMapped rightMapped
  split at leftMapped
  next leftRetained =>
    split at rightMapped
    next rightRetained =>
      have hostImagesExact :
          attachment.hostWire
              (Removal.wireIndex occurrence left leftRetained) =
            attachment.hostWire
              (Removal.wireIndex occurrence right rightRetained) :=
        Option.some.inj (leftMapped.trans rightMapped.symm)
      have indicesExact := attachment.hostWire_injective hostImagesExact
      have originsExact :=
        congrArg (Removal.sourceWire occurrence) indicesExact
      exact
        (Removal.sourceWire_wireIndex occurrence left leftRetained).symm.trans
          (originsExact.trans
            (Removal.sourceWire_wireIndex occurrence right rightRetained))
    next _ => simp at rightMapped
  next _ => simp at leftMapped

/-- The removal-to-splice composition preserves every surviving signature. -/
theorem removalSpliceWireImage_signature
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment
      removed.complement removed.site replacement)
    {wire : host.val.WireId}
    {mapped : attachment.diagram.WireId}
    (mappedExact :
      removalSpliceWireImage? occurrence removed attachment wire = some mapped) :
    (attachment.diagram.wires mapped).sig = (host.val.wires wire).sig := by
  unfold removalSpliceWireImage? at mappedExact
  split at mappedExact
  next retained =>
    have targetExact :
        attachment.hostWire
            (Removal.wireIndex occurrence wire retained) = mapped :=
      Option.some.inj mappedExact
    subst mapped
    calc
      (attachment.diagram.wires
          (attachment.hostWire
            (Removal.wireIndex occurrence wire retained))).sig =
          (removed.complement.val.wires
            (Removal.wireIndex occurrence wire retained)).sig :=
        attachment.diagram_wire_hostWire _
      _ = (host.val.wires wire).sig := by
        simpa [RemovalResult.complement_generated] using
          (Removal.diagramWire_signature occurrence
            (Removal.wireIndex occurrence wire retained)).symm
  next _ => simp at mappedExact

end Reconstruction
end VisualProof
