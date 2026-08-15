import VisualProof.Diagram.PortPartition
import VisualProof.Diagram.Scope.Rename
import VisualProof.Diagram.Scope.Context
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Identification

namespace Repeated

/-- The intrinsically typed wire at one position of a homogeneous context. -/
def wire (signature : Sig) : {count : Nat} →
    Fin count → Var (List.replicate count signature) signature
  | 0, position => Fin.elim0 position
  | _ + 1, position =>
      Fin.cases .here (fun rest => .there (wire signature rest)) position

/-- Dependent elimination for a homogeneous typed wire context. -/
def elim (signature : Sig) : {count : Nat} →
    (motive : ∀ {wireSignature},
      Var (List.replicate count signature) wireSignature → Sort u) →
    (wireCase : ∀ position : Fin count,
      motive (wire signature position)) →
    ∀ {wireSignature}
      (selected : Var (List.replicate count signature) wireSignature),
      motive selected
  | 0, _, _, _, selected => nomatch selected
  | count + 1, _, wireCase, _, .here => wireCase 0
  | count + 1, motive, wireCase, _, .there selected =>
      elim signature
        (motive := fun selected => motive (.there selected))
        (wireCase := fun position => wireCase position.succ) selected

@[simp] theorem wire_index (signature : Sig) {count : Nat}
    (position : Fin count) :
    (wire signature position).index.val = position.val := by
  induction count with
  | zero => exact Fin.elim0 position
  | succ count induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      simpa only [wire, Fin.val_succ] using
        congrArg Nat.succ (induction rest)

/-- Collapse every wire of a homogeneous context to one survivor. -/
def collapse (survivor : Var target signature) : {count : Nat} →
    ∀ {wireSignature},
      Var (List.replicate count signature) wireSignature →
        Var target wireSignature
  | 0, _, repeated => nomatch repeated
  | _ + 1, _, .here => survivor
  | _ + 1, _, .there repeated => collapse survivor repeated

@[simp] theorem collapse_wire (survivor : Var target signature)
    {count : Nat} (position : Fin count) :
    collapse survivor (wire signature position) = survivor := by
  induction count with
  | zero => exact Fin.elim0 position
  | succ count induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

end Repeated

/-- Embed every retained wire while adjoining homogeneous fresh wires. -/
def retainWire (outer locals : List Sig) (signature : Sig) (count : Nat) :
    WireRenaming (outer ++ locals)
      (outer ++ (locals ++ List.replicate count signature)) :=
  Region.adjoinHostWire outer locals (List.replicate count signature)

/-- One fresh current-region wire in the expanded local context. -/
def freshLocalWire (outer locals : List Sig) (signature : Sig)
    {count : Nat} (position : Fin count) :
    Var (outer ++ (locals ++ List.replicate count signature)) signature :=
  Var.appendRight outer
    (Var.appendRight locals (Repeated.wire signature position))

/-- Collapse the appended current-region wires to the selected survivor. -/
def collapseLocal (outer locals : List Sig)
    (survivor : Var (outer ++ locals) signature) (count : Nat) :
    WireRenaming
      (outer ++ (locals ++ List.replicate count signature))
      (outer ++ locals) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft locals)
    (Var.appendMap
      (fun wire => Var.appendRight outer wire)
      (Repeated.collapse survivor))⟩

@[simp] theorem collapseLocal_retained
    (survivor : Var (outer ++ locals) signature) (count : Nat)
    (wire : Var (outer ++ locals) wireSignature) :
    collapseLocal outer locals survivor count
      (retainWire outer locals signature count wire) = wire := by
  apply Var.appendCases (left := outer) (right := locals)
    (motive := fun wire => collapseLocal outer locals survivor count
      (retainWire outer locals signature count wire) = wire)
  · intro inheritedSignature inherited
    simp [collapseLocal, retainWire, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [collapseLocal, retainWire, Region.adjoinHostWire,
      Region.conjoinLeftWire]

@[simp] theorem collapseLocal_fresh
    (survivor : Var (outer ++ locals) signature) {count : Nat}
    (position : Fin count) :
    collapseLocal outer locals survivor count
      (freshLocalWire outer locals signature position) = survivor := by
  simp [collapseLocal, freshLocalWire]

/-- Collapse appended external wires to one retained external survivor. -/
def collapseOpen (external : List Sig)
    (survivor : Var external signature) (count : Nat) :
    WireRenaming (external ++ List.replicate count signature) external :=
  ⟨Var.appendMap (fun wire => wire)
    (Repeated.collapse survivor)⟩

/-- Embed one retained external wire into the expanded external context. -/
def retainOpenWire (signature : Sig) (count : Nat) :
    WireRenaming external (external ++ List.replicate count signature) :=
  ⟨fun wire => wire.appendLeft (List.replicate count signature)⟩

/-- One fresh external wire in the expanded external context. -/
def freshOpenWire (external : List Sig) (signature : Sig)
    {count : Nat} (position : Fin count) :
    Var (external ++ List.replicate count signature) signature :=
  Var.appendRight external (Repeated.wire signature position)

@[simp] theorem collapseOpen_retained
    (survivor : Var external signature) (count : Nat)
    (wire : Var external wireSignature) :
    collapseOpen external survivor count
      (retainOpenWire signature count wire) = wire := by
  simp [collapseOpen, retainOpenWire]

@[simp] theorem collapseOpen_fresh
    (survivor : Var external signature) {count : Nat}
    (position : Fin count) :
    collapseOpen external survivor count
      (freshOpenWire external signature position) = survivor := by
  simp [collapseOpen, freshOpenWire]

inductive PortExpansion (count : Nat) : Nat → Nat → Type
  | nil : PortExpansion count 0 0
  | retain {retained exposed : Nat}
      (tail : PortExpansion count retained exposed) :
      PortExpansion count (retained + 1) (exposed + 1)
  | absorb {retained exposed : Nat} (wire : Fin count)
      (tail : PortExpansion count retained exposed) :
      PortExpansion count retained (exposed + 1)

namespace PortExpansion

/-- The exact source of every exposed selected-node port.  The inductive
shape consumes retained ports in order while absorbed ports may be
interleaved arbitrarily and repeated. -/
def select : PortExpansion count retained exposed →
    Fin exposed → Sum (Fin retained) (Fin count)
  | .nil, position => Fin.elim0 position
  | .retain tail, position =>
      Fin.cases (Sum.inl 0) (fun rest =>
        match tail.select rest with
        | .inl retainedPosition => .inl retainedPosition.succ
        | .inr absorbedWire => .inr absorbedWire) position
  | .absorb wire tail, position =>
      Fin.cases (Sum.inr wire) tail.select position

end PortExpansion

/-- Exact selected-node data.  `expansion` preserves every retained port
exactly once and in order, while allowing arbitrary absorbed-port
interleaving and multiplicity. -/
structure NodeData (base : List Sig) (signature : Sig) (count : Nat) where
  survivor : Var base signature
  retainedArity : Nat
  retainedPorts : Fin retainedArity → Var base signature
  survivorPort : ∃ position, retainedPorts position = survivor
  exposedArity : Nat
  expansion : PortExpansion count retainedArity exposedArity
  absorbedPort : ∀ wire : Fin count, ∃ position,
    expansion.select position = Sum.inr wire

namespace NodeData

def collapsedNode (data : NodeData base signature count) : Item base :=
  .identity signature data.retainedArity data.retainedPorts

def exposedPorts (data : NodeData base signature count)
    (retain : WireRenaming base expanded)
    (fresh : Fin count → Var expanded signature) :
    Fin data.exposedArity → Var expanded signature := fun position =>
  match data.expansion.select position with
  | .inl retainedPosition => retain (data.retainedPorts retainedPosition)
  | .inr absorbedWire => fresh absorbedWire

def exposedNode (data : NodeData base signature count)
    (retain : WireRenaming base expanded)
    (fresh : Fin count → Var expanded signature) : Item expanded :=
  .identity signature data.exposedArity
    (data.exposedPorts retain fresh)

end NodeData

namespace Local

/-- Exact local exposure data.  `awayPartition` is the existing typed port
partition over every incidence except the selected identity node. -/
structure Data (outer : List Sig) where
  locals : List Sig
  signature : Sig
  count : Nat
  countPositive : 0 < count
  node : NodeData (outer ++ locals) signature count
  away : ItemSeq (outer ++ locals)
  awayPartition : ItemSeq.PortPartition
    (collapseLocal outer locals node.survivor count) away

def Data.collapsedRegion (data : Data outer) : Region outer :=
  .mk data.locals
    (.cons data.node.collapsedNode data.away)

def Data.exposedAway (data : Data outer) :
    ItemSeq
      (outer ++ (data.locals ++ List.replicate data.count data.signature)) :=
  data.away.partitionOutput
    (collapseLocal outer data.locals data.node.survivor data.count)
    data.awayPartition

def Data.exposedRegion (data : Data outer) : Region outer :=
  .mk (data.locals ++ List.replicate data.count data.signature)
    (.cons
      (data.node.exposedNode
        (retainWire outer data.locals data.signature data.count)
        (freshLocalWire outer data.locals data.signature))
      data.exposedAway)

/-- Local applicability.  `absorbedNonIdentity` selects a non-identity port
in the away syntax whose active port-partition output is each fresh wire.
The selected identity and ports on every other identity node are excluded. -/
structure Applicability (data : Data outer) : Prop where
  absorbedNonIdentity : ∀ wire : Fin data.count,
    ∃ port : ItemSeq.Port data.away data.node.survivor,
      port.IsNonIdentity ∧
        (data.awayPartition.output data.node.survivor port).val =
          freshLocalWire outer data.locals data.signature wire
  retainedSupport : ∀ {wireSignature}
      (wire : Var outer wireSignature),
    data.collapsedRegion.incidencePaths wire.index.val ≠ [] ↔
      data.exposedRegion.incidencePaths wire.index.val ≠ []

theorem collapsedRegion_rename (data : Data outer) :
    data.exposedAway.renameWires
      (collapseLocal outer data.locals data.node.survivor data.count) =
        data.away := by
  exact ItemSeq.partitionOutput_renameWires _ _ _

theorem exposedValidity
    (data : Data outer)
    (applicability : Applicability data)
    (occurrence : Occurrence data.collapsedRegion source)
    (targetCanonical : data.exposedRegion.Canonical) :
    (occurrence.context.fill data.exposedRegion).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill data.exposedRegion) := by
  have replaced := occurrence.context.replaceCanonical
    data.collapsedRegion data.exposedRegion occurrence.sourceCanonical
    targetCanonical applicability.retainedSupport
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill data.collapsedRegion)
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  exact ⟨replaced.1,
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill data.exposedRegion) replaced.2⟩

theorem collapsedValidity
    (data : Data outer)
    (applicability : Applicability data)
    (occurrence : Occurrence data.exposedRegion source) :
    (targetCanonical : data.collapsedRegion.Canonical) →
    (occurrence.context.fill data.collapsedRegion).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill data.collapsedRegion) := by
  intro targetCanonical
  have replaced := occurrence.context.replaceCanonical
    data.exposedRegion data.collapsedRegion occurrence.sourceCanonical
    targetCanonical (fun wire => (applicability.retainedSupport wire).symm)
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill data.exposedRegion)
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  exact ⟨replaced.1,
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill data.collapsedRegion) replaced.2⟩

private def Data.mapInternalWire (data : Data outer) :
    ∀ {wireSignature},
      Region.InternalWire data.collapsedRegion wireSignature →
        Region.InternalWire data.exposedRegion wireSignature
  | _, .here wire =>
      .here (wire.appendLeft
        (List.replicate data.count data.signature))
  | _, .nested (.tail wire) =>
      .nested (.tail (wire.partitionOutput
        (collapseLocal outer data.locals data.node.survivor data.count)
        data.away data.awayPartition))

private theorem Data.ownerPath_mapInternalWire
    (data : Data outer)
    (wire : Region.InternalWire data.collapsedRegion wireSignature) :
    (data.mapInternalWire wire).ownerPath = wire.ownerPath := by
  cases wire with
  | here wire => rfl
  | nested nested =>
      cases nested with
      | tail wire =>
          exact ItemSeq.InternalWire.ownerPathFrom_partitionOutput
            (collapseLocal outer data.locals data.node.survivor data.count)
            data.away data.awayPartition wire 1

end Local

/-- Local identification is one exact exposure; symmetry supplies collapse. -/
inductive Local : LocalRule
  | expose (data : Local.Data outer)
      (applicability : Local.Applicability data) :
      Local data.collapsedRegion data.exposedRegion

namespace Local

/-- Every wire of an exact collapsed local presentation survives exposure
with the same derived scope path. -/
theorem existsPresentedWire_scopePath
    {before after : Region wires} (step : Local before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after))
    {wireSignature}
    (wire : OpenDiagram.Wire
      (occurrence.interface.withBody
        (occurrence.context.fill before) occurrence.sourceCanonical
          occurrence.sourceExternalTwoEnded) wireSignature) :
    ∃ targetWire : OpenDiagram.Wire
        (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical
            targetExternalTwoEnded) wireSignature,
      (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical
            targetExternalTwoEnded).scopePath targetWire =
        (occurrence.interface.withBody
          (occurrence.context.fill before) occurrence.sourceCanonical
            occurrence.sourceExternalTwoEnded).scopePath wire := by
  cases step with
  | expose data applicability =>
      cases wire with
      | external externalWire =>
          refine ⟨.external externalWire, ?_⟩
          rw [OpenDiagram.scopePath_external, OpenDiagram.scopePath_external]
      | internal internalWire =>
          let holeMap : ∀ {signature},
              Region.InternalWire data.collapsedRegion signature →
                Region.InternalWire data.exposedRegion signature :=
            data.mapInternalWire
          let targetWire := occurrence.context.mapInternalWire
            holeMap internalWire
          refine ⟨.internal targetWire, ?_⟩
          rw [OpenDiagram.scopePath_internal, OpenDiagram.scopePath_internal]
          exact occurrence.context.ownerPath_mapInternalWire holeMap
            (fun wire => data.ownerPath_mapInternalWire wire) internalWire

end Local

namespace Open

private def presentedBoundary (diagram : OpenDiagram boundary)
    (external : WireEquiv diagram.external represented) :
    Vars represented boundary :=
  diagram.boundaryWire.map (fun wire => external wire)

private theorem boundaryPartitionOutput_map
    (collapse : WireRenaming target source)
    (variables : Vars source signatures)
    (partition : ∀ argument : Fin signatures.length,
      { result : Var target (signatures.get argument) //
        collapse result = variables.get argument }) :
    (Vars.partitionOutput collapse variables partition).map
        (fun wire => collapse wire) = variables := by
  induction signatures with
  | nil => cases variables; rfl
  | cons signature rest induction =>
      cases variables with
      | cons head tail =>
          simp only [Vars.partitionOutput, Vars.map]
          have headProperty : collapse (partition 0).val = head := by
            simpa only [Vars.get] using (partition 0).property
          calc
            _ = Vars.cons head
                ((Vars.partitionOutput collapse tail fun argument =>
                  partition argument.succ).map fun wire => collapse wire) :=
              congrArg (fun wire => Vars.cons wire _) headProperty
            _ = Vars.cons head tail := congrArg (Vars.cons head)
              (induction tail (fun argument => partition argument.succ))

/-- Exact root exposure data, including the partition of ordered boundary
positions. -/
structure Data (boundary : List Sig) (external : List Sig) where
  signature : Sig
  count : Nat
  countPositive : 0 < count
  locals : List Sig
  survivor : Var external signature
  node : NodeData (external ++ locals) signature count
  nodeSurvivor : node.survivor = survivor.appendLeft locals
  away : ItemSeq (external ++ locals)
  awayPartition : ItemSeq.PortPartition
    ((collapseOpen external survivor count).appendRight locals) away
  collapsedBoundary : Vars external boundary
  collapsedBoundarySurjective : ∀ wire : Fin external.length,
    ∃ position : Fin boundary.length,
      (collapsedBoundary.get position).index = wire
  boundaryPartition : ∀ position : Fin boundary.length,
    { result : Var (external ++ List.replicate count signature)
        (boundary.get position) //
      collapseOpen external survivor count result =
        collapsedBoundary.get position }

def Data.collapsedRegion (data : Data boundary external) : Region external :=
  .mk data.locals
    (.cons data.node.collapsedNode data.away)

def Data.exposedAway (data : Data boundary external) :
    ItemSeq ((external ++ List.replicate data.count data.signature) ++
      data.locals) :=
  data.away.partitionOutput
    ((collapseOpen external data.survivor data.count).appendRight
      data.locals) data.awayPartition

def Data.exposedNode (data : Data boundary external) :
    Item ((external ++ List.replicate data.count data.signature) ++
      data.locals) :=
  data.node.exposedNode
    ((retainOpenWire (external := external) data.signature
      data.count).appendRight data.locals)
    (fun wire => (freshOpenWire external data.signature wire).appendLeft
      data.locals)

def Data.exposedRegion (data : Data boundary external) :
    Region (external ++ List.replicate data.count data.signature) :=
  .mk data.locals
    (.cons data.exposedNode data.exposedAway)

def Data.exposedBoundary (data : Data boundary external) :
    Vars (external ++ List.replicate data.count data.signature) boundary :=
  Vars.partitionOutput
    (collapseOpen external data.survivor data.count)
    data.collapsedBoundary data.boundaryPartition

/-- Root applicability.  Every fresh external wire receives either an
ordered boundary position or one exact non-identity body port through the
active partition.  The selected identity and every other identity-node port
are excluded from body coverage.  `boundarySurjective` is the exact
boundary-partition obligation required to construct the expanded endpoint. -/
structure Applicability (data : Data boundary external) : Prop where
  absorbedNonIdentity : ∀ wire : Fin data.count,
    0 < data.exposedBoundary.countIndex
          (freshOpenWire external data.signature wire).index.val ∨
      ∃ port : ItemSeq.Port data.away
          data.node.survivor,
        port.IsNonIdentity ∧
          (data.awayPartition.output
            data.node.survivor port).val =
            (freshOpenWire external data.signature wire).appendLeft data.locals
  boundarySurjective : ∀ wire : Fin
      (external ++ List.replicate data.count data.signature).length,
    ∃ position : Fin boundary.length,
      (data.exposedBoundary.get position).index = wire

theorem exposedBoundary_collapse (data : Data boundary external) :
    data.exposedBoundary.map
      (fun wire => collapseOpen external data.survivor data.count wire) =
        data.collapsedBoundary := by
  exact boundaryPartitionOutput_map _ _ _

end Open

/-- An open identification step uses exact presentations of both external
contexts; the computed bodies and boundary partitions remain the sole syntax
authority. -/
structure Open (source target : OpenDiagram boundary) where
  external : List Sig
  data : Open.Data boundary external
  applicability : Open.Applicability data
  sourceExternal : WireEquiv source.external external
  sourceBody : RegionIso sourceExternal source.body data.collapsedRegion
  sourceBoundary : ∀ position : Fin boundary.length,
    sourceExternal (source.boundaryWire.get position) =
      data.collapsedBoundary.get position
  sourceCanonical : data.collapsedRegion.Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    data.collapsedBoundary data.collapsedRegion
  targetExternal : WireEquiv target.external
    (external ++ List.replicate data.count data.signature)
  targetBody : RegionIso targetExternal target.body data.exposedRegion
  targetBoundary : ∀ position : Fin boundary.length,
    targetExternal (target.boundaryWire.get position) =
      data.exposedBoundary.get position
  targetCanonical : data.exposedRegion.Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    data.exposedBoundary data.exposedRegion

namespace Open

def collapsedPresentation
    {boundary : List Sig} {source target : OpenDiagram boundary}
    (step : Identification.Open source target) : OpenDiagram boundary := {
  external := step.external
  boundaryWire := step.data.collapsedBoundary
  boundarySurjective := step.data.collapsedBoundarySurjective
  body := step.data.collapsedRegion
  canonical := step.sourceCanonical
  externalTwoEnded := step.sourceExternalTwoEnded
}

def exposedPresentation
    {boundary : List Sig} {source target : OpenDiagram boundary}
    (step : Identification.Open source target) : OpenDiagram boundary := {
  external := step.external ++
    List.replicate step.data.count step.data.signature
  boundaryWire := step.data.exposedBoundary
  boundarySurjective := step.applicability.boundarySurjective
  body := step.data.exposedRegion
  canonical := step.targetCanonical
  externalTwoEnded := step.targetExternalTwoEnded
}

private def Data.mapInternalWire
    {boundary represented : List Sig} (data : Data boundary represented) :
    ∀ {wireSignature},
      Region.InternalWire data.collapsedRegion wireSignature →
      Region.InternalWire data.exposedRegion wireSignature
  | _, .here wire => .here wire
  | _, .nested (.tail wire) =>
      .nested (.tail (wire.partitionOutput
        ((collapseOpen represented data.survivor data.count).appendRight
          data.locals) data.away data.awayPartition))

private theorem Data.ownerPath_mapInternalWire
    {boundary represented : List Sig} (data : Data boundary represented)
    (wire : Region.InternalWire data.collapsedRegion wireSignature) :
    (data.mapInternalWire wire).ownerPath = wire.ownerPath := by
  cases wire with
  | here wire => rfl
  | nested nested =>
      cases nested with
      | tail wire =>
          exact ItemSeq.InternalWire.ownerPathFrom_partitionOutput
            ((collapseOpen represented data.survivor data.count).appendRight
              data.locals) data.away data.awayPartition wire 1

/-- Every wire of the exact collapsed root presentation survives exposure
with the same derived scope path. -/
theorem existsPresentedWire_scopePath
    {boundary : List Sig} {source target : OpenDiagram boundary}
    (step : Identification.Open source target)
    {wireSignature}
    (wire : OpenDiagram.Wire step.collapsedPresentation wireSignature) :
    ∃ targetWire : OpenDiagram.Wire
        step.exposedPresentation wireSignature,
      step.exposedPresentation.scopePath targetWire =
        step.collapsedPresentation.scopePath wire := by
  cases wire with
  | external externalWire =>
      refine ⟨.external (externalWire.appendLeft
        (List.replicate step.data.count step.data.signature)), ?_⟩
      rw [OpenDiagram.scopePath_external, OpenDiagram.scopePath_external]
  | internal internalWire =>
      let targetWire := step.data.mapInternalWire internalWire
      refine ⟨.internal targetWire, ?_⟩
      rw [OpenDiagram.scopePath_internal, OpenDiagram.scopePath_internal]
      exact step.data.ownerPath_mapInternalWire internalWire

noncomputable def iso
    (sourceIso : OpenDiagramIso source source')
    (step : Open source target)
    (targetIso : OpenDiagramIso target target') :
    Open source' target' := {
  external := step.external
  data := step.data
  applicability := step.applicability
  sourceExternal := sourceIso.external.symm.trans step.sourceExternal
  sourceBody := sourceIso.body.symm.trans step.sourceBody
  sourceBoundary := by
    intro position
    change step.sourceExternal
        (sourceIso.external.symm (source'.boundaryWire.get position)) = _
    rw [← sourceIso.boundary_eq position, WireEquiv.symm_apply_apply]
    exact step.sourceBoundary position
  sourceCanonical := step.sourceCanonical
  sourceExternalTwoEnded := step.sourceExternalTwoEnded
  targetExternal := targetIso.external.symm.trans step.targetExternal
  targetBody := targetIso.body.symm.trans step.targetBody
  targetBoundary := by
    intro position
    change step.targetExternal
        (targetIso.external.symm (target'.boundaryWire.get position)) = _
    rw [← targetIso.boundary_eq position, WireEquiv.symm_apply_apply]
    exact step.targetBoundary position
  targetCanonical := step.targetCanonical
  targetExternalTwoEnded := step.targetExternalTwoEnded
}

end Open

end Identification

def Identification : Rule :=
  fun source target =>
    Contextual (symmetric Identification.Local) source target ∨
      Nonempty (Identification.Open source target) ∨
      Nonempty (Identification.Open target source)

theorem Identification.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Identification source target)
    (targetIso : OpenDiagramIso target target') :
    Identification source' target' := by
  rcases step with localStep | openForward | openBackward
  · exact Or.inl (Contextual.iso sourceIso localStep targetIso)
  · rcases openForward with ⟨openStep⟩
    exact Or.inr (Or.inl
      ⟨Identification.Open.iso sourceIso openStep targetIso⟩)
  · rcases openBackward with ⟨openStep⟩
    exact Or.inr (Or.inr
      ⟨Identification.Open.iso targetIso openStep sourceIso⟩)

theorem Identification.respectsTargetIso
    (step : Identification source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Identification source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Identification.iso (OpenDiagramIso.refl source) step targetIso

theorem Identification.backward_respectsTargetIso
    (step : Identification target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Identification target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Identification.iso targetIso step (OpenDiagramIso.refl source)

theorem Identification.symm
    (step : Identification source target) :
    Identification target source := by
  rcases step with localStep | openForward | openBackward
  · rcases localStep with ⟨wires, before, after, occurrence,
      targetCanonical, targetExternalTwoEnded, targetIso, localEvidence⟩
    let reverseOccurrence : Occurrence after target := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := targetCanonical
      sourceExternalTwoEnded := targetExternalTwoEnded
      host_iso := targetIso
    }
    refine Or.inl ⟨wires, after, before, reverseOccurrence,
      occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
      occurrence.host_iso, ?_⟩
    cases polarity : occurrence.context.polarity <;>
      simp only [polarity, atPolarity, converse, symmetric]
        at localEvidence ⊢
    · exact localEvidence.elim Or.inr Or.inl
    · exact localEvidence.elim Or.inr Or.inl
  · exact Or.inr (Or.inr openForward)
  · exact Or.inr (Or.inl openBackward)

end VisualProof.Rule
