import VisualProof.Rule.Vacuity
import VisualProof.Rule.Presentation
import VisualProof.Rule.Identification

namespace VisualProof.Rule

open Diagram
open Theory

namespace VacuousAssembly

/-! ## Addition embeddings

The assembly layer relates existing recursive syntax.  It does not define a
second diagram, item, wire, or port representation.  A wire embedding records
only how retained typed wires occur in the target; its complement is the
proof-only ownership predicate `Fresh`.
-/

/-- A signature-preserving injection between two existing wire contexts. -/
structure WireEmbedding (source target : List Sig) where
  toRenaming : WireRenaming source target
  index_injective : ∀ {signature}
      (left right : Var source signature),
    (toRenaming left).index.val = (toRenaming right).index.val → left = right

instance : CoeFun (WireEmbedding source target)
    (fun _ => ∀ {signature}, Var source signature → Var target signature) :=
  ⟨fun embedding => fun {_signature} wire => embedding.toRenaming wire⟩

namespace WireEmbedding

private inductive AppendView (left right : List Sig) :
    {signature : Sig} → Var (left ++ right) signature → Type
  | fromLeft (wire : Var left signature) :
      AppendView left right (wire.appendLeft right)
  | fromRight (wire : Var right signature) :
      AppendView left right (Var.appendRight left wire)

private def appendView :
    {left right : List Sig} → {signature : Sig} →
      (wire : Var (left ++ right) signature) → AppendView left right wire
  | [], _, _, wire => .fromRight wire
  | _ :: _, _, _, .here => .fromLeft .here
  | _ :: tail, right, _, .there rest =>
      match appendView (left := tail) (right := right) rest with
      | .fromLeft wire => .fromLeft (.there wire)
      | .fromRight wire => .fromRight wire

@[simp] private theorem appendView_appendLeft
    (wire : Var left signature) :
    appendView (wire.appendLeft right) = .fromLeft wire := by
  induction wire with
  | here => rfl
  | there wire induction =>
      simp only [Var.appendLeft, appendView, induction]

@[simp] private theorem appendView_appendRight
    (wire : Var right signature) :
    appendView (Var.appendRight left wire) = .fromRight wire := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [Var.appendRight, appendView, induction]

/-- A target wire belongs to the assembly complement exactly when it has no
retained source preimage. -/
def Fresh (embedding : WireEmbedding source target)
    (wire : Var target signature) : Prop :=
  ∀ sourceWire : Var source signature, embedding sourceWire ≠ wire

def refl (context : List Sig) : WireEmbedding context context where
  toRenaming := WireRenaming.id
  index_injective := by
    intro signature left right equality
    exact var_eq_of_index_eq left right equality
  where
    var_eq_of_index_eq {context : List Sig} {signature : Sig} :
        (left right : Var context signature) →
          left.index.val = right.index.val → left = right
      | .here, .here, _ => rfl
      | .here, .there _, equality => by
          simp only [Var.index, Fin.val_zero, Fin.val_succ] at equality
          omega
      | .there _, .here, equality => by
          simp only [Var.index, Fin.val_zero, Fin.val_succ] at equality
          omega
      | .there left, .there right, equality => by
          simp only [Var.index, Fin.val_succ] at equality
          exact congrArg Var.there (var_eq_of_index_eq left right (by omega))

/-- Combine inherited and local additions without changing either syntax
authority.  Target locals not in `localEmbedding`'s image are precisely the fresh
locals introduced at this region. -/
def append
    (outer : WireEmbedding sourceOuter targetOuter)
    (localEmbedding : WireEmbedding sourceLocal targetLocal) :
    WireEmbedding (sourceOuter ++ sourceLocal) (targetOuter ++ targetLocal) where
  toRenaming := ⟨Var.appendMap
    (fun wire => (outer wire).appendLeft targetLocal)
    (fun wire => Var.appendRight targetOuter (localEmbedding wire))⟩
  index_injective := by
    intro signature left right equality
    cases appendView left with
    | fromLeft leftWire =>
        cases appendView right with
        | fromLeft rightWire =>
            simp only [Var.appendMap_left, Var.index_appendLeft] at equality
            exact congrArg (fun wire => wire.appendLeft sourceLocal)
              (outer.index_injective leftWire rightWire equality)
        | fromRight rightWire =>
            simp only [Var.appendMap_left, Var.appendMap_right,
              Var.index_appendLeft, Var.index_appendRight] at equality
            have outerBound := (outer leftWire).index.isLt
            omega
    | fromRight leftWire =>
        cases appendView right with
        | fromLeft rightWire =>
            simp only [Var.appendMap_left, Var.appendMap_right,
              Var.index_appendLeft, Var.index_appendRight] at equality
            have outerBound := (outer rightWire).index.isLt
            omega
        | fromRight rightWire =>
            simp only [Var.appendMap_right, Var.index_appendRight] at equality
            exact congrArg (Var.appendRight sourceOuter)
              (localEmbedding.index_injective leftWire rightWire (by omega))

@[ext] theorem ext
    (left right : WireEmbedding source target)
    (applyEq : ∀ {signature} (wire : Var source signature),
      left wire = right wire) :
    left = right := by
  cases left with
  | mk leftRename leftInjective =>
      cases right with
      | mk rightRename rightInjective =>
          have renameEq : leftRename = rightRename := by
            apply WireRenaming.ext
            exact applyEq
          subst rightRename
          rfl

theorem append_refl (outer locals : List Sig) :
    append (refl outer) (refl locals) = refl (outer ++ locals) := by
  apply WireEmbedding.ext
  intro signature wire
  exact Var.appendCases
    (motive := fun {signature} wire =>
      append (refl outer) (refl locals) wire = refl (outer ++ locals) wire)
    (leftCase := by
      intro signature inherited
      simp [append, refl, WireRenaming.id])
    (rightCase := by
      intro signature localWire
      simp [append, refl, WireRenaming.id])
    wire

def complementSize (_embedding : WireEmbedding source target) : Nat :=
  target.length - source.length

end WireEmbedding

/-- A retained injection together with the partial collapse origin of every
target wire. `none` marks a bare assembly wire; `some sourceWire` marks either
the retained wire itself or an equated complement wire. -/
structure WireExtension (source target : List Sig) where
  retained : WireEmbedding source target
  origin : ∀ {signature}, Var target signature →
    Option (Var source signature)
  retained_origin : ∀ {signature} (wire : Var source signature),
    origin (retained wire) = some wire

namespace WireExtension

/-- A target wire owned by the complement rather than the retained image. -/
def Complement (extension : WireExtension source target)
    (wire : Var target signature) : Prop :=
  ∀ sourceWire : Var source signature,
    extension.retained sourceWire ≠ wire

def Bare (extension : WireExtension source target)
    (wire : Var target signature) : Prop :=
  extension.Complement wire ∧ extension.origin wire = none

def Equated (extension : WireExtension source target)
    (wire : Var target signature) (origin : Var source signature) : Prop :=
  extension.Complement wire ∧ extension.origin wire = some origin

def refl (context : List Sig) : WireExtension context context where
  retained := WireEmbedding.refl context
  origin := fun wire => some wire
  retained_origin := fun _ => rfl

private def appendOrigin
    (outer : WireExtension sourceOuter targetOuter)
    (locals : WireExtension sourceLocal targetLocal) :
    ∀ {signature}, Var (targetOuter ++ targetLocal) signature →
      Option (Var (sourceOuter ++ sourceLocal) signature)
  | _, wire =>
      match WireEmbedding.appendView wire with
      | .fromLeft outerWire =>
          (outer.origin outerWire).map
            (fun sourceWire => sourceWire.appendLeft sourceLocal)
      | .fromRight localWire =>
          (locals.origin localWire).map
            (fun sourceWire => Var.appendRight sourceOuter sourceWire)

def append
    (outer : WireExtension sourceOuter targetOuter)
    (locals : WireExtension sourceLocal targetLocal) :
    WireExtension (sourceOuter ++ sourceLocal) (targetOuter ++ targetLocal) where
  retained := outer.retained.append locals.retained
  origin := appendOrigin outer locals
  retained_origin := by
    intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        appendOrigin outer locals
            (outer.retained.append locals.retained wire) = some wire)
      (leftCase := by
        intro signature inherited
        simp only [WireEmbedding.append, Var.appendMap_left]
        change appendOrigin outer locals
          ((outer.retained inherited).appendLeft targetLocal) =
            some (inherited.appendLeft sourceLocal)
        simp [appendOrigin, outer.retained_origin])
      (rightCase := by
        intro signature localWire
        simp only [WireEmbedding.append, Var.appendMap_right]
        change appendOrigin outer locals
          (Var.appendRight targetOuter (locals.retained localWire)) =
            some (Var.appendRight sourceOuter localWire)
        simp [appendOrigin, locals.retained_origin])
      wire

@[ext] theorem ext
    (left right : WireExtension source target)
    (retainedEq : left.retained = right.retained)
    (originEq : ∀ {signature} (wire : Var target signature),
      left.origin wire = right.origin wire) :
    left = right := by
  cases left with
  | mk leftRetained leftOrigin leftLaw =>
      cases right with
      | mk rightRetained rightOrigin rightLaw =>
          dsimp only at retainedEq originEq
          subst rightRetained
          have originsEq : @leftOrigin = @rightOrigin := by
            funext signature wire
            exact originEq wire
          subst rightOrigin
          rfl

theorem append_refl (outer locals : List Sig) :
    append (refl outer) (refl locals) = refl (outer ++ locals) := by
  apply WireExtension.ext
  · exact WireEmbedding.append_refl outer locals
  · intro signature wire
    apply Var.appendCases
      (motive := fun wire =>
        (append (refl outer) (refl locals)).origin wire =
          (refl (outer ++ locals)).origin wire)
      (leftCase := by
        intro signature inherited
        simp [append, appendOrigin, refl])
      (rightCase := by
        intro signature localWire
        simp [append, appendOrigin, refl])
      wire

def complementSize (_extension : WireExtension source target) : Nat :=
  target.length - source.length

end WireExtension

/-- A context containing exactly the origin-bearing wires used by one
retained item.  Its total collapse is the existing typed partition authority;
bare wires remain outside this fiber. -/
structure Fiber (extension : WireExtension source target) where
  context : List Sig
  embedding : WireEmbedding context target
  collapse : WireRenaming context source
  origin_eq : ∀ {signature} (wire : Var context signature),
    extension.origin (embedding wire) = some (collapse wire)

namespace Fiber

def refl (context : List Sig) : Fiber (WireExtension.refl context) where
  context := context
  embedding := WireEmbedding.refl context
  collapse := WireRenaming.id
  origin_eq := fun _ => rfl

end Fiber

/-- Reflexive evidence using the existing typed item-port partition. -/
def Item.PortPartition.refl (item : Item wires) :
    Item.PortPartition WireRenaming.id item where
  output := fun wire _ => ⟨wire, rfl⟩

private def retainExpansion :
    (arity : Nat) → Identification.PortExpansion 0 arity arity
  | 0 => .nil
  | arity + 1 => .retain (retainExpansion arity)

private theorem retainExpansion_select
    (position : Fin arity) :
    (retainExpansion arity).select position = Sum.inl position := by
  induction arity with
  | zero => exact Fin.elim0 position
  | succ arity induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      simp only [retainExpansion, Identification.PortExpansion.select]
      rw [Fin.cases_succ]
      rw [induction rest]

/-- A retained identity node first distributes its existing ports through an
origin-bearing fiber, then interleaves actual complement-owned target ports
using Identification's existing `PortExpansion`. -/
structure IdentityExpansion
    (extension : WireExtension source target)
    {signature : Sig} {sourceArity : Nat}
    (sourcePorts : Fin sourceArity → Var source signature) : Type where
  fiber : Fiber extension
  partition : Item.PortPartition fiber.collapse
    (.identity signature sourceArity sourcePorts)
  addedCount : Nat
  added : Fin addedCount → Var target signature
  added_complement : ∀ position, extension.Complement (added position)
  targetArity : Nat
  expansion : Identification.PortExpansion addedCount
    sourceArity targetArity
  added_position : ∀ position : Fin addedCount,
    ∃ targetPosition, expansion.select targetPosition = Sum.inr position

namespace IdentityExpansion

def basePort
    {source target : List Sig}
    {extension : WireExtension source target}
    {signature : Sig} {sourceArity : Nat}
    {sourcePorts : Fin sourceArity → Var source signature}
    (data : IdentityExpansion extension sourcePorts)
    (position : Fin sourceArity) : Var target signature :=
  data.fiber.embedding
    (data.partition.output (sourcePorts position) (.identity position)).val

def targetPorts
    {source target : List Sig}
    {extension : WireExtension source target}
    {signature : Sig} {sourceArity : Nat}
    {sourcePorts : Fin sourceArity → Var source signature}
    (data : IdentityExpansion extension sourcePorts) :
    Fin data.targetArity → Var target signature := fun position =>
  match data.expansion.select position with
  | .inl retainedPosition => data.basePort retainedPosition
  | .inr addedPosition => data.added addedPosition

def complementSize
    {source target : List Sig}
    {extension : WireExtension source target}
    {signature : Sig} {sourceArity : Nat}
    {sourcePorts : Fin sourceArity → Var source signature}
    (data : IdentityExpansion extension sourcePorts) : Nat :=
  data.targetArity - sourceArity

def refl
    {wires : List Sig} {signature : Sig} {arity : Nat}
    (ports : Fin arity → Var wires signature) :
    IdentityExpansion (WireExtension.refl wires) ports where
  fiber := Fiber.refl wires
  partition := Item.PortPartition.refl (.identity signature arity ports)
  addedCount := 0
  added := Fin.elim0
  added_complement := fun position => nomatch position
  targetArity := arity
  expansion := retainExpansion arity
  added_position := fun position => nomatch position

theorem refl_targetPorts
    {wires : List Sig} {signature : Sig} {arity : Nat}
    (ports : Fin arity → Var wires signature) :
    @targetPorts wires wires (WireExtension.refl wires) signature arity
      ports (refl ports) = ports := by
  funext position
  simp only [targetPorts, refl, retainExpansion_select, basePort,
    Fiber.refl, Item.PortPartition.refl, WireEmbedding.refl,
    WireRenaming.id]

end IdentityExpansion

/-! ## Exact retained occurrences and physical ports

All event references below point into the existing recursive `ItemSeq` syntax.
The positional enumeration keeps the multiplicity and order needed to derive a
`Presentation.Local.replace`; list membership alone is deliberately not used as
an exactness claim.
-/

/-- One positive-arity identity item at one exact physical item position. -/
def mappedAtom
    {source target : List Sig}
    {extension : WireExtension source target}
    {arguments : List Sig}
    {sourceHead : Var source (.rel arguments)}
    {sourcePorts : Vars source arguments}
    (fiber : Fiber extension)
    (partition : Item.PortPartition fiber.collapse
      (.atom sourceHead sourcePorts)) : Item target :=
  ((Item.atom sourceHead sourcePorts).partitionOutput
    fiber.collapse partition).renameWires fiber.embedding.toRenaming

mutual
  inductive RegionAddition :
      {source target : List Sig} →
      WireExtension source target → Region source → Region target → Type
    | mk
        {extension : WireExtension source target}
        (locals : WireExtension sourceLocals targetLocals)
        (items : ItemSeqAddition (extension.append locals)
          sourceItems targetItems) :
        RegionAddition extension
          (.mk sourceLocals sourceItems) (.mk targetLocals targetItems)

  inductive ItemSeqAddition :
      {source target : List Sig} →
      WireExtension source target →
      ItemSeq source → ItemSeq target → Type
    | nil : ItemSeqAddition extension .nil .nil
    | atom
        {extension : WireExtension source target}
        {arguments : List Sig}
        {sourceHead : Var source (.rel arguments)}
        {sourcePorts : Vars source arguments}
        {sourceTail : ItemSeq source} {targetTail : ItemSeq target}
        (fiber : Fiber extension)
        (partition : Item.PortPartition fiber.collapse
          (.atom sourceHead sourcePorts))
        (tail : ItemSeqAddition extension sourceTail targetTail) :
        ItemSeqAddition extension
          (.cons (.atom sourceHead sourcePorts) sourceTail)
          (.cons (mappedAtom fiber partition) targetTail)
    | identity
        {extension : WireExtension source target}
        {signature : Sig} {sourceArity : Nat}
        {sourcePorts : Fin sourceArity → Var source signature}
        {sourceTail : ItemSeq source} {targetTail : ItemSeq target}
        (ports : IdentityExpansion extension sourcePorts)
        (tail : ItemSeqAddition extension sourceTail targetTail) :
        ItemSeqAddition extension
          (.cons (.identity signature sourceArity sourcePorts) sourceTail)
          (.cons (.identity signature ports.targetArity ports.targetPorts)
            targetTail)
    | cut
        {extension : WireExtension source target}
        {sourceBody : Region source} {targetBody : Region target}
        {sourceTail : ItemSeq source} {targetTail : ItemSeq target}
        (body : RegionAddition extension sourceBody targetBody)
        (tail : ItemSeqAddition extension sourceTail targetTail) :
        ItemSeqAddition extension
          (.cons (.cut sourceBody) sourceTail)
          (.cons (.cut targetBody) targetTail)
    | addIdentity
        {extension : WireExtension source target}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var target signature}
        {sourceItems : ItemSeq source} {targetTail : ItemSeq target}
        (tail : ItemSeqAddition extension sourceItems targetTail) :
        ItemSeqAddition extension sourceItems
          (.cons (.identity signature arity ports) targetTail)
end

mutual
  def RegionAddition.refl :
      (region : Region wires) →
        RegionAddition (WireExtension.refl wires) region region
    | .mk locals items => by
        have itemAddition : ItemSeqAddition
            ((WireExtension.refl wires).append (WireExtension.refl locals))
            items items := by
          rw [WireExtension.append_refl]
          exact ItemSeqAddition.refl items
        exact .mk (WireExtension.refl locals) itemAddition

  def ItemSeqAddition.refl :
      (items : ItemSeq wires) →
        ItemSeqAddition (WireExtension.refl wires) items items
    | .nil => .nil
    | .cons (.atom head ports) tail => by
        let fiber := Fiber.refl wires
        let partition := Item.PortPartition.refl (.atom head ports)
        have itemEq := Item.partitionOutput_renameWires WireRenaming.id
          (.atom head ports) partition
        simpa only [mappedAtom, fiber, Fiber.refl, WireEmbedding.refl,
          itemEq] using
          ItemSeqAddition.atom fiber partition (ItemSeqAddition.refl tail)
    | .cons (.identity signature arity ports) tail => by
        have targetPorts := IdentityExpansion.refl_targetPorts ports
        have identityEq :
            Item.identity signature (IdentityExpansion.refl ports).targetArity
                (IdentityExpansion.refl ports).targetPorts =
              Item.identity signature arity ports := by
          rw [targetPorts]
          change Item.identity signature arity ports =
            Item.identity signature arity ports
          rfl
        have result := ItemSeqAddition.identity
          (IdentityExpansion.refl ports) (ItemSeqAddition.refl tail)
        rw [identityEq] at result
        exact result
    | .cons (.cut body) tail =>
        .cut (RegionAddition.refl body) (ItemSeqAddition.refl tail)
end

mutual
  def RegionAddition.complementSize :
      RegionAddition extension source target → Nat
    | .mk locals items =>
        locals.complementSize + items.complementSize

  def ItemSeqAddition.complementSize :
      ItemSeqAddition extension source target → Nat
    | .nil => 0
    | .atom _ _ tail => tail.complementSize
    | .identity ports tail =>
        ports.complementSize + tail.complementSize
    | .cut body tail => body.complementSize + tail.complementSize
    | .addIdentity tail => 1 + tail.complementSize
end

/-- A source and its generic assembly insertion presented over exactly the
same external context and ordered boundary.  Assembly insertion cannot add a
boundary entry; all fresh assembly wires are locally owned by a region. -/
structure OpenAddition
    (source target : OpenDiagram boundary) : Type where
  interface : OpenDiagram boundary
  sourceBody : Region interface.external
  targetBody : Region interface.external
  sourceCanonical : sourceBody.Canonical
  targetCanonical : targetBody.Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire sourceBody
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire targetBody
  sourceIso : OpenDiagramIso source
    (interface.withBody sourceBody sourceCanonical sourceExternalTwoEnded)
  targetIso : OpenDiagramIso target
    (interface.withBody targetBody targetCanonical targetExternalTwoEnded)
  body : RegionAddition (WireExtension.refl interface.external)
    sourceBody targetBody

namespace OpenAddition

noncomputable def refl
    (diagram : OpenDiagram boundary) : OpenAddition diagram diagram where
  interface := diagram
  sourceBody := diagram.body
  targetBody := diagram.body
  sourceCanonical := diagram.canonical
  targetCanonical := diagram.canonical
  sourceExternalTwoEnded := diagram.externalTwoEnded
  targetExternalTwoEnded := diagram.externalTwoEnded
  sourceIso := OpenDiagramIso.refl diagram
  targetIso := OpenDiagramIso.refl diagram
  body := RegionAddition.refl diagram.body

def complementSize (addition : OpenAddition source target) : Nat :=
  addition.body.complementSize

end OpenAddition

/-! ## Raw absorption endpoints -/

/-- Exact erased endpoint data shared by raw absorption constructors.  The
local syntax and occurrence are data; no primitive rule witness is stored. -/
structure RawContext
    (beforeRegion afterRegion : Region wires)
    (before after : OpenDiagram boundary) where
  occurrence : Occurrence beforeRegion before
  targetCanonical : (occurrence.context.fill afterRegion).Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire
      (occurrence.context.fill afterRegion)
  targetIso : OpenDiagramIso after
    (occurrence.interface.withBody
      (occurrence.context.fill afterRegion)
      targetCanonical targetExternalTwoEnded)

namespace RawContext

def contextual
    (raw : RawContext beforeRegion afterRegion before after)
    (localRule : LocalRule)
    (evidence : localRule beforeRegion afterRegion) :
    Contextual (symmetric localRule) before after :=
  ⟨_, beforeRegion, afterRegion, raw.occurrence,
    raw.targetCanonical, raw.targetExternalTwoEnded, raw.targetIso,
    atPolarity_symmetric_of raw.occurrence.context.polarity evidence⟩

end RawContext

/-- Raw isolated-point absorption data. -/
structure RawPoint (before after : OpenDiagram boundary) where
  outer : List Sig
  locals : List Sig
  items : ItemSeq (outer ++ locals)
  signature : Sig
  endpoint : RawContext
    (Vacuity.Point.plain locals items)
    (Vacuity.Point.present locals items signature) before after

def RawPoint.toVacuity (raw : RawPoint before after) :
    Vacuity before after :=
  raw.endpoint.contextual
    Vacuity.Local (Vacuity.Local.point raw.locals raw.items raw.signature)

/-- Raw unary-end home data. -/
structure RawPin (before after : OpenDiagram boundary) where
  outer : List Sig
  locals : List Sig
  items : ItemSeq (outer ++ locals)
  signature : Sig
  wire : Var (outer ++ locals) signature
  endpoint : RawContext
    (Vacuity.Pin.plain locals items)
    (Vacuity.Pin.present locals items signature wire) before after

def RawPin.toVacuity (raw : RawPin before after) : Vacuity before after :=
  raw.endpoint.contextual
    Vacuity.Local
    (Vacuity.Local.pin raw.locals raw.items raw.signature raw.wire)

/-- Raw single-stub attachment data. -/
structure RawStub (before after : OpenDiagram boundary) where
  outer : List Sig
  hostLocals : List Sig
  leading : ItemSeq (outer ++ hostLocals)
  trailing : ItemSeq (outer ++ hostLocals)
  signature : Sig
  arity : Nat
  ports : Fin arity → Var (outer ++ hostLocals) signature
  position : Fin (arity + 1)
  far : Vacuity.Stub.Far
    (Vacuity.Stub.freshWire outer hostLocals signature)
    (Vacuity.Stub.extendedItems hostLocals leading trailing
      signature arity ports position)
  endpoint : RawContext
    (Vacuity.Stub.plain hostLocals leading trailing signature arity ports)
    (Vacuity.Stub.present hostLocals leading trailing signature arity ports
      position far) before after

def RawStub.toVacuity (raw : RawStub before after) : Vacuity before after :=
  raw.endpoint.contextual
    Vacuity.Local
    (Vacuity.Local.stub raw.hostLocals raw.leading raw.trailing
      raw.signature raw.arity raw.ports raw.position raw.far)

/-- Raw equality-presentation replacement used only as the final bookkeeping
edge from a computed tree form to the accepted physical identity syntax. -/
structure RawPresentation (before after : OpenDiagram boundary) where
  outer : List Sig
  locals : List Sig
  retained : ItemSeq (outer ++ locals)
  signature : Sig
  sourceConfiguration : Presentation.Configuration
    (outer ++ locals) signature
  targetConfiguration : Presentation.Configuration
    (outer ++ locals) signature
  applicability : Presentation.Applicability outer locals retained
    sourceConfiguration targetConfiguration
  endpoint : RawContext
    (Presentation.region locals retained sourceConfiguration)
    (Presentation.region locals retained targetConfiguration) before after

def RawPresentation.toPresentation
    (raw : RawPresentation before after) : Presentation before after :=
  raw.endpoint.contextual
    Presentation.Local
    (Presentation.Local.replace raw.locals raw.retained raw.signature
      raw.sourceConfiguration raw.targetConfiguration raw.applicability)

/-- Raw equated-with-transfer absorption data.  The active identification
partition and its nonempty non-identity transfer certificate are fields of
the existing `Identification.Local.Data` and `.Applicability`. -/
structure RawEquated (before after : OpenDiagram boundary) where
  outer : List Sig
  data : Identification.Local.Data outer
  applicability : Identification.Local.Applicability data
  endpoint : RawContext data.collapsedRegion data.exposedRegion before after

def RawEquated.toIdentification
    (raw : RawEquated before after) : Identification before after :=
  Or.inl (raw.endpoint.contextual
    Identification.Local
    (Identification.Local.expose raw.data raw.applicability))

/-! A bare wire component has one stub end and a finite family of additional
unary ends.  `Vacuity.Stub.Far` is reused as the existing raw home/visibility
path for one unary end; this topology stores no primitive rule witness. -/

inductive ExtraPins
    (wire : Var baseWires signature) :
    ItemSeq baseWires → ItemSeq baseWires → Type
  | done (items) : ExtraPins wire items items
  | add (home : Vacuity.Stub.Far wire items)
      (tail : ExtraPins wire home.result finalItems) :
      ExtraPins wire items finalItems

namespace ExtraPins

inductive Valid
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (locals : List Sig) {wire : Var (outer ++ locals) signature} :
    {startItems finalItems : ItemSeq (outer ++ locals)} →
    ExtraPins wire startItems finalItems → Type
  | done (items) : Valid interface context locals (ExtraPins.done items)
  | add {home : Vacuity.Stub.Far wire items}
      {tail : ExtraPins wire home.result finalItems}
      (targetCanonical :
        (context.fill (.mk locals home.result)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill (.mk locals home.result)))
      (tailValid : Valid interface context locals tail) :
      Valid interface context locals (ExtraPins.add home tail)

def Valid.finalCanonical
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {startItems finalItems : ItemSeq (outer ++ locals)}
    {pins : ExtraPins wire startItems finalItems}
    (valid : Valid (wire := wire) interface context locals pins)
    (sourceCanonical : (context.fill (.mk locals startItems)).Canonical) :
    (context.fill (.mk locals finalItems)).Canonical := by
  induction valid with
  | done => exact sourceCanonical
  | add targetCanonical targetExternal tailValid induction =>
      exact induction targetCanonical

def Valid.finalExternalTwoEnded
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {startItems finalItems : ItemSeq (outer ++ locals)}
    {pins : ExtraPins wire startItems finalItems}
    (valid : Valid (wire := wire) interface context locals pins)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals startItems))) :
    OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (.mk locals finalItems)) := by
  induction valid with
  | done => exact sourceExternalTwoEnded
  | add targetCanonical targetExternal tailValid induction =>
      exact induction targetExternal

def endpoint
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {startItems finalItems : ItemSeq (outer ++ locals)}
    {pins : ExtraPins wire startItems finalItems}
    (valid : Valid (wire := wire) interface context locals pins)
    (sourceCanonical : (context.fill (.mk locals startItems)).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals startItems))) :
    OpenDiagram boundary :=
  interface.withBody (context.fill (.mk locals finalItems))
    (valid.finalCanonical sourceCanonical)
    (valid.finalExternalTwoEnded sourceExternalTwoEnded)

/-- One raw home in a component determines the exact primitive pin endpoint.
The descendant case derives its occurrence by composing the component's
actual recursive context with `Far`'s existing navigation data. -/
noncomputable def rawPin
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {sourceDiagram : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {items : ItemSeq (outer ++ locals)}
    {sourceCanonical : (context.fill (.mk locals items)).Canonical}
    {sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals items))}
    (sourceIso : OpenDiagramIso sourceDiagram
      (interface.withBody (context.fill (.mk locals items))
        sourceCanonical sourceExternalTwoEnded))
    (home : Vacuity.Stub.Far wire items)
    (targetCanonical : (context.fill (.mk locals home.result)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals home.result))) :
    RawPin
      sourceDiagram
      (interface.withBody (context.fill (.mk locals home.result))
        targetCanonical targetExternalTwoEnded) := by
  cases home with
  | atBase =>
      exact {
        outer := outer
        locals := locals
        items := items
        signature := signature
        wire := wire
        endpoint := {
          occurrence := {
            interface := interface
            context := context
            sourceCanonical := sourceCanonical
            sourceExternalTwoEnded := sourceExternalTwoEnded
            host_iso := sourceIso
          }
          targetCanonical := by
            simpa [Vacuity.Pin.present, Vacuity.Stub.Far.result] using
              targetCanonical
          targetExternalTwoEnded := by
            intro wireSignature selected
            exact targetExternalTwoEnded selected
          targetIso := OpenDiagramIso.refl _
        }
      }
  | @below farWires before after body focus descendant farLocals farItems bodyEq =>
      subst items
      let nestedOccurrence : Occurrence
          (Vacuity.Pin.plain farLocals farItems)
          sourceDiagram := {
        interface := interface
        context := context.comp (.cut locals before after descendant)
        sourceCanonical := by
          simpa [Vacuity.Pin.plain, DiagramContext.fill, bodyEq] using
            sourceCanonical
        sourceExternalTwoEnded := by
          intro wireSignature selected
          simpa [Vacuity.Pin.plain, DiagramContext.fill, bodyEq] using
            (sourceExternalTwoEnded selected)
        host_iso := by
          simpa [Vacuity.Pin.plain, DiagramContext.fill, bodyEq] using sourceIso
      }
      exact {
        outer := _
        locals := farLocals
        items := farItems
        signature := signature
        wire := (descendant.outerWire wire).appendLeft farLocals
        endpoint := {
          occurrence := nestedOccurrence
          targetCanonical := by
            simpa [nestedOccurrence, Vacuity.Pin.present,
              Vacuity.Stub.Far.result, DiagramContext.fill] using
                targetCanonical
          targetExternalTwoEnded := by
            intro wireSignature selected
            simpa [nestedOccurrence, Vacuity.Pin.present,
              Vacuity.Stub.Far.result, DiagramContext.fill] using
                (targetExternalTwoEnded selected)
          targetIso := by
            simpa [nestedOccurrence, Vacuity.Pin.present,
              Vacuity.Stub.Far.result, DiagramContext.fill] using
                (OpenDiagramIso.refl
                  (interface.withBody
                    _
                    targetCanonical targetExternalTwoEnded))
        }
      }

end ExtraPins

/-! ## Coarse bare-component absorptions

These four cases are the shapes consumed by one accepting fixpoint
absorption.  In particular, a stub component stores one attachment and one
finite `ExtraPins` topology, not a list of point/stub/pin rule witnesses.
-/

structure RawIsolatedPoint (before : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  outer : List Sig
  context : DiagramContext interface.external outer
  locals : List Sig
  items : ItemSeq (outer ++ locals)
  signature : Sig
  sourceCanonical :
    (context.fill (Vacuity.Point.plain locals items)).Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (Vacuity.Point.plain locals items))
  sourceIso : OpenDiagramIso before
    (interface.withBody (context.fill (Vacuity.Point.plain locals items))
      sourceCanonical sourceExternalTwoEnded)
  targetCanonical :
    (context.fill (Vacuity.Point.present locals items signature)).Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (Vacuity.Point.present locals items signature))

def RawIsolatedPoint.target
    {boundary : List Sig} {before : OpenDiagram boundary}
    (raw : RawIsolatedPoint before) :
    OpenDiagram boundary :=
  raw.interface.withBody
    (raw.context.fill
      (Vacuity.Point.present raw.locals raw.items raw.signature))
    raw.targetCanonical raw.targetExternalTwoEnded

structure RawFreshStub (before : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  outer : List Sig
  context : DiagramContext interface.external outer
  hostLocals : List Sig
  items : ItemSeq (outer ++ hostLocals)
  signature : Sig
  sourceCanonical :
    (context.fill (Vacuity.Point.plain hostLocals items)).Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (Vacuity.Point.plain hostLocals items))
  sourceIso : OpenDiagramIso before
    (interface.withBody (context.fill
      (Vacuity.Point.plain hostLocals items))
      sourceCanonical sourceExternalTwoEnded)
  pointCanonical :
    (context.fill
      (Vacuity.Point.present hostLocals items signature)).Canonical
  pointExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (Vacuity.Point.present hostLocals items signature))
  far : Vacuity.Stub.Far
    (Vacuity.Stub.freshWire outer hostLocals signature)
    (Vacuity.Stub.extendedItems hostLocals items .nil signature 0
      Fin.elim0 0)
  stubCanonical :
    (context.fill (Vacuity.Stub.present hostLocals items .nil signature 0
      Fin.elim0 0 far)).Canonical
  stubExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (Vacuity.Stub.present hostLocals items .nil signature 0
      Fin.elim0 0 far))
  finalItems : ItemSeq (outer ++ (hostLocals ++ [signature]))
  pins : ExtraPins
    (Vacuity.Stub.freshWire outer hostLocals signature) far.result finalItems
  pinsValid : ExtraPins.Valid interface context (hostLocals ++ [signature]) pins

def RawFreshStub.target
    {boundary : List Sig} {before : OpenDiagram boundary}
    (raw : RawFreshStub before) : OpenDiagram boundary :=
  ExtraPins.endpoint
    (interface := raw.interface) (context := raw.context)
    (locals := raw.hostLocals ++ [raw.signature])
    raw.pinsValid raw.stubCanonical
    raw.stubExternalTwoEnded

structure RawAttachedStub (before : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  outer : List Sig
  context : DiagramContext interface.external outer
  hostLocals : List Sig
  leading : ItemSeq (outer ++ hostLocals)
  trailing : ItemSeq (outer ++ hostLocals)
  signature : Sig
  arity : Nat
  ports : Fin arity → Var (outer ++ hostLocals) signature
  position : Fin (arity + 1)
  sourceCanonical : (context.fill
    (Vacuity.Stub.plain hostLocals leading trailing signature arity ports)).Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill
      (Vacuity.Stub.plain hostLocals leading trailing signature arity ports))
  sourceIso : OpenDiagramIso before
    (interface.withBody (context.fill
      (Vacuity.Stub.plain hostLocals leading trailing signature arity ports))
      sourceCanonical sourceExternalTwoEnded)
  far : Vacuity.Stub.Far
    (Vacuity.Stub.freshWire outer hostLocals signature)
    (Vacuity.Stub.extendedItems hostLocals leading trailing signature arity
      ports position)
  stubCanonical : (context.fill
    (Vacuity.Stub.present hostLocals leading trailing signature arity ports
      position far)).Canonical
  stubExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill
      (Vacuity.Stub.present hostLocals leading trailing signature arity ports
        position far))
  finalItems : ItemSeq (outer ++ (hostLocals ++ [signature]))
  pins : ExtraPins
    (Vacuity.Stub.freshWire outer hostLocals signature) far.result finalItems
  pinsValid : ExtraPins.Valid interface context (hostLocals ++ [signature]) pins

def RawAttachedStub.target
    {boundary : List Sig} {before : OpenDiagram boundary}
    (raw : RawAttachedStub before) :
    OpenDiagram boundary :=
  ExtraPins.endpoint
    (interface := raw.interface) (context := raw.context)
    (locals := raw.hostLocals ++ [raw.signature])
    raw.pinsValid raw.stubCanonical
    raw.stubExternalTwoEnded

/-- The nonempty pin-only degenerate component. -/
structure RawPinBatch (before : OpenDiagram boundary) where
  interface : OpenDiagram boundary
  outer : List Sig
  context : DiagramContext interface.external outer
  locals : List Sig
  items : ItemSeq (outer ++ locals)
  signature : Sig
  wire : Var (outer ++ locals) signature
  sourceCanonical : (context.fill (.mk locals items)).Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded interface.boundaryWire
    (context.fill (.mk locals items))
  sourceIso : OpenDiagramIso before
    (interface.withBody (context.fill (.mk locals items))
      sourceCanonical sourceExternalTwoEnded)
  first : Vacuity.Stub.Far wire items
  finalItems : ItemSeq (outer ++ locals)
  tail : ExtraPins wire first.result finalItems
  firstTargetCanonical : (context.fill (.mk locals first.result)).Canonical
  firstTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire (context.fill (.mk locals first.result))
  tailValid : ExtraPins.Valid interface context locals tail

def RawPinBatch.valid
    {boundary : List Sig} {before : OpenDiagram boundary}
    (raw : RawPinBatch before) : ExtraPins.Valid raw.interface raw.context
      raw.locals (ExtraPins.add raw.first raw.tail) :=
  .add raw.firstTargetCanonical raw.firstTargetExternalTwoEnded raw.tailValid

def RawPinBatch.target
    {boundary : List Sig} {before : OpenDiagram boundary}
    (raw : RawPinBatch before) : OpenDiagram boundary :=
  ExtraPins.endpoint
    (interface := raw.interface) (context := raw.context)
    (locals := raw.locals)
    raw.valid raw.sourceCanonical
    raw.sourceExternalTwoEnded

/-- One coarse bare absorption accepted by the old fixpoint. -/
inductive RawBare : OpenDiagram boundary → OpenDiagram boundary → Type
  | isolated (raw : RawIsolatedPoint before) : RawBare before raw.target
  | freshStub (raw : RawFreshStub before) : RawBare before raw.target
  | attachedStub (raw : RawAttachedStub before) : RawBare before raw.target
  | pinBatch (raw : RawPinBatch before) : RawBare before raw.target

/-- The finite conclusion language of the decomposition theorem. -/
def Primitive (before after : OpenDiagram boundary) : Prop :=
  Vacuity before after ∨ Presentation before after ∨
    Identification before after

private theorem transGen_head
    (first : Primitive source middle)
    (rest : Relation.TransGen Primitive middle target) :
    Relation.TransGen Primitive source target := by
  induction rest with
  | single last => exact .tail (.single first) last
  | tail prior last induction => exact .tail induction last

private theorem closure_head
    (first : Primitive source middle)
    (rest : middle = target ∨
      Relation.TransGen Primitive middle target) :
    source = target ∨ Relation.TransGen Primitive source target := by
  rcases rest with equality | rest
  · subst target
    exact Or.inr (.single first)
  · exact Or.inr (transGen_head first rest)

private theorem closure_trans
    (first : source = middle ∨
      Relation.TransGen Primitive source middle)
    (second : middle = target ∨
      Relation.TransGen Primitive middle target) :
    source = target ∨ Relation.TransGen Primitive source target := by
  rcases first with firstEquality | firstSteps
  · subst middle
    exact second
  · rcases second with secondEquality | secondSteps
    · subst target
      exact Or.inr firstSteps
    · exact Or.inr (firstSteps.trans secondSteps)

namespace ExtraPins

/-- Convert the independently stored finite unary-end topology into the exact
pin chain.  Each descendant occurrence is derived by `rawPin`; no primitive
relation evidence occurs in `ExtraPins` or `Valid`. -/
noncomputable def Valid.toPrimitives
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {startItems finalItems : ItemSeq (outer ++ locals)}
    {pins : ExtraPins wire startItems finalItems}
    (valid : Valid (wire := wire) interface context locals pins)
    (sourceCanonical : (context.fill (.mk locals startItems)).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals startItems))) :
    let source := interface.withBody
      (context.fill (.mk locals startItems))
      sourceCanonical sourceExternalTwoEnded
    let target := endpoint valid sourceCanonical sourceExternalTwoEnded
    source = target ∨ Relation.TransGen Primitive source target := by
  induction valid with
  | done => exact Or.inl rfl
  | @add items finalItems home tail targetCanonical
      targetExternalTwoEnded tailValid induction =>
      let firstRaw := rawPin
        (sourceCanonical := sourceCanonical)
        (sourceExternalTwoEnded := sourceExternalTwoEnded)
        (OpenDiagramIso.refl _) home targetCanonical targetExternalTwoEnded
      let first : Primitive
          (interface.withBody (context.fill (.mk locals items))
            sourceCanonical sourceExternalTwoEnded)
          (interface.withBody (context.fill (.mk locals home.result))
            targetCanonical targetExternalTwoEnded) :=
        Or.inl firstRaw.toVacuity
      exact closure_head first
        (induction targetCanonical targetExternalTwoEnded)

/-- The nonempty form transports the exact first occurrence from an arbitrary
isomorphic source, then continues structurally through the remaining homes. -/
noncomputable def addToPrimitives
    {boundary : List Sig} {interface : OpenDiagram boundary}
    {source : OpenDiagram boundary}
    {outer locals : List Sig}
    {context : DiagramContext interface.external outer}
    {signature : Sig} {wire : Var (outer ++ locals) signature}
    {items finalItems : ItemSeq (outer ++ locals)}
    (sourceCanonical : (context.fill (.mk locals items)).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals items)))
    (sourceIso : OpenDiagramIso source
      (interface.withBody (context.fill (.mk locals items))
        sourceCanonical sourceExternalTwoEnded))
    (home : Vacuity.Stub.Far wire items)
    (tail : ExtraPins wire home.result finalItems)
    (targetCanonical : (context.fill (.mk locals home.result)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals home.result)))
    (tailValid : Valid interface context locals tail) :
    let targetValid : Valid interface context locals
      (ExtraPins.add home tail) :=
        .add targetCanonical targetExternalTwoEnded tailValid
    source = endpoint targetValid sourceCanonical sourceExternalTwoEnded ∨
      Relation.TransGen Primitive source
        (endpoint targetValid sourceCanonical sourceExternalTwoEnded) := by
  let firstRaw := rawPin sourceIso home targetCanonical
    targetExternalTwoEnded
  let first : Primitive source
      (interface.withBody (context.fill (.mk locals home.result))
        targetCanonical targetExternalTwoEnded) :=
    Or.inl firstRaw.toVacuity
  exact closure_head first
    (tailValid.toPrimitives targetCanonical targetExternalTwoEnded)

end ExtraPins

namespace RawBare

noncomputable def isolatedToPrimitives
    (raw : RawIsolatedPoint before) :
    before = raw.target ∨
      Relation.TransGen Primitive before raw.target := by
  let point : RawPoint before raw.target := {
    outer := raw.outer
    locals := raw.locals
    items := raw.items
    signature := raw.signature
    endpoint := {
      occurrence := {
        interface := raw.interface
        context := raw.context
        sourceCanonical := raw.sourceCanonical
        sourceExternalTwoEnded := raw.sourceExternalTwoEnded
        host_iso := raw.sourceIso
      }
      targetCanonical := raw.targetCanonical
      targetExternalTwoEnded := raw.targetExternalTwoEnded
      targetIso := OpenDiagramIso.refl raw.target
    }
  }
  exact Or.inr (.single (Or.inl point.toVacuity))

noncomputable def freshStubToPrimitives
    (raw : RawFreshStub before) :
    before = raw.target ∨
      Relation.TransGen Primitive before raw.target := by
  let pointTarget := raw.interface.withBody
    (raw.context.fill
      (Vacuity.Point.present raw.hostLocals raw.items raw.signature))
    raw.pointCanonical raw.pointExternalTwoEnded
  let stubTarget := raw.interface.withBody
    (raw.context.fill (Vacuity.Stub.present raw.hostLocals raw.items .nil
      raw.signature 0 Fin.elim0 0 raw.far))
    raw.stubCanonical raw.stubExternalTwoEnded
  let point : RawPoint before pointTarget := {
    outer := raw.outer
    locals := raw.hostLocals
    items := raw.items
    signature := raw.signature
    endpoint := {
      occurrence := {
        interface := raw.interface
        context := raw.context
        sourceCanonical := raw.sourceCanonical
        sourceExternalTwoEnded := raw.sourceExternalTwoEnded
        host_iso := raw.sourceIso
      }
      targetCanonical := raw.pointCanonical
      targetExternalTwoEnded := raw.pointExternalTwoEnded
      targetIso := OpenDiagramIso.refl pointTarget
    }
  }
  let stub : RawStub pointTarget stubTarget := {
    outer := raw.outer
    hostLocals := raw.hostLocals
    leading := raw.items
    trailing := .nil
    signature := raw.signature
    arity := 0
    ports := Fin.elim0
    position := 0
    far := raw.far
    endpoint := {
      occurrence := {
        interface := raw.interface
        context := raw.context
        sourceCanonical := by
          simpa [Vacuity.Point.present, Vacuity.Stub.plain] using
            raw.pointCanonical
        sourceExternalTwoEnded := by
          intro wireSignature selected
          exact raw.pointExternalTwoEnded selected
        host_iso := by
          simpa [pointTarget, Vacuity.Point.present, Vacuity.Stub.plain] using
            (OpenDiagramIso.refl pointTarget)
      }
      targetCanonical := raw.stubCanonical
      targetExternalTwoEnded := raw.stubExternalTwoEnded
      targetIso := OpenDiagramIso.refl stubTarget
    }
  }
  let pins := raw.pinsValid.toPrimitives raw.stubCanonical
    raw.stubExternalTwoEnded
  let pointStep : Primitive before pointTarget := Or.inl point.toVacuity
  let stubStep : Primitive pointTarget stubTarget := Or.inl stub.toVacuity
  exact closure_head pointStep (closure_head stubStep pins)

noncomputable def attachedStubToPrimitives
    (raw : RawAttachedStub before) :
    before = raw.target ∨
      Relation.TransGen Primitive before raw.target := by
  let stubTarget := raw.interface.withBody
    (raw.context.fill (Vacuity.Stub.present raw.hostLocals raw.leading
      raw.trailing raw.signature raw.arity raw.ports raw.position raw.far))
    raw.stubCanonical raw.stubExternalTwoEnded
  let stub : RawStub before stubTarget := {
    outer := raw.outer
    hostLocals := raw.hostLocals
    leading := raw.leading
    trailing := raw.trailing
    signature := raw.signature
    arity := raw.arity
    ports := raw.ports
    position := raw.position
    far := raw.far
    endpoint := {
      occurrence := {
        interface := raw.interface
        context := raw.context
        sourceCanonical := raw.sourceCanonical
        sourceExternalTwoEnded := raw.sourceExternalTwoEnded
        host_iso := raw.sourceIso
      }
      targetCanonical := raw.stubCanonical
      targetExternalTwoEnded := raw.stubExternalTwoEnded
      targetIso := OpenDiagramIso.refl stubTarget
    }
  }
  let pins := raw.pinsValid.toPrimitives raw.stubCanonical
    raw.stubExternalTwoEnded
  exact closure_head (Or.inl stub.toVacuity) pins

noncomputable def pinBatchToPrimitives
    (raw : RawPinBatch before) :
    before = raw.target ∨
      Relation.TransGen Primitive before raw.target := by
  exact ExtraPins.addToPrimitives raw.sourceCanonical
    raw.sourceExternalTwoEnded raw.sourceIso raw.first raw.tail
    raw.firstTargetCanonical raw.firstTargetExternalTwoEnded raw.tailValid

noncomputable def toPrimitives
    (raw : RawBare before after) :
    before = after ∨ Relation.TransGen Primitive before after := by
  cases raw with
  | isolated raw => exact isolatedToPrimitives raw
  | freshStub raw => exact freshStubToPrimitives raw
  | attachedStub raw => exact attachedStubToPrimitives raw
  | pinBatch raw => exact pinBatchToPrimitives raw

end RawBare

/-! ## Accepting fixpoint trace

The constructors are the accepting absorption run read backwards.  Bare and
equated reconstruction strictly add complement syntax.  Presentation changes
only the physical arrangement of already-accounted-for identity incidences.
-/

inductive AbsorptionTrace (source : OpenDiagram boundary) :
    {current : OpenDiagram boundary} → OpenAddition source current → Type
  | empty : AbsorptionTrace source (OpenAddition.refl source)
  | bare
      {before after : OpenDiagram boundary}
      {beforeGrowth : OpenAddition source before}
      (prior : AbsorptionTrace source beforeGrowth)
      (afterGrowth : OpenAddition source after)
      (strictGrowth : beforeGrowth.complementSize <
        afterGrowth.complementSize)
      (event : RawBare before after) :
      AbsorptionTrace source afterGrowth
  | equated
      {before after : OpenDiagram boundary}
      {beforeGrowth : OpenAddition source before}
      (prior : AbsorptionTrace source beforeGrowth)
      (afterGrowth : OpenAddition source after)
      (strictGrowth : beforeGrowth.complementSize <
        afterGrowth.complementSize)
      (event : RawEquated before after) :
      AbsorptionTrace source afterGrowth
  | present
      {before after : OpenDiagram boundary}
      {beforeGrowth : OpenAddition source before}
      (prior : AbsorptionTrace source beforeGrowth)
      (afterGrowth : OpenAddition source after)
      (sameComplement : beforeGrowth.complementSize =
        afterGrowth.complementSize)
      (event : RawPresentation before after) :
      AbsorptionTrace source afterGrowth

namespace AbsorptionTrace

noncomputable def toPrimitives
    {source current : OpenDiagram boundary}
    {growth : OpenAddition source current}
    (trace : AbsorptionTrace source growth) :
    source = current ∨ Relation.TransGen Primitive source current := by
  induction trace with
  | empty => exact Or.inl rfl
  | bare prior afterGrowth strictGrowth event induction =>
      exact closure_trans induction event.toPrimitives
  | equated prior afterGrowth strictGrowth event induction =>
      exact closure_trans induction
        (Or.inr (.single (Or.inr (Or.inr event.toIdentification))))
  | present prior afterGrowth sameComplement event induction =>
      exact closure_trans induction
        (Or.inr (.single (Or.inr (Or.inl event.toPresentation))))

end AbsorptionTrace

/-- The old generic assembly endpoint together with its successful proof-only
absorption fixpoint run.  `Nonempty` keeps acceptance proof-irrelevant while
the dependent witness remains erased `Type` data.  Recursive diagram syntax
remains the only syntax; `OpenAddition` only relates retained source
occurrences to their target occurrences and owns complement size. -/
def AcceptedVacuousAssembly
    (source insertion : OpenDiagram boundary) : Prop :=
  Nonempty (Σ growth : OpenAddition source insertion,
    AbsorptionTrace source growth)

/-- Every accepted generic vacuous assembly is reconstructed by the primitive
identity-family rules, up to the existing structural open-diagram isomorphism. -/
theorem AcceptedVacuousAssembly.decompose
    {boundary : List Sig}
    {source insertion : OpenDiagram boundary}
    (accepted : AcceptedVacuousAssembly source insertion) :
    ∃ endpoint : OpenDiagram boundary,
      (source = endpoint ∨
        Relation.TransGen Primitive source endpoint) ∧
      OpenDiagram.Isomorphic endpoint insertion := by
  rcases accepted with ⟨⟨growth, trace⟩⟩
  exact ⟨insertion, trace.toPrimitives,
    OpenDiagram.Isomorphic.refl insertion⟩

end VacuousAssembly

end VisualProof.Rule
