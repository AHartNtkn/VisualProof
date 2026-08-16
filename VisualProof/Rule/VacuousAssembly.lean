import VisualProof.Rule.Step

namespace VisualProof.Rule

open Diagram
open Theory

namespace VacuousAssembly

/-!
`AcceptedVacuousAssembly` is the proof-only statement of the former generic
assembly check.  It is deliberately not a rule and has no executable index.

The acceptance boundary contains only the mathematical input of that check:
an identity-only addition, its connected components and contacts, and a
successful absorption run.  In particular it contains no rule steps,
intermediate well-formed diagrams, or primitive applicability evidence.
-/

/-- A signature-preserving injection of the wires retained by an assembly
insertion. -/
structure WireEmbedding (source target : List Sig) where
  toRenaming : WireRenaming source target
  injective : ∀ {signature} (left right : Var source signature),
    toRenaming left = toRenaming right → left = right

instance : CoeFun (WireEmbedding source target)
    (fun _ => ∀ {signature}, Var source signature → Var target signature) :=
  ⟨fun embedding => fun {_signature} wire => embedding.toRenaming wire⟩

namespace WireEmbedding

/-- A target wire is new exactly when it is outside the retained image. -/
def Fresh (embedding : WireEmbedding source target)
    (wire : Var target signature) : Prop :=
  ∀ sourceWire : Var source signature, embedding sourceWire ≠ wire

end WireEmbedding

/-- Insertion of fresh-wire ports into a retained identity node.  Port
positions are storage only, so the retained positions form an arbitrary
injection; every other target position is a genuinely fresh assembly wire. -/
structure PortGrowth (embedding : WireEmbedding source target)
    {signature : Sig} {sourceArity targetArity : Nat}
    (sourcePorts : Fin sourceArity → Var source signature)
    (targetPorts : Fin targetArity → Var target signature) where
  retainedPosition : Fin sourceArity → Fin targetArity
  retainedPosition_injective : Function.Injective retainedPosition
  retainedPort : ∀ position,
    targetPorts (retainedPosition position) = embedding (sourcePorts position)
  addedFresh : ∀ targetPosition,
    (∀ sourcePosition, retainedPosition sourcePosition ≠ targetPosition) →
      embedding.Fresh (targetPorts targetPosition)

mutual
  /-- Exact recursive evidence that a region is obtained by adding local
  wires and identity apparatus only. -/
  inductive RegionAddition :
      {sourceOuter targetOuter : List Sig} →
      WireEmbedding sourceOuter targetOuter →
      Region sourceOuter → Region targetOuter → Type
    | mk
        {outer : WireEmbedding sourceOuter targetOuter}
        (locals : WireEmbedding sourceLocals targetLocals)
        (combined : WireEmbedding
          (sourceOuter ++ sourceLocals) (targetOuter ++ targetLocals))
        (mapsOuter : ∀ {signature} (wire : Var sourceOuter signature),
          combined (wire.appendLeft sourceLocals) =
            (outer wire).appendLeft targetLocals)
        (mapsLocal : ∀ {signature} (wire : Var sourceLocals signature),
          combined (Var.appendRight sourceOuter wire) =
            Var.appendRight targetOuter (locals wire))
        (items : ItemSeqAddition combined sourceItems targetItems) :
        RegionAddition outer
          (.mk sourceLocals sourceItems) (.mk targetLocals targetItems)

  /-- Exact identity-only addition on a recursive item sequence.  Atoms and
  cuts are retained structurally; identities may gain fresh-wire ports and
  new identity nodes may be interleaved anywhere. -/
  inductive ItemSeqAddition :
      {sourceWires targetWires : List Sig} →
      WireEmbedding sourceWires targetWires →
      ItemSeq sourceWires → ItemSeq targetWires → Type
    | nil : ItemSeqAddition embedding .nil .nil
    | atom
        (tail : ItemSeqAddition embedding sourceTail targetTail) :
        ItemSeqAddition embedding
          (.cons (.atom head ports) sourceTail)
          (.cons (.atom (embedding head)
            (ports.map (fun {_signature} wire =>
              embedding.toRenaming wire))) targetTail)
    | identity
        {signature : Sig} {sourceArity targetArity : Nat}
        {sourcePorts : Fin sourceArity → Var sourceWires signature}
        {targetPorts : Fin targetArity → Var targetWires signature}
        (ports : PortGrowth embedding sourcePorts targetPorts)
        (tail : ItemSeqAddition embedding sourceTail targetTail) :
        ItemSeqAddition embedding
          (.cons (.identity signature sourceArity sourcePorts) sourceTail)
          (.cons (.identity signature targetArity targetPorts) targetTail)
    | cut
        (body : RegionAddition embedding sourceBody targetBody)
        (tail : ItemSeqAddition embedding sourceTail targetTail) :
        ItemSeqAddition embedding
          (.cons (.cut sourceBody) sourceTail)
          (.cons (.cut targetBody) targetTail)
    | addIdentity
        (tail : ItemSeqAddition embedding sourceItems targetTail) :
        ItemSeqAddition embedding sourceItems
          (.cons (.identity signature arity ports) targetTail)
end

/-- One exact presentation of `source ∪ assembly = insertion`.  Both
endpoints use the ordinary recursive `OpenDiagram`; this object records only
which wires/items are retained and which identity apparatus is added. -/
structure OpenAddition
    (source insertion : OpenDiagram boundary) : Type where
  interface : OpenDiagram boundary
  sourceBody : Region interface.external
  insertionBody : Region interface.external
  sourceCanonical : sourceBody.Canonical
  insertionCanonical : insertionBody.Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire sourceBody
  insertionExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    interface.boundaryWire insertionBody
  sourceIso : OpenDiagramIso source
    (interface.withBody sourceBody sourceCanonical sourceExternalTwoEnded)
  insertionIso : OpenDiagramIso insertion
    (interface.withBody insertionBody insertionCanonical
      insertionExternalTwoEnded)
  retained : WireEmbedding interface.external interface.external
  retained_eq : ∀ {signature} (wire : Var interface.external signature),
    retained wire = wire
  body : RegionAddition retained sourceBody insertionBody

/-! The remaining objects state the original generic acceptance test.  They
are graph facts about the complement selected by `OpenAddition`, not a
recipe for constructing the insertion with rules. -/

/-- A proof-derived view of the fresh wires, identity incidences, and
existing-item contacts of one exact recursive addition.  Its carriers are
proof references into `RegionAddition`; the view carries no copied diagram
syntax. -/
structure ExactGraph (addition : OpenAddition source insertion) where
  Wire : Type
  Identity : Type
  ExistingItem : Type
  incident : Wire → Identity → Prop
  touchesWire : Wire → ExistingItem → Prop
  touchesIdentity : Identity → ExistingItem → Prop
  home : Identity → RegionPath

namespace ExactGraph

inductive Connected (graph : ExactGraph addition) :
    Sum graph.Wire graph.Identity →
      Sum graph.Wire graph.Identity → Prop
  | refl (cell) : Connected graph cell cell
  | incidence (wire) (identity) (edge : graph.incident wire identity) :
      Connected graph (.inl wire) (.inr identity)
  | symm (path : Connected graph left right) : Connected graph right left
  | trans (first : Connected graph left middle)
      (second : Connected graph middle right) : Connected graph left right

def Touches (graph : ExactGraph addition)
    (cell : Sum graph.Wire graph.Identity)
    (existing : graph.ExistingItem) : Prop :=
  match cell with
  | .inl wire => graph.touchesWire wire existing
  | .inr identity => graph.touchesIdentity identity existing

/-- The historical per-component condition, without any regional or
constructability strengthening. -/
def OneExistingItemPerComponent (graph : ExactGraph addition) : Prop :=
  ∀ {left right existingLeft existingRight},
    graph.Connected left right → graph.Touches left existingLeft →
      graph.Touches right existingRight → existingLeft = existingRight

/-- The mutable part of the historical absorption check: live assembly wires
and the current owner of every identity incidence after transfers. -/
structure AbsorptionState (graph : ExactGraph addition) where
  live : graph.Wire → Prop
  owner : graph.Identity → graph.Wire → Prop

/-- One literal fixpoint reduction.  `bare` removes an exclusive component
wire; `equated` absorbs through an incident identity and transfers its other
mentions to a live assembly survivor or the component's sole existing
contact. -/
inductive Absorbs (graph : ExactGraph addition) :
    AbsorptionState graph → AbsorptionState graph → Prop
  | bare
      (selected : graph.Wire)
      (selectedLive : before.live selected)
      (exclusive : ∀ identity,
        before.owner identity selected →
          (∀ other, before.owner identity other → other = selected) ∧
          ¬ ∃ existing, graph.touchesIdentity identity existing)
      (live_eq : ∀ wire, after.live wire ↔
        before.live wire ∧ wire ≠ selected)
      (owner_eq : ∀ identity wire,
        after.owner identity wire ↔
          before.owner identity wire ∧ wire ≠ selected) :
      Absorbs graph before after
  | equated
      (selected : graph.Wire)
      (home : graph.Identity)
      (selectedLive : before.live selected)
      (atHome : before.owner home selected)
      (survivor : Option graph.Wire)
      (survives : ∀ wire, survivor = some wire →
        before.live wire ∧ wire ≠ selected ∧
          before.owner home wire)
      (contact : survivor = none →
        ∃ existing, graph.touchesIdentity home existing)
      (belowHome : ∀ identity,
        before.owner identity selected → identity ≠ home →
          List.IsPrefix (graph.home home) (graph.home identity))
      (live_eq : ∀ wire, after.live wire ↔
        before.live wire ∧ wire ≠ selected)
      (owner_eq : ∀ identity wire,
        after.owner identity wire ↔
          (before.owner identity wire ∧ wire ≠ selected) ∨
          (∃ chosen, survivor = some chosen ∧ wire = chosen ∧
            identity ≠ home ∧ before.owner identity selected)) :
      Absorbs graph before after

inductive AbsorptionRun (graph : ExactGraph addition) :
    AbsorptionState graph → Prop
  | done (empty : ∀ wire, ¬ state.live wire) : AbsorptionRun graph state
  | step (next : AbsorptionState graph) (absorbs : Absorbs graph state next)
      (tail : AbsorptionRun graph next) : AbsorptionRun graph state

def InitialState (graph : ExactGraph addition) : AbsorptionState graph where
  live := fun _ => True
  owner := fun identity wire => graph.incident wire identity

end ExactGraph

/-- The original whole-assembly acceptance condition: exact identity-only
addition, at most one existing contact per connected component, and a
fixpoint run that eliminates every assembly wire. -/
structure AcceptanceCertificate
    (source insertion : OpenDiagram boundary) : Type 1 where
  addition : OpenAddition source insertion
  graph : ExactGraph addition
  oneContact : graph.OneExistingItemPerComponent
  absorbs : graph.AbsorptionRun graph.InitialState

def AcceptedVacuousAssembly
    (source insertion : OpenDiagram boundary) : Prop :=
  Nonempty (AcceptanceCertificate source insertion)

end VacuousAssembly

open VacuousAssembly

/-- Every assembly accepted by the original generic condition is obtainable,
up to open-diagram isomorphism, by a finite sequence of rules from the full
system. -/
theorem AcceptedVacuousAssembly.decompose
    {boundary : List Sig}
    {source insertion : OpenDiagram boundary}
    (accepted : AcceptedVacuousAssembly source insertion) :
    ∃ endpoint : OpenDiagram boundary,
      (source = endpoint ∨ Relation.TransGen Step source endpoint) ∧
      OpenDiagram.Isomorphic endpoint insertion := by
  sorry

end VisualProof.Rule
