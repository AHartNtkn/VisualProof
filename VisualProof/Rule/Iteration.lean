import VisualProof.Diagram.NestedOccurrence
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Iteration

/-- A local copy may keep an inherited wire or allocate one fresh wire of the
same signature for a selected source wire. -/
structure WireFreshening
    (sourceWires targetWires freshWires : List Sig)
    (inherited : WireRenaming sourceWires targetWires) where
  sourceOfFresh : WireRenaming freshWires sourceWires
  sourceOfFresh_injective :
    ∀ {signature} {left right : Var freshWires signature},
      sourceOfFresh left = sourceOfFresh right → left = right
  wire : WireRenaming sourceWires (targetWires ++ freshWires)
  wire_fresh : ∀ {signature} (fresh : Var freshWires signature),
    wire (sourceOfFresh fresh) = Var.appendRight targetWires fresh
  wire_inherited : ∀ {signature} (source : Var sourceWires signature),
    (∀ fresh : Var freshWires signature, sourceOfFresh fresh ≠ source) →
      wire source = (inherited source).appendLeft freshWires

/-- The selected material after its inherited wires have been redirected and
its chosen wires have been freshened. -/
def freshenedSelected
    (selected : Region sourceWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : Region (targetWires ++ freshWires) :=
  selected.renameWires freshening.wire

/-- Direct identities that complete every newly allocated copy wire. The
primary batch handles every incidence set that is not already rooted with two
ends; the extra batch gives an empty incidence set its second distinct unary
pin. -/
def freshPins
    (selected : Region sourceWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : ItemSeq (targetWires ++ freshWires) :=
  let copied := freshenedSelected selected freshening
  let primary := ItemSeq.pinWires freshWires
    ⟨fun wire => Var.appendRight targetWires wire⟩
    (fun wire =>
      let paths := copied.incidencePaths
        (targetWires.length + wire.index.val)
      decide (¬RegionPath.RootedTwo paths))
  let extra := ItemSeq.pinWires freshWires
    ⟨fun wire => Var.appendRight targetWires wire⟩
    (fun wire => decide (copied.incidencePaths
      (targetWires.length + wire.index.val) = []))
  primary.append extra

/-- The independently scoped copied block before it is conjoined with the
descendant remainder. -/
def copyBlock
    (selected : Region sourceWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : Region targetWires :=
  Region.adjoinAt freshWires (freshPins selected freshening)
    (freshenedSelected selected freshening)

/-- Canonical iteration target: pinned copy followed by the remainder. -/
def copied
    (selected : Region sourceWires) (remainder : Region targetWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : Region targetWires :=
  (copyBlock selected freshening).conjoin remainder

/-- Direct inherited-wire identities required when removing the copy would
otherwise remove the descendant hole's last incidence of that wire. -/
def uncopyPins
    (selected : Region sourceWires) (remainder : Region targetWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : ItemSeq targetWires :=
  let removed := copyBlock selected freshening
  ItemSeq.pinWires targetWires WireRenaming.id
    (fun wire => decide
      (removed.incidencePaths wire.index.val ≠ [] ∧
        remainder.incidencePaths wire.index.val = []))

/-- Canonical deiteration target: the remainder plus exactly the inherited
wire residue needed to preserve the descendant hole interface. -/
def uncopyResidue
    (selected : Region sourceWires) (remainder : Region targetWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      inherited) : Region targetWires :=
  match remainder with
  | .mk locals items =>
      .mk locals
        (((uncopyPins selected remainder freshening).renameWires
          ⟨fun wire => wire.appendLeft locals⟩).append items)

/-- The two primitive local equivalences. Symmetry supplies their converse
directions without introducing a second rule presentation. -/
inductive Local
    (descendant : DiagramContext sourceWires targetWires)
    (selected : Region sourceWires) :
    Region targetWires → Region targetWires → Prop
  | copy
      (remainder : Region targetWires)
      (copyLocals : List Sig)
      (freshening : WireFreshening sourceWires targetWires copyLocals
        descendant.outerWire) :
      Local descendant selected remainder
        (copied selected remainder freshening)
  | remove
      (remainder : Region targetWires)
      (copyLocals : List Sig)
      (freshening : WireFreshening sourceWires targetWires copyLocals
        descendant.outerWire) :
      Local descendant selected
        (copied selected remainder freshening)
        (uncopyResidue selected remainder freshening)

end Iteration

/-- Iteration and deiteration at one exact selected ancestor and descendant
hole. Both endpoint bodies must be canonical recursive diagrams. -/
def Iteration : Rule :=
  fun {_boundary} source target =>
    ∃ (occurrence : NestedOccurrence source)
      (after : Region occurrence.descendantWires)
      (targetCanonical : (occurrence.targetBody after).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire (occurrence.targetBody after))
      (_targetIso : OpenDiagramIso target
        (occurrence.replace after targetCanonical targetExternalTwoEnded)),
      symmetric (Iteration.Local occurrence.descendant occurrence.selected)
        occurrence.before after

theorem Iteration.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Iteration source target)
    (targetIso : OpenDiagramIso target target') :
    Iteration source' target' := by
  rcases step with ⟨occurrence, after, targetCanonical,
    targetExternalTwoEnded, existingTargetIso, localEvidence⟩
  exact ⟨occurrence.transportSource sourceIso.symm, after,
    targetCanonical, targetExternalTwoEnded,
    targetIso.symm.trans existingTargetIso, localEvidence⟩

theorem Iteration.respectsTargetIso
    (step : Iteration source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Iteration source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Iteration.iso (OpenDiagramIso.refl source) step targetIso

theorem Iteration.backward_respectsTargetIso
    (step : Iteration target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Iteration target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Iteration.iso targetIso step (OpenDiagramIso.refl source)

theorem Iteration.symm (step : Iteration source target) :
    Iteration target source := by
  rcases step with ⟨occurrence, after, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : NestedOccurrence target := {
    ancestorWires := occurrence.ancestorWires
    anchorLocals := occurrence.anchorLocals
    descendantWires := occurrence.descendantWires
    selected := occurrence.selected
    before := after
    interface := occurrence.interface
    outer := occurrence.outer
    descendant := occurrence.descendant
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    source_iso := targetIso
  }
  exact ⟨reverseOccurrence, occurrence.before, occurrence.sourceCanonical,
    occurrence.sourceExternalTwoEnded, occurrence.source_iso,
    localEvidence.elim Or.inr Or.inl⟩

end VisualProof.Rule
