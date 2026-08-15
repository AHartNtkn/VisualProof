import VisualProof.Diagram.PortPartition
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace WireSever

private theorem Vars.get_map_wire
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (position : Fin signatures.length) :
    (variables.map (fun wire => rename wire)).get position =
      rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun index => induction index) position

private theorem Vars.eq_of_get_eq_wire
    (left right : Vars context signatures)
    (getEq : ∀ position, left.get position = right.get position) :
    left = right := by
  induction signatures with
  | nil => cases left; cases right; rfl
  | cons signature rest induction =>
      cases left with
      | cons leftHead leftTail =>
          cases right with
          | cons rightHead rightTail =>
              have headEq : leftHead = rightHead := getEq 0
              have tailEq : leftTail = rightTail := by
                apply induction
                intro position
                exact getEq position.succ
              rw [headEq, tailEq]

private def presentedBoundary (diagram : OpenDiagram boundary)
    (external : WireEquiv diagram.external represented) :
    Vars represented boundary :=
  diagram.boundaryWire.map (fun wire => external wire)

private theorem presentedBoundary_iso (iso : OpenDiagramIso source target)
    (external : WireEquiv source.external represented) :
    presentedBoundary target (iso.external.symm.trans external) =
      presentedBoundary source external := by
  apply Vars.eq_of_get_eq_wire
  intro position
  simp only [presentedBoundary]
  rw [Vars.get_map_wire, Vars.get_map_wire]
  change external (iso.external.symm (target.boundaryWire.get position)) =
    external (source.boundaryWire.get position)
  rw [← iso.boundary_eq position, WireEquiv.symm_apply_apply]

def collapseLocal
    (wires localWires : List Sig)
    (joined : Var (wires ++ localWires) signature) :
    WireRenaming (wires ++ (localWires ++ [signature]))
      (wires ++ localWires) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft localWires)
    (Var.appendMap
      (fun wire => Var.appendRight wires wire)
      (fun {wireSignature} (wire : Var [signature] wireSignature) =>
        match wire with
        | .here => joined))⟩

@[simp] theorem collapseLocal_inherited
    (joined : Var (wires ++ localWires) signature)
    (wire : Var wires inheritedSignature) :
    collapseLocal wires localWires joined
        (wire.appendLeft (localWires ++ [signature])) =
      wire.appendLeft localWires := by
  simp [collapseLocal]

@[simp] theorem collapseLocal_local
    (joined : Var (wires ++ localWires) signature)
    (wire : Var localWires localSignature) :
    collapseLocal wires localWires joined
        (Var.appendRight wires (wire.appendLeft [signature])) =
      Var.appendRight wires wire := by
  simp [collapseLocal]

@[simp] theorem collapseLocal_last
    (joined : Var (wires ++ localWires) signature) :
    collapseLocal wires localWires joined
        (Var.appendRight wires (Var.appendRight localWires (.here :
          Var [signature] signature))) = joined := by
  simp [collapseLocal]

private def inheritedTarget : WireRenaming wires
    (wires ++ (localWires ++ [signature])) :=
  ⟨fun wire => wire.appendLeft (localWires ++ [signature])⟩

private def localTarget : WireRenaming (localWires ++ [signature])
    (wires ++ (localWires ++ [signature])) :=
  ⟨fun wire => Var.appendRight wires wire⟩

def localCompletion
    (joined : Var (wires ++ localWires) signature)
    (raw : ItemSeq (wires ++ (localWires ++ [signature]))) :
    ItemSeq (wires ++ (localWires ++ [signature])) :=
  let collapse := collapseLocal wires localWires joined
  let inheritedPins := ItemSeq.pinWires wires inheritedTarget
    (fun inherited => decide
      ((raw.renameWires collapse).incidencePaths inherited.index.val 0 ≠ [] ∧
        raw.incidencePaths inherited.index.val 0 = []))
  inheritedPins.append (ItemSeq.rootedTwoPins (localWires ++ [signature])
    localTarget (fun wire =>
      raw.incidencePaths (wires.length + wire.index.val) 0))

def completeLocal
    (joined : Var (wires ++ localWires) signature)
    (raw : ItemSeq (wires ++ (localWires ++ [signature]))) : Region wires :=
  .mk (localWires ++ [signature]) (raw.append (localCompletion joined raw))

private def externalTarget (external locals : List Sig) :
    WireRenaming external (external ++ locals) :=
  ⟨fun wire => wire.appendLeft locals⟩

def openCompletion (boundaryWire : Vars external boundary)
    (raw : Region external) : ItemSeq (external ++ raw.locals) :=
  ItemSeq.rootedTwoPins external (externalTarget external raw.locals)
    (fun wire => List.replicate (boundaryWire.countIndex wire.index.val) [] ++
      raw.incidencePaths wire.index.val)

def completeOpen (boundaryWire : Vars external boundary)
    (raw : Region external) : Region external :=
  match raw with
  | .mk locals items =>
      .mk locals (items.append (openCompletion boundaryWire (.mk locals items)))

inductive Local : LocalRule
  | sever
      (joined : Var (wires ++ localWires) signature)
      (joinedItems : ItemSeq (wires ++ localWires))
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems) :
      Local
        (.mk localWires joinedItems)
        (completeLocal joined (joinedItems.partitionOutput
          (collapseLocal wires localWires joined) partition))

/-- An open sever step expressed through exact typed presentations of both
external-wire contexts. The target presentation is the source presentation
with one wire of the selected signature appended. -/
structure Open
    (source target : OpenDiagram boundary) where
  sourceWires : List Sig
  signature : Sig
  sourceExternal : WireEquiv source.external sourceWires
  targetExternal : WireEquiv target.external (sourceWires ++ [signature])
  sourceBody : Region sourceWires
  source_body : RegionIso sourceExternal source.body sourceBody
  sourceCanonical : sourceBody.Canonical
  sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    (presentedBoundary source sourceExternal) sourceBody
  collapse : WireRenaming (sourceWires ++ [signature]) sourceWires
  collapse_surjective : ∀ {wireSignature} (wire : Var sourceWires wireSignature),
    ∃ targetWire : Var (sourceWires ++ [signature]) wireSignature,
      collapse targetWire = wire
  boundary : ∀ position : Fin boundary.length,
    collapse (targetExternal (target.boundaryWire.get position)) =
      sourceExternal (source.boundaryWire.get position)
  partition : Region.PortPartition collapse sourceBody
  target_body : RegionIso targetExternal target.body
    (completeOpen (presentedBoundary target targetExternal)
      (sourceBody.partitionOutput collapse partition))
  targetCanonical : (completeOpen (presentedBoundary target targetExternal)
    (sourceBody.partitionOutput collapse partition)).Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    (presentedBoundary target targetExternal)
    (completeOpen (presentedBoundary target targetExternal)
      (sourceBody.partitionOutput collapse partition))

noncomputable def Open.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Open source target)
    (targetIso : OpenDiagramIso target target') :
    Open source' target' := by
  refine {
    sourceWires := step.sourceWires
    signature := step.signature
    sourceExternal := sourceIso.external.symm.trans step.sourceExternal
    targetExternal := targetIso.external.symm.trans step.targetExternal
    sourceBody := step.sourceBody
    source_body := sourceIso.body.symm.trans step.source_body
    sourceCanonical := step.sourceCanonical
    sourceExternalTwoEnded := ?_
    collapse := step.collapse
    collapse_surjective := step.collapse_surjective
    boundary := ?_
    partition := step.partition
    target_body := ?_
    targetCanonical := ?_
    targetExternalTwoEnded := ?_
  }
  · rw [presentedBoundary_iso sourceIso step.sourceExternal]
    intro signature wire
    exact step.sourceExternalTwoEnded wire
  · intro position
    change step.collapse
        (step.targetExternal
          (targetIso.external.symm (target'.boundaryWire.get position))) =
      step.sourceExternal
        (sourceIso.external.symm (source'.boundaryWire.get position))
    rw [← targetIso.boundary_eq position, WireEquiv.symm_apply_apply,
      ← sourceIso.boundary_eq position, WireEquiv.symm_apply_apply]
    exact step.boundary position
  · rw [presentedBoundary_iso targetIso step.targetExternal]
    exact targetIso.body.symm.trans step.target_body
  · rw [presentedBoundary_iso targetIso step.targetExternal]
    exact step.targetCanonical
  · rw [presentedBoundary_iso targetIso step.targetExternal]
    intro signature wire
    exact step.targetExternalTwoEnded wire

end WireSever

def WireSever : Rule :=
  fun source target =>
    Contextual WireSever.Local source target ∨
      Nonempty (WireSever.Open source target)

theorem WireSever.iso
    (sourceIso : OpenDiagramIso source source')
    (step : WireSever source target)
    (targetIso : OpenDiagramIso target target') :
    WireSever source' target' := by
  cases step with
  | inl localStep =>
      exact Or.inl (Contextual.iso sourceIso localStep targetIso)
  | inr openNonempty =>
      rcases openNonempty with ⟨openStep⟩
      exact Or.inr ⟨WireSever.Open.iso sourceIso openStep targetIso⟩

theorem WireSever.respectsTargetIso
    (step : WireSever source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    WireSever source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact WireSever.iso (OpenDiagramIso.refl source) step targetIso

theorem WireSever.backward_respectsTargetIso
    (step : WireSever target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    WireSever target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact WireSever.iso targetIso step (OpenDiagramIso.refl source)

end VisualProof.Rule
