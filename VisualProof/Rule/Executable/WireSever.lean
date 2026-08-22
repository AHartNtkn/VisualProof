import VisualProof.Rule.WireSever
import VisualProof.Rule.Executable.WirePrimitive.Uniform

namespace VisualProof.Rule.WireSever

open Theory
open Diagram

private def mapBoundary (boundaryWire : Vars source boundary)
    (rename : WireRenaming source target) : Vars target boundary :=
  boundaryWire.map (fun wire => rename wire)

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

private theorem Vars.map_id_wire (variables : Vars context signatures) :
    variables.map (fun wire => WireRenaming.id wire) = variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons head) induction

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

private theorem WireRenaming.index_eq_of_index_eq
    (rename : WireRenaming source target)
    (left : Var source leftSignature) (right : Var source rightSignature)
    (indexEq : left.index.val = right.index.val) :
    (rename left).index.val = (rename right).index.val := by
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there right =>
          simp only [Var.index, Fin.val_zero, Fin.val_succ] at indexEq
          omega
  | there left induction =>
      cases right with
      | here =>
          simp only [Var.index, Fin.val_zero, Fin.val_succ] at indexEq
          omega
      | there right =>
          apply induction
            (⟨fun wire => rename (.there wire)⟩ : WireRenaming _ target) right
          simp only [Var.index, Fin.val_succ] at indexEq
          omega

private theorem presentedBoundary_surjective
    (diagram : OpenDiagram boundary)
    (external : WireEquiv diagram.external represented) :
    ∀ wire : Fin represented.length,
      ∃ position : Fin boundary.length,
        ((mapBoundary diagram.boundaryWire external.toRenaming).get position).index =
          wire := by
  intro representedIndex
  let representedWire := Var.ofIndex representedIndex
  let actualWire := external.symm representedWire
  obtain ⟨position, found⟩ := diagram.boundarySurjective actualWire.index
  refine ⟨position, ?_⟩
  simp only [mapBoundary]
  rw [Vars.get_map_wire]
  apply Fin.ext
  calc
    (external (diagram.boundaryWire.get position)).index.val =
        (external actualWire).index.val :=
      WireRenaming.index_eq_of_index_eq external.toRenaming _ _
        (congrArg Fin.val found)
    _ = representedWire.index.val := by rw [WireEquiv.apply_symm_apply]
    _ = representedIndex.val := by simp only [representedWire, Var.index_ofIndex]

private structure LocalDescription (wires : List Sig) where
  localWires : List Sig
  signature : Sig
  joined : Var (wires ++ localWires) signature
  joinedItems : ItemSeq (wires ++ localWires)
  partition : ItemSeq.PortPartition
    (collapseLocal wires localWires joined) joinedItems

private def LocalDescription.source
    (description : LocalDescription wires) : Region wires :=
  .mk description.localWires description.joinedItems

private def LocalDescription.target
    (description : LocalDescription wires) : Region wires :=
  separateLocal description.joined
    (description.joinedItems.partitionOutput
      (collapseLocal wires description.localWires description.joined)
      description.partition)

private def localFamily : WirePrimitive.Executable.Family where
  Description := LocalDescription
  source := LocalDescription.source
  target := LocalDescription.target

private theorem local_build {wires : List Sig}
    (description : LocalDescription wires) :
    Local description.source description.target :=
  .sever description.joined description.joinedItems description.partition

private theorem local_view {wires : List Sig} {before after : Region wires}
    (step : Local before after) :
    ∃ description : LocalDescription wires,
      before = description.source ∧ after = description.target := by
  cases step with
  | sever joined joinedItems partition =>
      exact ⟨⟨_, _, joined, joinedItems, partition⟩, rfl, rfl⟩

private def severCandidate (sourceWires : List Sig) (signature : Sig)
    (sourceBody : Region sourceWires)
    (separateBoundary : Vars (sourceWires ++ [signature]) boundary)
    (collapse : WireRenaming (sourceWires ++ [signature]) sourceWires)
    (partition : Region.PortPartition collapse sourceBody) :
    OpenDiagram.Candidate boundary where
  external := sourceWires ++ [signature]
  boundaryWire := separateBoundary
  body := sourceBody.partitionOutput collapse partition

private def joinCandidate (source : OpenDiagram boundary)
    (joinedWires : List Sig) (signature : Sig)
    (sourceExternal : WireEquiv source.external (joinedWires ++ [signature]))
    (rawBody : Region (joinedWires ++ [signature]))
    (collapse : WireRenaming (joinedWires ++ [signature]) joinedWires) :
    OpenDiagram.Candidate boundary where
  external := joinedWires
  boundaryWire := mapBoundary source.boundaryWire
    (WireRenaming.comp collapse sourceExternal.toRenaming)
  body := rawBody.renameWires collapse

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | contextual
      (index : WirePrimitive.Executable.ComputedDirected.Index
        localFamily source) : ForwardIndex source
  | openSever
      (sourceWires : List Sig)
      (signature : Sig)
      (sourceExternal : WireEquiv source.external sourceWires)
      (sourceBody : Region sourceWires)
      (source_body : RegionIso sourceExternal source.body sourceBody)
      (sourceCanonical : sourceBody.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        (mapBoundary source.boundaryWire sourceExternal.toRenaming) sourceBody)
      (separateBoundary : Vars (sourceWires ++ [signature]) boundary)
      (collapse : WireRenaming (sourceWires ++ [signature]) sourceWires)
      (collapseSurjective : ∀ {wireSignature}
        (wire : Var sourceWires wireSignature),
        ∃ targetWire : Var (sourceWires ++ [signature]) wireSignature,
          collapse targetWire = wire)
      (boundaryEq : ∀ position : Fin boundary.length,
        collapse (separateBoundary.get position) =
          sourceExternal (source.boundaryWire.get position))
      (partition : Region.PortPartition collapse sourceBody) :
      ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | contextual
      (index : WirePrimitive.Executable.ComputedDirected.Index
        localFamily source) : BackwardIndex source
  | openJoin
      (joinedWires : List Sig)
      (signature : Sig)
      (sourceExternal : WireEquiv source.external
        (joinedWires ++ [signature]))
      (rawBody : Region (joinedWires ++ [signature]))
      (source_body : RegionIso sourceExternal source.body rawBody)
      (sourceCanonical : rawBody.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        (mapBoundary source.boundaryWire sourceExternal.toRenaming) rawBody)
      (collapse : WireRenaming (joinedWires ++ [signature]) joinedWires)
      (collapseSurjective : ∀ {wireSignature}
        (wire : Var joinedWires wireSignature),
        ∃ sourceWire : Var (joinedWires ++ [signature]) wireSignature,
          collapse sourceWire = wire) :
      BackwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .contextual index =>
      WirePrimitive.Executable.ComputedDirected.runForward source index
  | .openSever sourceWires signature _ sourceBody _ _ _ separateBoundary
      collapse _ _ partition =>
      (severCandidate sourceWires signature sourceBody separateBoundary
        collapse partition).validate

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary)
  | .contextual index =>
      WirePrimitive.Executable.ComputedDirected.runBackward source index
  | .openJoin joinedWires signature sourceExternal rawBody _ _ _ collapse _ =>
      (joinCandidate source joinedWires signature sourceExternal rawBody
        collapse).validate

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WireSever source target := by
  constructor
  · rintro ⟨index, output, computed, isomorphic⟩
    cases index with
    | contextual localIndex =>
        apply Or.inl
        exact (WirePrimitive.Executable.ComputedDirected.forward_exact
          localFamily Local local_build local_view source target).mp
            ⟨localIndex, output, computed, isomorphic⟩
    | openSever sourceWires signature sourceExternal sourceBody source_body
        sourceCanonical sourceExternalTwoEnded separateBoundary collapse
        collapseSurjective boundaryEq partition =>
        let candidate := severCandidate sourceWires signature sourceBody
          separateBoundary collapse partition
        obtain ⟨valid, rfl⟩ :=
          (OpenDiagram.Candidate.validate_eq_some_iff candidate output).mp computed
        apply respectsTargetIso (target' := target) ?_ isomorphic
        exact Or.inr ⟨{
          sourceWires := sourceWires
          signature := signature
          sourceExternal := sourceExternal
          targetExternal := WireEquiv.refl _
          sourceBody := sourceBody
          source_body := source_body
          sourceCanonical := sourceCanonical
          sourceExternalTwoEnded := sourceExternalTwoEnded
          collapse := collapse
          collapse_surjective := collapseSurjective
          boundary := by
            intro position
            simpa only [candidate, severCandidate,
              OpenDiagram.Candidate.toOpen] using boundaryEq position
          partition := partition
          target_body := RegionIso.refl _
          targetCanonical := valid.2.1
          targetExternalTwoEnded := by
            have computedTwoEnded : OpenDiagram.ExternalTwoEnded
                separateBoundary
                (sourceBody.partitionOutput collapse partition) := by
              intro wireSignature wire
              simpa only [candidate, severCandidate] using valid.2.2 wire
            change OpenDiagram.ExternalTwoEnded
              (mapBoundary separateBoundary WireRenaming.id)
              (sourceBody.partitionOutput collapse partition)
            intro wireSignature wire
            simpa only [mapBoundary, Vars.map_id_wire] using
              computedTwoEnded wire
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · obtain ⟨localIndex, output, computed, isomorphic⟩ :=
        (WirePrimitive.Executable.ComputedDirected.forward_exact
          localFamily Local local_build local_view source target).mpr localStep
      exact ⟨.contextual localIndex, output, computed, isomorphic⟩
    · rcases openNonempty with ⟨openStep⟩
      let separateBoundary := mapBoundary target.boundaryWire
        openStep.targetExternal.toRenaming
      let candidate := severCandidate openStep.sourceWires openStep.signature
        openStep.sourceBody separateBoundary openStep.collapse
        openStep.partition
      have valid : candidate.Valid := by
        refine ⟨presentedBoundary_surjective target openStep.targetExternal,
          openStep.targetCanonical, ?_⟩
        exact openStep.targetExternalTwoEnded
      refine ⟨.openSever openStep.sourceWires openStep.signature
        openStep.sourceExternal openStep.sourceBody openStep.source_body
        openStep.sourceCanonical openStep.sourceExternalTwoEnded
        separateBoundary openStep.collapse openStep.collapse_surjective ?_
        openStep.partition, candidate.toOpen valid, ?_, ⟨?_⟩⟩
      · intro position
        simp only [separateBoundary, mapBoundary]
        rw [Vars.get_map_wire]
        exact openStep.boundary position
      · exact OpenDiagram.Candidate.validate_of_valid candidate valid
      · exact {
          external := openStep.targetExternal.symm
          boundary_eq := by
            intro position
            simp only [candidate, severCandidate,
              OpenDiagram.Candidate.toOpen, separateBoundary, mapBoundary]
            rw [Vars.get_map_wire]
            exact openStep.targetExternal.left_inv _
          body := openStep.target_body.symm
        }

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      Rule.WireSever target source := by
  constructor
  · rintro ⟨index, output, computed, isomorphic⟩
    cases index with
    | contextual localIndex =>
        apply Or.inl
        exact (WirePrimitive.Executable.ComputedDirected.backward_exact
          localFamily Local local_build local_view source target).mp
            ⟨localIndex, output, computed, isomorphic⟩
    | openJoin joinedWires signature sourceExternal rawBody source_body
        sourceCanonical sourceExternalTwoEnded collapse collapseSurjective =>
        let candidate := joinCandidate source joinedWires signature
          sourceExternal rawBody collapse
        obtain ⟨valid, rfl⟩ :=
          (OpenDiagram.Candidate.validate_eq_some_iff candidate output).mp computed
        apply backward_respectsTargetIso (target' := target) ?_ isomorphic
        obtain ⟨partition, outputEq⟩ :=
          Region.exists_partition_of_renamed collapse rawBody
        exact Or.inr ⟨{
          sourceWires := joinedWires
          signature := signature
          sourceExternal := WireEquiv.refl _
          targetExternal := sourceExternal
          sourceBody := rawBody.renameWires collapse
          source_body := RegionIso.refl _
          sourceCanonical := valid.2.1
          sourceExternalTwoEnded := by
            have computedTwoEnded : OpenDiagram.ExternalTwoEnded
                (mapBoundary source.boundaryWire
                  (WireRenaming.comp collapse sourceExternal.toRenaming))
                (rawBody.renameWires collapse) := by
              intro wireSignature wire
              simpa only [candidate, joinCandidate] using valid.2.2 wire
            change OpenDiagram.ExternalTwoEnded
              (mapBoundary
                (mapBoundary source.boundaryWire
                  (WireRenaming.comp collapse sourceExternal.toRenaming))
                WireRenaming.id)
              (rawBody.renameWires collapse)
            intro wireSignature wire
            simpa only [mapBoundary, Vars.map_id_wire] using
              computedTwoEnded wire
          collapse := collapse
          collapse_surjective := collapseSurjective
          boundary := by
            intro position
            simp only [candidate, joinCandidate,
              OpenDiagram.Candidate.toOpen, mapBoundary]
            rw [Vars.get_map_wire]
            rfl
          partition := partition
          target_body := by
            rw [outputEq]
            exact source_body
          targetCanonical := by
            rw [outputEq]
            exact sourceCanonical
          targetExternalTwoEnded := by
            rw [outputEq]
            exact sourceExternalTwoEnded
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · obtain ⟨localIndex, output, computed, isomorphic⟩ :=
        (WirePrimitive.Executable.ComputedDirected.backward_exact
          localFamily Local local_build local_view source target).mpr localStep
      exact ⟨.contextual localIndex, output, computed, isomorphic⟩
    · rcases openNonempty with ⟨openStep⟩
      let separateBody := openStep.sourceBody.partitionOutput
        openStep.collapse openStep.partition
      let joinedBoundary := mapBoundary source.boundaryWire
        (WireRenaming.comp openStep.collapse
          openStep.targetExternal.toRenaming)
      let candidate := joinCandidate source openStep.sourceWires
        openStep.signature openStep.targetExternal separateBody
        openStep.collapse
      have bodyEq : separateBody.renameWires openStep.collapse =
          openStep.sourceBody :=
        Region.partitionOutput_renameWires _ _ _
      have boundaryEq : joinedBoundary =
          mapBoundary target.boundaryWire
            openStep.sourceExternal.toRenaming := by
        apply Vars.eq_of_get_eq_wire
        intro position
        simp only [joinedBoundary, mapBoundary]
        rw [Vars.get_map_wire, Vars.get_map_wire]
        exact openStep.boundary position
      have valid : candidate.Valid := by
        refine ⟨?_, ?_, ?_⟩
        · change ∀ wire : Fin openStep.sourceWires.length,
            ∃ position : Fin boundary.length,
              (joinedBoundary.get position).index = wire
          rw [boundaryEq]
          exact presentedBoundary_surjective target openStep.sourceExternal
        · change (separateBody.renameWires openStep.collapse).Canonical
          rw [bodyEq]
          exact openStep.sourceCanonical
        · change OpenDiagram.ExternalTwoEnded joinedBoundary
            (separateBody.renameWires openStep.collapse)
          rw [boundaryEq, bodyEq]
          exact openStep.sourceExternalTwoEnded
      refine ⟨.openJoin openStep.sourceWires openStep.signature
        openStep.targetExternal separateBody openStep.target_body
        openStep.targetCanonical openStep.targetExternalTwoEnded
        openStep.collapse openStep.collapse_surjective,
        candidate.toOpen valid, ?_, ⟨?_⟩⟩
      · exact OpenDiagram.Candidate.validate_of_valid candidate valid
      · exact {
          external := openStep.sourceExternal.symm
          boundary_eq := by
            intro position
            simp only [candidate, joinCandidate,
              OpenDiagram.Candidate.toOpen, mapBoundary]
            rw [Vars.get_map_wire]
            change openStep.sourceExternal.symm
                (openStep.collapse
                  (openStep.targetExternal
                    (source.boundaryWire.get position))) =
              target.boundaryWire.get position
            rw [openStep.boundary position]
            exact openStep.sourceExternal.left_inv _
          body := (RegionIso.ofEq bodyEq).trans openStep.source_body.symm
        }

end VisualProof.Rule.WireSever
