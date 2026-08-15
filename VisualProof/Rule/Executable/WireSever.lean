import VisualProof.Rule.WireSever

namespace VisualProof.Rule.WireSever

open Theory
open Diagram

private noncomputable def regionIsoOfEq
    {left right : Region wires} (equality : left = right) :
    RegionIso (WireEquiv.refl wires) left right := by
  subst right
  exact RegionIso.refl left

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
            (⟨fun wire => rename (.there wire)⟩ :
              WireRenaming _ target) right
          simp only [Var.index, Fin.val_succ] at indexEq
          omega

inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | localSever
      (joined : Var (wires ++ localWires) signature)
      (joinedItems : ItemSeq (wires ++ localWires))
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems)
      (occurrence : Occurrence (.mk localWires joinedItems) source)
      (polarity : occurrence.context.polarity = .positive)
      (targetCanonical : (occurrence.context.fill
        (completeLocal joined (joinedItems.partitionOutput
          (collapseLocal wires localWires joined) partition))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (completeLocal joined (joinedItems.partitionOutput
            (collapseLocal wires localWires joined) partition)))) :
      ForwardIndex source
  | localJoin
      (joined : Var (wires ++ localWires) signature)
      (raw : ItemSeq (wires ++ (localWires ++ [signature])))
      (occurrence : Occurrence
        (completeLocal joined raw) source)
      (polarity : occurrence.context.polarity = .negative)
      (targetCanonical : (occurrence.context.fill
        (.mk localWires (raw.renameWires
          (collapseLocal wires localWires joined)))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (.mk localWires (raw.renameWires
            (collapseLocal wires localWires joined))))) :
      ForwardIndex source
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
      (separateBoundarySurjective : ∀ wire : Fin (sourceWires ++ [signature]).length,
        ∃ position : Fin boundary.length,
          (separateBoundary.get position).index = wire)
      (collapse : WireRenaming (sourceWires ++ [signature]) sourceWires)
      (collapseSurjective : ∀ {wireSignature}
        (wire : Var sourceWires wireSignature),
        ∃ targetWire : Var (sourceWires ++ [signature]) wireSignature,
          collapse targetWire = wire)
      (boundaryEq : ∀ position : Fin boundary.length,
        collapse (separateBoundary.get position) =
          sourceExternal (source.boundaryWire.get position))
      (partition : Region.PortPartition collapse sourceBody)
      (targetCanonical : (completeOpen separateBoundary
        (sourceBody.partitionOutput collapse partition)).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        separateBoundary (completeOpen separateBoundary
          (sourceBody.partitionOutput collapse partition))) :
      ForwardIndex source

inductive BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | localJoin
      (joined : Var (wires ++ localWires) signature)
      (raw : ItemSeq (wires ++ (localWires ++ [signature])))
      (occurrence : Occurrence
        (completeLocal joined raw) source)
      (polarity : occurrence.context.polarity = .positive)
      (targetCanonical : (occurrence.context.fill
        (.mk localWires (raw.renameWires
          (collapseLocal wires localWires joined)))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (.mk localWires (raw.renameWires
            (collapseLocal wires localWires joined))))) :
      BackwardIndex source
  | localSever
      (joined : Var (wires ++ localWires) signature)
      (joinedItems : ItemSeq (wires ++ localWires))
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems)
      (occurrence : Occurrence (.mk localWires joinedItems) source)
      (polarity : occurrence.context.polarity = .negative)
      (targetCanonical : (occurrence.context.fill
        (completeLocal joined (joinedItems.partitionOutput
          (collapseLocal wires localWires joined) partition))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (completeLocal joined (joinedItems.partitionOutput
            (collapseLocal wires localWires joined) partition)))) :
      BackwardIndex source
  | openJoin
      (joinedWires : List Sig)
      (signature : Sig)
      (sourceExternal : WireEquiv source.external
        (joinedWires ++ [signature]))
      (rawBody : Region (joinedWires ++ [signature]))
      (source_body : RegionIso sourceExternal source.body
        (completeOpen (mapBoundary source.boundaryWire
          sourceExternal.toRenaming) rawBody))
      (sourceCanonical : (completeOpen (mapBoundary source.boundaryWire
        sourceExternal.toRenaming) rawBody).Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        (mapBoundary source.boundaryWire sourceExternal.toRenaming)
        (completeOpen (mapBoundary source.boundaryWire
          sourceExternal.toRenaming) rawBody))
      (collapse : WireRenaming (joinedWires ++ [signature]) joinedWires)
      (collapseSurjective : ∀ {wireSignature}
        (wire : Var joinedWires wireSignature),
        ∃ sourceWire : Var (joinedWires ++ [signature]) wireSignature,
          collapse sourceWire = wire)
      (targetCanonical : (rawBody.renameWires collapse).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        (mapBoundary source.boundaryWire
          (WireRenaming.comp collapse sourceExternal.toRenaming))
        (rawBody.renameWires collapse)) :
      BackwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .localSever joined joinedItems partition occurrence _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill (completeLocal joined
          (joinedItems.partitionOutput
            (collapseLocal _ _ joined) partition)))
        targetCanonical targetExternalTwoEnded
  | .localJoin joined raw occurrence _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (raw.renameWires
            (collapseLocal _ _ joined))))
        targetCanonical targetExternalTwoEnded
  | .openSever _ _ _ sourceBody _ _ _ separateBoundary
      separateBoundarySurjective collapse _ _ partition targetCanonical
      targetExternalTwoEnded => {
      external := _
      boundaryWire := separateBoundary
      boundarySurjective := separateBoundarySurjective
      body := completeOpen separateBoundary
        (sourceBody.partitionOutput collapse partition)
      canonical := targetCanonical
      externalTwoEnded := targetExternalTwoEnded
    }

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary
  | .localJoin joined raw occurrence _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (raw.renameWires
            (collapseLocal _ _ joined))))
        targetCanonical targetExternalTwoEnded
  | .localSever joined joinedItems partition occurrence _ targetCanonical
      targetExternalTwoEnded =>
      occurrence.interface.withBody
        (occurrence.context.fill (completeLocal joined
          (joinedItems.partitionOutput
            (collapseLocal _ _ joined) partition)))
        targetCanonical targetExternalTwoEnded
  | .openJoin joinedWires _ sourceExternal rawBody _ _ _ collapse
      collapseSurjective targetCanonical targetExternalTwoEnded => {
      external := joinedWires
      boundaryWire := mapBoundary source.boundaryWire
        (WireRenaming.comp collapse sourceExternal.toRenaming)
      boundarySurjective := by
        intro joinedIndex
        let joinedWire := Var.ofIndex joinedIndex
        obtain ⟨representedWire, collapsed⟩ :=
          collapseSurjective joinedWire
        let actualWire := sourceExternal.symm representedWire
        obtain ⟨position, found⟩ :=
          source.boundarySurjective actualWire.index
        refine ⟨position, ?_⟩
        simp only [mapBoundary]
        rw [Vars.get_map_wire]
        apply Fin.ext
        calc
          (collapse (sourceExternal
              (source.boundaryWire.get position))).index.val =
              (collapse (sourceExternal actualWire)).index.val :=
            WireRenaming.index_eq_of_index_eq
              (WireRenaming.comp collapse sourceExternal.toRenaming)
              _ _ (congrArg Fin.val found)
          _ = (collapse representedWire).index.val := by
            rw [WireEquiv.apply_symm_apply]
          _ = joinedWire.index.val := congrArg (fun wire => wire.index.val)
            collapsed
          _ = joinedIndex.val := by simp only [joinedWire, Var.index_ofIndex]
      body := rawBody.renameWires collapse
      canonical := targetCanonical
      externalTwoEnded := targetExternalTwoEnded
    }

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.WireSever source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localSever joined joinedItems partition occurrence polarity
        targetCanonical targetExternalTwoEnded =>
        refine Or.inl ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.sever joined joinedItems partition
    | localJoin joined separate occurrence polarity targetCanonical
        targetExternalTwoEnded =>
        obtain ⟨partition, outputEq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (collapseLocal _ _ joined) separate
        refine Or.inl ⟨_, _, _, occurrence, targetCanonical,
          targetExternalTwoEnded, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        change Local
          (.mk _ (separate.renameWires (collapseLocal _ _ joined)))
          (completeLocal joined separate)
        simpa only [outputEq] using
          (Local.sever joined
            (separate.renameWires (collapseLocal _ _ joined)) partition)
    | openSever sourceWires signature sourceExternal sourceBody source_body
        sourceCanonical sourceExternalTwoEnded separateBoundary
        separateBoundarySurjective collapse collapseSurjective boundaryEq
        partition targetCanonical targetExternalTwoEnded =>
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
          boundary := boundaryEq
          partition := partition
          target_body := by
            change RegionIso (WireEquiv.refl _)
              (completeOpen separateBoundary
                (sourceBody.partitionOutput collapse partition))
              (completeOpen (mapBoundary separateBoundary WireRenaming.id)
                (sourceBody.partitionOutput collapse partition))
            apply regionIsoOfEq
            simp only [mapBoundary, Vars.map_id_wire]
          targetCanonical := by
            change (completeOpen (mapBoundary separateBoundary
              WireRenaming.id)
              (sourceBody.partitionOutput collapse partition)).Canonical
            simpa only [mapBoundary, Vars.map_id_wire] using targetCanonical
          targetExternalTwoEnded := by
            change OpenDiagram.ExternalTwoEnded
              (mapBoundary separateBoundary WireRenaming.id)
              (completeOpen (mapBoundary separateBoundary WireRenaming.id)
                (sourceBody.partitionOutput collapse partition))
            intro wireSignature wire
            simpa only [mapBoundary, Vars.map_id_wire] using
              targetExternalTwoEnded wire
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, before, after, occurrence,
        targetCanonical, targetExternalTwoEnded, targetIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              exact ⟨.localSever joined joinedItems partition occurrence
                polarity targetCanonical targetExternalTwoEnded,
                ⟨targetIso.symm⟩⟩
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let separate := joinedItems.partitionOutput
                (collapseLocal _ _ joined) partition
              have bodyEq : occurrence.context.fill
                    (.mk _ (separate.renameWires
                      (collapseLocal _ _ joined))) =
                  occurrence.context.fill (.mk _ joinedItems) := by
                simp only [separate, ItemSeq.partitionOutput_renameWires]
              have computedCanonical : (occurrence.context.fill
                  (.mk _ (separate.renameWires
                    (collapseLocal _ _ joined)))).Canonical := by
                rw [bodyEq]
                exact targetCanonical
              have computedExternalTwoEnded :
                  OpenDiagram.ExternalTwoEnded
                    occurrence.interface.boundaryWire
                    (occurrence.context.fill
                      (.mk _ (separate.renameWires
                        (collapseLocal _ _ joined)))) := by
                rw [bodyEq]
                intro wireSignature wire
                exact targetExternalTwoEnded wire
              let index := ForwardIndex.localJoin joined separate occurrence
                polarity computedCanonical computedExternalTwoEnded
              refine ⟨index, ⟨?_⟩⟩
              exact (OpenDiagram.withBody_iso computedCanonical
                targetCanonical computedExternalTwoEnded
                targetExternalTwoEnded (regionIsoOfEq bodyEq)).trans
                  targetIso.symm
    · rcases openNonempty with ⟨openStep⟩
      let separateBoundary := mapBoundary target.boundaryWire
        openStep.targetExternal.toRenaming
      have separateBoundarySurjective :
          ∀ wire : Fin (openStep.sourceWires ++ [openStep.signature]).length,
            ∃ position : Fin boundary.length,
              (separateBoundary.get position).index = wire := by
        intro representedIndex
        let representedWire := Var.ofIndex representedIndex
        let actualWire := openStep.targetExternal.symm representedWire
        obtain ⟨position, found⟩ :=
          target.boundarySurjective actualWire.index
        refine ⟨position, ?_⟩
        simp only [separateBoundary, mapBoundary]
        rw [Vars.get_map_wire]
        apply Fin.ext
        calc
          (openStep.targetExternal
              (target.boundaryWire.get position)).index.val =
              (openStep.targetExternal actualWire).index.val :=
            WireRenaming.index_eq_of_index_eq
              openStep.targetExternal.toRenaming _ _ (congrArg Fin.val found)
          _ = representedWire.index.val := by
            rw [WireEquiv.apply_symm_apply]
          _ = representedIndex.val := by
            simp only [representedWire, Var.index_ofIndex]
      refine ⟨.openSever openStep.sourceWires openStep.signature
        openStep.sourceExternal openStep.sourceBody openStep.source_body
        openStep.sourceCanonical openStep.sourceExternalTwoEnded
        separateBoundary separateBoundarySurjective openStep.collapse
        openStep.collapse_surjective ?_ openStep.partition
        openStep.targetCanonical openStep.targetExternalTwoEnded, ⟨?_⟩⟩
      · intro position
        simp only [separateBoundary, mapBoundary]
        rw [Vars.get_map_wire]
        exact openStep.boundary position
      · exact {
          external := openStep.targetExternal.symm
          boundary_eq := by
            intro position
            simp only [runForward, separateBoundary, mapBoundary]
            rw [Vars.get_map_wire]
            exact openStep.targetExternal.left_inv _
          body := openStep.target_body.symm
        }

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.WireSever target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply backward_respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localJoin joined separate occurrence polarity targetCanonical
        targetExternalTwoEnded =>
        obtain ⟨partition, outputEq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (collapseLocal _ _ joined) separate
        let joinedBody := Region.mk _
          (separate.renameWires (collapseLocal _ _ joined))
        let outputOccurrence : Occurrence joinedBody
            (occurrence.interface.withBody
              (occurrence.context.fill joinedBody) targetCanonical
              targetExternalTwoEnded) := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := targetExternalTwoEnded
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, outputOccurrence,
          occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        change Local joinedBody (completeLocal joined separate)
        simpa only [joinedBody, outputEq] using
          (Local.sever joined
            (separate.renameWires (collapseLocal _ _ joined)) partition)
    | localSever joined joinedItems partition occurrence polarity
        targetCanonical targetExternalTwoEnded =>
        let separate := joinedItems.partitionOutput
          (collapseLocal _ _ joined) partition
        let separateBody := completeLocal joined separate
        let outputOccurrence : Occurrence separateBody
            (occurrence.interface.withBody
              (occurrence.context.fill separateBody) targetCanonical
              targetExternalTwoEnded) := {
          interface := occurrence.interface
          context := occurrence.context
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := targetExternalTwoEnded
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, outputOccurrence,
          occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.sever joined joinedItems partition
    | openJoin joinedWires signature sourceExternal sourceBody source_body
        sourceCanonical sourceExternalTwoEnded collapse collapseSurjective
        targetCanonical targetExternalTwoEnded =>
        obtain ⟨partition, outputEq⟩ :=
          Region.exists_partition_of_renamed collapse sourceBody
        exact Or.inr ⟨{
          sourceWires := joinedWires
          signature := signature
          sourceExternal := WireEquiv.refl _
          targetExternal := sourceExternal
          sourceBody := sourceBody.renameWires collapse
          source_body := RegionIso.refl _
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := by
            change OpenDiagram.ExternalTwoEnded
              (mapBoundary
                (mapBoundary source.boundaryWire
                  (WireRenaming.comp collapse sourceExternal.toRenaming))
                WireRenaming.id)
              (sourceBody.renameWires collapse)
            intro wireSignature wire
            simpa only [mapBoundary, Vars.map_id_wire] using
              targetExternalTwoEnded wire
          collapse := collapse
          collapse_surjective := collapseSurjective
          boundary := by
            intro position
            simp only [runBackward, mapBoundary]
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
            change OpenDiagram.ExternalTwoEnded
              (mapBoundary source.boundaryWire sourceExternal.toRenaming)
              (completeOpen
                (mapBoundary source.boundaryWire sourceExternal.toRenaming)
                ((sourceBody.renameWires collapse).partitionOutput collapse
                  partition))
            rw [outputEq]
            intro wireSignature wire
            exact sourceExternalTwoEnded wire
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, before, after, occurrence,
        targetCanonical, targetExternalTwoEnded, sourceIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let separate := joinedItems.partitionOutput
                (collapseLocal _ _ joined) partition
              let sourceOccurrence : Occurrence
                  (completeLocal joined separate) source := {
                interface := occurrence.interface
                context := occurrence.context
                sourceCanonical := targetCanonical
                sourceExternalTwoEnded := targetExternalTwoEnded
                host_iso := sourceIso
              }
              have bodyEq : sourceOccurrence.context.fill
                    (.mk _ (separate.renameWires
                      (collapseLocal _ _ joined))) =
                  occurrence.context.fill (.mk _ joinedItems) := by
                simp only [sourceOccurrence, separate,
                  ItemSeq.partitionOutput_renameWires]
              have computedCanonical : (sourceOccurrence.context.fill
                  (.mk _ (separate.renameWires
                    (collapseLocal _ _ joined)))).Canonical := by
                rw [bodyEq]
                exact occurrence.sourceCanonical
              have computedExternalTwoEnded :
                  OpenDiagram.ExternalTwoEnded
                    sourceOccurrence.interface.boundaryWire
                    (sourceOccurrence.context.fill
                      (.mk _ (separate.renameWires
                        (collapseLocal _ _ joined)))) := by
                rw [bodyEq]
                intro wireSignature wire
                exact occurrence.sourceExternalTwoEnded wire
              let index := BackwardIndex.localJoin joined separate
                sourceOccurrence polarity computedCanonical
                computedExternalTwoEnded
              refine ⟨index, ⟨?_⟩⟩
              exact (OpenDiagram.withBody_iso computedCanonical
                occurrence.sourceCanonical computedExternalTwoEnded
                occurrence.sourceExternalTwoEnded
                (regionIsoOfEq bodyEq)).trans occurrence.host_iso.symm
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let sourceOccurrence : Occurrence
                  (.mk _ joinedItems) source := {
                interface := occurrence.interface
                context := occurrence.context
                sourceCanonical := targetCanonical
                sourceExternalTwoEnded := targetExternalTwoEnded
                host_iso := sourceIso
              }
              exact ⟨.localSever joined joinedItems partition sourceOccurrence
                polarity occurrence.sourceCanonical
                occurrence.sourceExternalTwoEnded,
                ⟨occurrence.host_iso.symm⟩⟩
    · rcases openNonempty with ⟨openStep⟩
      let separateBody := openStep.sourceBody.partitionOutput
        openStep.collapse openStep.partition
      let joinedBoundary := mapBoundary source.boundaryWire
        (WireRenaming.comp openStep.collapse
          openStep.targetExternal.toRenaming)
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
      have joinedCanonical :
          (separateBody.renameWires openStep.collapse).Canonical := by
        rw [bodyEq]
        exact openStep.sourceCanonical
      have joinedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          joinedBoundary (separateBody.renameWires openStep.collapse) := by
        rw [boundaryEq, bodyEq]
        intro wireSignature wire
        exact openStep.sourceExternalTwoEnded wire
      let index := BackwardIndex.openJoin openStep.sourceWires
        openStep.signature openStep.targetExternal separateBody
        openStep.target_body openStep.targetCanonical
        openStep.targetExternalTwoEnded openStep.collapse
        openStep.collapse_surjective joinedCanonical joinedExternalTwoEnded
      refine ⟨index, ⟨?_⟩⟩
      exact {
        external := openStep.sourceExternal.symm
        boundary_eq := by
          intro position
          simp only [index, runBackward, joinedBoundary, mapBoundary]
          rw [Vars.get_map_wire]
          change openStep.sourceExternal.symm
              (openStep.collapse
                (openStep.targetExternal
                  (source.boundaryWire.get position))) =
            target.boundaryWire.get position
          rw [openStep.boundary position]
          exact openStep.sourceExternal.left_inv _
        body := (regionIsoOfEq bodyEq).trans openStep.source_body.symm
      }

end VisualProof.Rule.WireSever
