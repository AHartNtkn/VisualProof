import VisualProof.Rule.WireSever

namespace VisualProof.Rule.WireSever

open Theory
open Diagram

private noncomputable def regionIsoOfEq
    {left right : Region wires rels} (equality : left = right) :
    RegionIso (FiniteEquiv.refl (Fin wires)) rels left right := by
  subst right
  exact RegionIso.refl left

inductive ForwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | localSever
      (joined : Fin (wires + localWires))
      (joinedItems : ItemSeq (wires + localWires) rels)
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems)
      (occurrence : Occurrence (.mk localWires joinedItems) source)
      (polarity : occurrence.context.polarity = .positive) :
      ForwardIndex source
  | localJoin
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence (.mk (localWires + 1) separate) source)
      (polarity : occurrence.context.polarity = .negative) :
      ForwardIndex source
  | openSever
      (sourceWires : Nat)
      (targetClasses : Nat)
      (sourceExternal : FiniteEquiv
        (Fin source.externalClasses) (Fin sourceWires))
      (sourceBody : Region sourceWires [])
      (source_body : RegionIso sourceExternal [] source.body sourceBody)
      (one_more : targetClasses = sourceWires + 1)
      (separateBoundary : Fin arity → Fin targetClasses)
      (separateBoundary_surjective : Function.Surjective separateBoundary)
      (collapse : Fin targetClasses → Fin sourceWires)
      (collapse_surjective : Function.Surjective collapse)
      (boundary : ∀ position,
        collapse (separateBoundary position) =
          sourceExternal (source.boundary position))
      (partition : Region.PortPartition collapse sourceBody) :
      ForwardIndex source

inductive BackwardIndex {arity : Nat} (source : OpenDiagram arity) : Type
  | localJoin
      (joined : Fin (wires + localWires))
      (separate : ItemSeq (wires + (localWires + 1)) rels)
      (occurrence : Occurrence (.mk (localWires + 1) separate) source)
      (polarity : occurrence.context.polarity = .positive) :
      BackwardIndex source
  | localSever
      (joined : Fin (wires + localWires))
      (joinedItems : ItemSeq (wires + localWires) rels)
      (partition : ItemSeq.PortPartition
        (collapseLocal wires localWires joined) joinedItems)
      (occurrence : Occurrence (.mk localWires joinedItems) source)
      (polarity : occurrence.context.polarity = .negative) :
      BackwardIndex source
  | openJoin
      (sourceWires joinedWires : Nat)
      (sourceExternal : FiniteEquiv
        (Fin source.externalClasses) (Fin sourceWires))
      (sourceBody : Region sourceWires [])
      (source_body : RegionIso sourceExternal [] source.body sourceBody)
      (one_more : sourceWires = joinedWires + 1)
      (collapse : Fin sourceWires → Fin joinedWires)
      (collapse_surjective : Function.Surjective collapse) :
      BackwardIndex source

def runForward (source : OpenDiagram arity) :
    ForwardIndex source → OpenDiagram arity
  | .localSever joined joinedItems partition occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _
          (joinedItems.partitionOutput
            (collapseLocal _ _ joined) partition)))
  | .localJoin joined separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (separate.renameWires
            (collapseLocal _ _ joined))))
  | .openSever _ targetClasses _ sourceBody _ _ separateBoundary
      separateBoundary_surjective collapse _ _ partition => {
      externalClasses := targetClasses
      boundary := separateBoundary
      boundary_surjective := separateBoundary_surjective
      body := sourceBody.partitionOutput collapse partition
    }

def runBackward (source : OpenDiagram arity) :
    BackwardIndex source → OpenDiagram arity
  | .localJoin joined separate occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill
          (.mk _ (separate.renameWires
            (collapseLocal _ _ joined))))
  | .localSever joined joinedItems partition occurrence _ =>
      occurrence.interface.withBody
        (occurrence.context.fill (.mk _
          (joinedItems.partitionOutput
            (collapseLocal _ _ joined) partition)))
  | .openJoin _ joinedWires sourceExternal sourceBody _ _ collapse
      collapse_surjective => {
      externalClasses := joinedWires
      boundary := collapse ∘ sourceExternal.toFun ∘ source.boundary
      boundary_surjective := by
        intro targetWire
        obtain ⟨sourceWire, collapsed⟩ := collapse_surjective targetWire
        let actualWire := sourceExternal.invFun sourceWire
        have represented : sourceExternal actualWire = sourceWire :=
          sourceExternal.right_inv sourceWire
        obtain ⟨position, found⟩ := source.boundary_surjective actualWire
        exact ⟨position, by
          simp only [Function.comp_apply, found, represented, collapsed]⟩
      body := sourceBody.renameWires collapse
    }

theorem forward_exact (source target : OpenDiagram arity) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
    Rule.WireSever source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localSever joined joinedItems partition occurrence polarity =>
        refine Or.inl ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        exact Local.sever joined joinedItems partition
    | localJoin joined separate occurrence polarity =>
        obtain ⟨partition, output_eq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (collapseLocal _ _ joined) separate
        refine Or.inl ⟨_, _, _, _, occurrence, OpenDiagramIso.refl _, ?_⟩
        rw [polarity]
        change Local
          (.mk _ (separate.renameWires (collapseLocal _ _ joined)))
          (.mk _ separate)
        simpa only [output_eq] using
          (Local.sever joined
            (separate.renameWires (collapseLocal _ _ joined)) partition)
    | openSever sourceWires targetClasses sourceExternal sourceBody
        source_body one_more separateBoundary separateBoundary_surjective
        collapse collapse_surjective boundary partition =>
        exact Or.inr ⟨{
          sourceWires := sourceWires
          targetWires := targetClasses
          sourceExternal := sourceExternal
          targetExternal := FiniteEquiv.refl _
          sourceBody := sourceBody
          source_body := source_body
          one_more := one_more
          collapse := collapse
          collapse_surjective := collapse_surjective
          boundary := boundary
          partition := partition
          target_body := RegionIso.refl _
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, rels, before, after, occurrence,
        targetIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              exact ⟨.localSever joined joinedItems partition occurrence polarity,
                ⟨targetIso.symm⟩⟩
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let separate := joinedItems.partitionOutput
                (collapseLocal _ _ joined) partition
              refine ⟨.localJoin joined separate occurrence polarity,
                ⟨?_⟩⟩
              simpa only [runForward, separate,
                ItemSeq.partitionOutput_renameWires] using targetIso.symm
    · rcases openNonempty with ⟨openStep⟩
      let separateBoundary : Fin arity → Fin openStep.targetWires :=
        openStep.targetExternal.toFun ∘ target.boundary
      have separateBoundary_surjective :
          Function.Surjective separateBoundary := by
        intro wire
        let actualWire := openStep.targetExternal.invFun wire
        obtain ⟨position, found⟩ := target.boundary_surjective actualWire
        exact ⟨position, by
          simp only [separateBoundary, Function.comp_apply, found]
          exact openStep.targetExternal.right_inv wire⟩
      refine ⟨.openSever openStep.sourceWires openStep.targetWires
        openStep.sourceExternal openStep.sourceBody openStep.source_body
        openStep.one_more separateBoundary separateBoundary_surjective
        openStep.collapse openStep.collapse_surjective ?_ openStep.partition,
        ⟨?_ ⟩⟩
      · exact openStep.boundary
      · exact {
          external := openStep.targetExternal.symm
          boundary := by
            intro position
            change openStep.targetExternal.symm
              (separateBoundary position) = target.boundary position
            simp only [separateBoundary, Function.comp_apply,
              FiniteEquiv.symm_apply_apply]
          body := openStep.target_body.symm
        }

theorem backward_exact (source target : OpenDiagram arity) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
    Rule.WireSever target source := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply backward_respectsTargetIso (target' := target) ?_ isomorphic
    cases index with
    | localJoin joined separate occurrence polarity =>
        obtain ⟨partition, output_eq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (collapseLocal _ _ joined) separate
        let outputOccurrence : Occurrence
            (.mk _ (separate.renameWires (collapseLocal _ _ joined)))
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk _ (separate.renameWires
                  (collapseLocal _ _ joined))))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, _, outputOccurrence,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        change Local
          (.mk _ (separate.renameWires (collapseLocal _ _ joined)))
          (.mk _ separate)
        simpa only [output_eq] using
          (Local.sever joined
            (separate.renameWires (collapseLocal _ _ joined)) partition)
    | localSever joined joinedItems partition occurrence polarity =>
        let separate := joinedItems.partitionOutput
          (collapseLocal _ _ joined) partition
        let outputOccurrence : Occurrence (.mk _ separate)
            (occurrence.interface.withBody
              (occurrence.context.fill (.mk _ separate))) := {
          interface := occurrence.interface
          context := occurrence.context
          host_iso := OpenDiagramIso.refl _
        }
        refine Or.inl ⟨_, _, _, _, outputOccurrence,
          occurrence.host_iso, ?_⟩
        rw [polarity]
        exact Local.sever joined joinedItems partition
    | openJoin sourceWires joinedWires sourceExternal sourceBody source_body
        one_more collapse collapse_surjective =>
        obtain ⟨partition, output_eq⟩ :=
          Region.exists_partition_of_renamed collapse sourceBody
        exact Or.inr ⟨{
          sourceWires := joinedWires
          targetWires := sourceWires
          sourceExternal := FiniteEquiv.refl _
          targetExternal := sourceExternal
          sourceBody := sourceBody.renameWires collapse
          source_body := RegionIso.refl _
          one_more := one_more
          collapse := collapse
          collapse_surjective := collapse_surjective
          boundary := fun _ => rfl
          partition := partition
          target_body := by
            rw [output_eq]
            exact source_body
        }⟩
  · intro step
    rcases step with localStep | openNonempty
    · rcases localStep with ⟨wires, rels, before, after, occurrence,
        sourceIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let separate := joinedItems.partitionOutput
                (collapseLocal _ _ joined) partition
              let sourceOccurrence : Occurrence (.mk _ separate) source := {
                interface := occurrence.interface
                context := occurrence.context
                host_iso := sourceIso
              }
              refine ⟨.localJoin joined separate sourceOccurrence
                polarity, ⟨?_⟩⟩
              simpa only [runBackward, separate,
                ItemSeq.partitionOutput_renameWires] using
                occurrence.host_iso.symm
      | negative =>
          simp only [polarity, atPolarity, converse] at localEvidence
          cases localEvidence with
          | sever joined joinedItems partition =>
              let sourceOccurrence : Occurrence
                  (.mk _ joinedItems) source := {
                interface := occurrence.interface
                context := occurrence.context
                host_iso := sourceIso
              }
              exact ⟨.localSever joined joinedItems partition sourceOccurrence
                polarity, ⟨occurrence.host_iso.symm⟩⟩
    · rcases openNonempty with ⟨openStep⟩
      let separateBody := openStep.sourceBody.partitionOutput
        openStep.collapse openStep.partition
      refine ⟨.openJoin openStep.targetWires openStep.sourceWires
        openStep.targetExternal separateBody openStep.target_body
        openStep.one_more openStep.collapse openStep.collapse_surjective,
        ⟨?_⟩⟩
      exact {
        external := openStep.sourceExternal.symm
        boundary := by
          intro position
          change openStep.sourceExternal.symm
            (openStep.collapse
              (openStep.targetExternal (source.boundary position))) =
            target.boundary position
          rw [openStep.boundary position,
            FiniteEquiv.symm_apply_apply]
        body := by
          have body_eq : separateBody.renameWires openStep.collapse =
              openStep.sourceBody :=
            Region.partitionOutput_renameWires _ _ _
          exact (regionIsoOfEq body_eq).trans openStep.source_body.symm
      }

end VisualProof.Rule.WireSever
