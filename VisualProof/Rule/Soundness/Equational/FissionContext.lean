import VisualProof.Rule.Soundness.Equational.FissionTerm
import VisualProof.Diagram.Concrete.Elaboration.Simulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace FissionSoundness

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) = (allFin n).map Fin.castSucc ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]

@[simp] theorem fissionRaw_oldWire_scope
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (wire : Fin input.val.wireCount) :
    ((fissionRaw input node region producer residual).wires wire.castSucc).scope =
      (input.val.wires wire).scope := by
  simp [fissionRaw]

@[simp] theorem fissionRaw_freshWire_scope
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    ((fissionRaw input node region producer residual).wires
      (Fin.last input.val.wireCount)).scope = region := by
  simp [fissionRaw]

theorem fissionRaw_exactScopeWires_mem_old_iff
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (wire : Fin input.val.wireCount) :
    wire.castSucc ∈ ConcreteElaboration.exactScopeWires
        (fissionRaw input node site producer residual) candidateRegion ↔
      wire ∈ ConcreteElaboration.exactScopeWires input.val candidateRegion := by
  constructor
  · intro member
    have scope := (ConcreteElaboration.mem_exactScopeWires
      (fissionRaw input node site producer residual) candidateRegion
      wire.castSucc).mp member
    rw [fissionRaw_oldWire_scope] at scope
    exact (ConcreteElaboration.mem_exactScopeWires input.val candidateRegion
      wire).mpr scope
  · intro member
    have scope := (ConcreteElaboration.mem_exactScopeWires input.val
      candidateRegion wire).mp member
    apply (ConcreteElaboration.mem_exactScopeWires
      (fissionRaw input node site producer residual) candidateRegion
      wire.castSucc).mpr
    rw [fissionRaw_oldWire_scope]
    exact scope

theorem fissionRaw_exactScopeWires
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    ConcreteElaboration.exactScopeWires
        (fissionRaw input node site producer residual) candidateRegion =
      (ConcreteElaboration.exactScopeWires input.val candidateRegion).map
          Fin.castSucc ++
        if candidateRegion = site then [Fin.last input.val.wireCount] else [] := by
  unfold ConcreteElaboration.exactScopeWires filterFin
  change List.filter _ (allFin (input.val.wireCount + 1)) = _
  rw [allFin_succ_last, List.filter_append, List.filter_map]
  congr 1
  · apply congrArg (List.map Fin.castSucc)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.wireCount))
    funext wire
    simp only [Function.comp_apply]
    rw [fissionRaw_oldWire_scope]
    rfl
  · by_cases equality : candidateRegion = site
    · subst candidateRegion
      simp [fissionRaw_freshWire_scope]
    · have reverse : site ≠ candidateRegion := fun same => equality same.symm
      simp [fissionRaw_freshWire_scope, equality]
      exact reverse

/-- The source lexical wire context embedded in the append-only fission wire
layout.  The target has one additional site-local wire. -/
structure ContextEmbedding
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fissionRaw input node site producer residual)) where
  index : Fin source.length → Fin target.length
  get : ∀ i, target.get (index i) = (source.get i).castSucc
  mem_old : ∀ wire : Fin input.val.wireCount,
    wire.castSucc ∈ target ↔ wire ∈ source

namespace ContextEmbedding

noncomputable def ofMem
    {input : CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {site : Fin input.val.regionCount}
    {producer : Lambda.Term 0 (Fin input.val.wireCount)}
    {residual : Lambda.Term 0 (Option (Fin input.val.wireCount))}
    {source : ConcreteElaboration.WireContext input.val}
    {target : ConcreteElaboration.WireContext
      (fissionRaw input node site producer residual)}
    (membership : ∀ wire : Fin input.val.wireCount,
      wire.castSucc ∈ target ↔ wire ∈ source) :
    ContextEmbedding input node site producer residual source target where
  index := fun i => Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((membership (source.get i)).mpr (List.get_mem source i)))
  get := by
    intro i
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (ConcreteElaboration.WireContext.lookup?_complete
          ((membership (source.get i)).mpr (List.get_mem source i))))
  mem_old := membership

theorem index_eq_of_get
    (embedding : ContextEmbedding input node site producer residual
      source target)
    (targetNodup : target.Nodup) (i : Fin source.length)
    (candidate : Fin target.length)
    (candidateGet : target.get candidate = (source.get i).castSucc) :
    candidate = embedding.index i := by
  obtain ⟨found, foundResult⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete
      (List.get_mem target candidate)
  have candidateFound := ConcreteElaboration.WireContext.lookup?_unique
    targetNodup foundResult rfl
  have embeddingFound := ConcreteElaboration.WireContext.lookup?_unique
    targetNodup foundResult ((embedding.get i).trans candidateGet.symm)
  exact candidateFound.trans embeddingFound.symm

theorem index_injective
    (embedding : ContextEmbedding input node site producer residual
      source target)
    (sourceNodup : source.Nodup) : Function.Injective embedding.index := by
  intro first second equality
  have wires : source.get first = source.get second := by
    have castEquality : (source.get first).castSucc =
        (source.get second).castSucc := by
      rw [← embedding.get first, ← embedding.get second, equality]
    apply Fin.ext
    have values := congrArg
      (fun value : Fin (input.val.wireCount + 1) => value.val) castEquality
    simpa only [Fin.val_castSucc] using values
  apply Fin.ext
  exact (List.getElem_inj sourceNodup).mp (by
    simpa only [List.get_eq_getElem] using wires)

noncomputable def extendEnvironment
    (embedding : ContextEmbedding input node site producer residual
      source target)
    (sourceNodup : source.Nodup) (fallback : D)
    (sourceEnv : Fin source.length → D) : Fin target.length → D :=
  fun targetIndex =>
    if witness : ∃ sourceIndex, embedding.index sourceIndex = targetIndex then
      sourceEnv witness.choose
    else fallback

theorem extendEnvironment_index
    (embedding : ContextEmbedding input node site producer residual
      source target)
    (sourceNodup : source.Nodup) (fallback : D)
    (sourceEnv : Fin source.length → D) :
    embedding.extendEnvironment sourceNodup fallback sourceEnv ∘
        embedding.index = sourceEnv := by
  funext sourceIndex
  simp only [Function.comp_apply, extendEnvironment]
  split
  · rename_i witness
    exact congrArg sourceEnv
      (embedding.index_injective sourceNodup witness.choose_spec)
  · rename_i absent
    exact False.elim (absent ⟨sourceIndex, rfl⟩)

noncomputable def extend
    (embedding : ContextEmbedding input node site producer residual
      source target)
    (region : Fin input.val.regionCount) :
    ContextEmbedding input node site producer residual
      (source.extend region) (target.extend region) :=
  ofMem (by
    intro wire
    unfold ConcreteElaboration.WireContext.extend
    constructor
    · intro member
      rcases List.mem_append.mp member with inherited | localMember
      · exact List.mem_append_left _ ((embedding.mem_old wire).mp inherited)
      · exact List.mem_append_right _
          ((fissionRaw_exactScopeWires_mem_old_iff input node site region
            producer residual wire).mp localMember)
    · intro member
      rcases List.mem_append.mp member with inherited | localMember
      · exact List.mem_append_left _ ((embedding.mem_old wire).mpr inherited)
      · exact List.mem_append_right _
          ((fissionRaw_exactScopeWires_mem_old_iff input node site region
            producer residual wire).mpr localMember))

end ContextEmbedding

@[simp] theorem fissionRaw_oldNode_region
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : input.val.nodes node = .term region freePorts term)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (candidate : Fin input.val.nodeCount) :
    ((fissionRaw input node region producer residual).nodes
      candidate.castSucc).region = (input.val.nodes candidate).region := by
  by_cases selected : candidate = node
  · subst candidate
    simp [fissionRaw, nodeShape]
    rfl
  · simp [fissionRaw, selected]

@[simp] theorem fissionRaw_producer_node
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    (fissionRaw input node region producer residual).nodes
        (Fin.last input.val.nodeCount) =
      .term region producer.freeSupport.length producer.compact := by
  simp [fissionRaw]

theorem fissionRaw_nodeOccurrences
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : input.val.nodes node = .term site freePorts term)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    (filterFin fun candidate : Fin (fissionRaw input node site producer
      residual).nodeCount => decide (((fissionRaw input node site producer
        residual).nodes candidate).region = candidateRegion)) =
      (filterFin fun candidate : Fin input.val.nodeCount =>
        decide ((input.val.nodes candidate).region = candidateRegion)).map
          Fin.castSucc ++
        if site = candidateRegion then [Fin.last input.val.nodeCount] else [] := by
  unfold filterFin
  change List.filter _ (allFin (input.val.nodeCount + 1)) = _
  rw [allFin_succ_last, List.filter_append, List.filter_map]
  congr 1
  · apply congrArg (List.map Fin.castSucc)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.val.nodeCount))
    funext candidate
    simp only [Function.comp_apply]
    rw [fissionRaw_oldNode_region input node site freePorts term nodeShape]
    rfl
  · by_cases equality : site = candidateRegion
    · subst candidateRegion
      simp
      rfl
    · simp [equality]
      exact equality

theorem fissionRaw_childOccurrences
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    (filterFin fun child : Fin (fissionRaw input node site producer
      residual).regionCount => decide ((((fissionRaw input node site producer
        residual).regions child).parent?) = some candidateRegion)) =
      filterFin fun child : Fin input.val.regionCount =>
        decide ((input.val.regions child).parent? = some candidateRegion) := by
  rfl

def mapOccurrence (input : CheckedDiagram signature)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount
      (input.val.nodeCount + 1) :=
  match occurrence with
  | .node candidate => ConcreteElaboration.LocalOccurrence.node candidate.castSucc
  | .child child => ConcreteElaboration.LocalOccurrence.child child

theorem fissionRaw_localOccurrences
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : input.val.nodes node = .term site freePorts term)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    ConcreteElaboration.localOccurrences
        (fissionRaw input node site producer residual) candidateRegion =
      ((filterFin fun candidate : Fin input.val.nodeCount =>
          decide ((input.val.nodes candidate).region = candidateRegion)).map
        (fun candidate => ConcreteElaboration.LocalOccurrence.node
          candidate.castSucc)) ++
        (if site = candidateRegion then
          [ConcreteElaboration.LocalOccurrence.node
            (Fin.last input.val.nodeCount)]
        else []) ++
      ((filterFin fun child : Fin input.val.regionCount =>
          decide ((input.val.regions child).parent? = some candidateRegion)).map
        (fun child => (ConcreteElaboration.LocalOccurrence.child child :
          ConcreteElaboration.LocalOccurrence input.val.regionCount
            (input.val.nodeCount + 1)))) := by
  unfold ConcreteElaboration.localOccurrences
  rw [fissionRaw_nodeOccurrences input node site candidateRegion freePorts term
      nodeShape producer residual]
  simp only [fissionRaw]
  rw [List.map_append, List.map_map]
  have nodeMap :
      List.map ((@ConcreteElaboration.LocalOccurrence.node
          input.val.regionCount (input.val.nodeCount + 1)) ∘ Fin.castSucc)
          (filterFin fun candidate : Fin input.val.nodeCount =>
            decide ((input.val.nodes candidate).region = candidateRegion)) =
        List.map (fun candidate : Fin input.val.nodeCount =>
          (ConcreteElaboration.LocalOccurrence.node candidate.castSucc :
            ConcreteElaboration.LocalOccurrence input.val.regionCount
              (input.val.nodeCount + 1)))
          (filterFin fun candidate : Fin input.val.nodeCount =>
            decide ((input.val.nodes candidate).region = candidateRegion)) := by
    rfl
  rw [nodeMap]
  have childMap :
      List.map (@ConcreteElaboration.LocalOccurrence.child
          input.val.regionCount (input.val.nodeCount + 1))
          (filterFin fun child : Fin input.val.regionCount =>
            decide ((input.val.regions child).parent? = some candidateRegion)) =
        List.map (fun child =>
          (ConcreteElaboration.LocalOccurrence.child child :
            ConcreteElaboration.LocalOccurrence input.val.regionCount
              (input.val.nodeCount + 1)))
          (filterFin fun child : Fin input.val.regionCount =>
            decide ((input.val.regions child).parent? = some candidateRegion)) := by
    rfl
  rw [childMap]
  by_cases equality : site = candidateRegion
  · simp only [if_pos equality, List.map_singleton]
    congr 1
  · simp only [if_neg equality, List.map_nil, List.append_nil]
    congr 1

theorem fissionRaw_localOccurrences_regular
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site candidateRegion : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : input.val.nodes node = .term site freePorts term)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (regular : candidateRegion ≠ site) :
    ConcreteElaboration.localOccurrences
        (fissionRaw input node site producer residual) candidateRegion =
      (ConcreteElaboration.localOccurrences input.val candidateRegion).map
        (mapOccurrence input) := by
  rw [fissionRaw_localOccurrences input node site candidateRegion freePorts term
    nodeShape producer residual, if_neg regular.symm]
  unfold ConcreteElaboration.localOccurrences
  rw [List.map_append, List.map_map, List.map_map]
  simp only [mapOccurrence, Function.comp_def, List.append_nil]
  congr 1

theorem fissionRaw_localOccurrences_focused
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (nodeShape : input.val.nodes node = .term site freePorts term)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    ConcreteElaboration.localOccurrences
        (fissionRaw input node site producer residual) site =
      ((filterFin fun candidate : Fin input.val.nodeCount =>
          decide ((input.val.nodes candidate).region = site)).map
        (fun candidate => ConcreteElaboration.LocalOccurrence.node
          candidate.castSucc)) ++
        [ConcreteElaboration.LocalOccurrence.node
          (Fin.last input.val.nodeCount)] ++
      ((filterFin fun child : Fin input.val.regionCount =>
          decide ((input.val.regions child).parent? = some site)).map
        (fun child => (ConcreteElaboration.LocalOccurrence.child child :
          ConcreteElaboration.LocalOccurrence input.val.regionCount
            (input.val.nodeCount + 1)))) := by
  rw [fissionRaw_localOccurrences input node site site freePorts term nodeShape
    producer residual, if_pos rfl]

end FissionSoundness

end VisualProof.Rule
