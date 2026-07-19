import VisualProof.Rule.Soundness.Equational.FissionFrame

namespace VisualProof.Rule

open VisualProof
open Diagram

namespace FissionSoundness

theorem exactScopeWires_length_at_site
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount))) :
    (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length =
      (ConcreteElaboration.exactScopeWires input.val site).length + 1 := by
  rw [fissionRaw_exactScopeWires, if_pos rfl]
  calc
    (List.map Fin.castSucc
        (ConcreteElaboration.exactScopeWires input.val site) ++
      [Fin.last input.val.wireCount]).length =
        (List.map Fin.castSucc
          (ConcreteElaboration.exactScopeWires input.val site)).length +
          [Fin.last input.val.wireCount].length := List.length_append
    _ = (ConcreteElaboration.exactScopeWires input.val site).length + 1 := by
      rw [List.length_map]
      rfl

noncomputable def extendedWireMapAtSite
    (embedding : ContextEmbedding input selected site producer residual
      source target) :
    Fin (source.extend site).length → Fin (target.extend site).length :=
  fun index =>
    Fin.cast (ConcreteElaboration.WireContext.length_extend target site).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (fissionRaw input selected site producer residual) site).length
          (embedding.index outer))
        (fun localIndex => Fin.natAdd target.length
          (Fin.cast (exactScopeWires_length_at_site input selected site producer
            residual).symm localIndex.castSucc))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source site) index))

theorem extendedWireMapAtSite_spec
    (embedding : ContextEmbedding input selected site producer residual
      source target)
    (index : Fin (source.extend site).length) :
    (target.extend site).get (extendedWireMapAtSite embedding index) =
      ((source.extend site).get index).castSucc := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source site) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source site).symm split =
        index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapEq : extendedWireMapAtSite embedding
        (Fin.cast (ConcreteElaboration.WireContext.length_extend source site).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.val site).length outer)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend target site).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (fissionRaw input selected site producer residual) site).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [extendedWireMapAtSite]
    rw [mapEq]
    simpa [ConcreteElaboration.WireContext.extend] using embedding.get outer
  · have mapEq : extendedWireMapAtSite embedding
        (Fin.cast (ConcreteElaboration.WireContext.length_extend source site).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend target site).symm
          (Fin.natAdd target.length
            (Fin.cast (exactScopeWires_length_at_site input selected site
              producer residual).symm localIndex.castSucc)) := by
      apply Fin.ext
      simp [extendedWireMapAtSite]
    rw [mapEq]
    have scopeList := fissionRaw_exactScopeWires input selected site site
      producer residual
    rw [if_pos rfl] at scopeList
    simp [ConcreteElaboration.WireContext.extend, scopeList]
    change
      (List.map Fin.castSucc
        (ConcreteElaboration.exactScopeWires input.val site) ++
          [Fin.last input.val.wireCount])[localIndex.val] =
        (ConcreteElaboration.exactScopeWires input.val site)[localIndex.val].castSucc
    rw [List.getElem_append_left (by
      rw [List.length_map]
      exact localIndex.isLt)]
    exact List.getElem_map _

theorem ContextEmbedding.extend_index_eq_map_at_site
    (embedding : ContextEmbedding input selected site producer residual
      source target)
    (targetNodup : (target.extend site).Nodup)
    (index : Fin (source.extend site).length) :
    (embedding.extend site).index index = extendedWireMapAtSite embedding index := by
  symm
  apply ContextEmbedding.index_eq_of_get (embedding.extend site) targetNodup
    index
  exact extendedWireMapAtSite_spec embedding index

theorem extendWireEnv_at_site
    (embedding : ContextEmbedding input selected site producer residual
      source target)
    (outerEnvironment : Fin target.length → D)
    (localEnvironment : Fin (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length → D) :
    (extendWireEnv outerEnvironment localEnvironment ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend target site)) ∘
        extendedWireMapAtSite embedding =
      extendWireEnv (outerEnvironment ∘ embedding.index)
          (fun localWire => localEnvironment
            (Fin.cast (exactScopeWires_length_at_site input selected site
              producer residual).symm localWire.castSucc)) ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend source site) := by
  funext wire
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source site) wire
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source site).symm split =
        wire := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localWire => ?_) split
  · simp [extendedWireMapAtSite, extendWireEnv, Function.comp_def]
  · simp [extendedWireMapAtSite, extendWireEnv, Function.comp_def]

def focusedTargetLocal
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val site).length → D)
    (fresh : D) :
    Fin (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length → D :=
  fun index => Fin.lastCases fresh sourceLocal
    (Fin.cast (exactScopeWires_length_at_site input selected site producer
      residual) index)

@[simp] theorem focusedTargetLocal_old
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val site).length → D)
    (fresh : D) (wire : Fin (ConcreteElaboration.exactScopeWires input.val site).length) :
    focusedTargetLocal input selected site producer residual sourceLocal fresh
      (Fin.cast (exactScopeWires_length_at_site input selected site producer
        residual).symm wire.castSucc) = sourceLocal wire := by
  simp [focusedTargetLocal]

@[simp] theorem focusedTargetLocal_fresh
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val site).length → D)
    (fresh : D) :
    focusedTargetLocal input selected site producer residual sourceLocal fresh
      (Fin.cast (exactScopeWires_length_at_site input selected site producer
        residual).symm
        (Fin.last (ConcreteElaboration.exactScopeWires input.val site).length)) =
      fresh := by
  simp [focusedTargetLocal]

theorem focusedForwardAgreement
    (embedding : ContextEmbedding input selected site producer residual
      source target)
    (targetExact : (target.extend site).Exact site)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : (ConcreteElaboration.ContextIndexRelation.forwardMap
      embedding.index).EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val site).length → D)
    (fresh : D) :
    (ConcreteElaboration.ContextIndexRelation.forwardMap
      (embedding.extend site).index).EnvironmentsAgree
      (ConcreteElaboration.extendedEnvironment source site sourceOuter sourceLocal)
      (ConcreteElaboration.extendedEnvironment target site targetOuter
        (focusedTargetLocal input selected site producer residual sourceLocal
          fresh)) := by
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
    (embedding.extend site).index _ _).mpr
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgrees
  have indexEq : (embedding.extend site).index =
      extendedWireMapAtSite embedding := by
    funext index
    exact embedding.extend_index_eq_map_at_site targetExact.nodup index
  have environmentEq := extendWireEnv_at_site embedding targetOuter
    (focusedTargetLocal input selected site producer residual sourceLocal fresh)
  have localEq :
      (fun localWire =>
        focusedTargetLocal input selected site producer residual sourceLocal fresh
          (Fin.cast (exactScopeWires_length_at_site input selected site producer
            residual).symm localWire.castSucc)) = sourceLocal := by
    funext localWire
    exact focusedTargetLocal_old input selected site producer residual
      sourceLocal fresh localWire
  unfold ConcreteElaboration.extendedEnvironment
  rw [indexEq, environmentEq, localEq, outerEq]

def focusedSourceLocal
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.val site).length → D :=
  fun wire => targetLocal
    (Fin.cast (exactScopeWires_length_at_site input selected site producer
      residual).symm wire.castSucc)

theorem focusedBackwardAgreement
    (embedding : ContextEmbedding input selected site producer residual
      source target)
    (targetExact : (target.extend site).Exact site)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : (ConcreteElaboration.ContextIndexRelation.forwardMap
      embedding.index).EnvironmentsAgree sourceOuter targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length → D) :
    (ConcreteElaboration.ContextIndexRelation.forwardMap
      (embedding.extend site).index).EnvironmentsAgree
      (ConcreteElaboration.extendedEnvironment source site sourceOuter
        (focusedSourceLocal input selected site producer residual targetLocal))
      (ConcreteElaboration.extendedEnvironment target site targetOuter
        targetLocal) := by
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
    (embedding.extend site).index _ _).mpr
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgrees
  have indexEq : (embedding.extend site).index =
      extendedWireMapAtSite embedding := by
    funext index
    exact embedding.extend_index_eq_map_at_site targetExact.nodup index
  have environmentEq := extendWireEnv_at_site embedding targetOuter targetLocal
  unfold ConcreteElaboration.extendedEnvironment focusedSourceLocal
  rw [indexEq, environmentEq, outerEq]

theorem focusedTargetEnvironment_fresh
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (target : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (targetExact : (target.extend site).Exact site)
    (targetOuter : Fin target.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val site).length → D)
    (fresh : D)
    (index : Fin (target.extend site).length)
    (get : (target.extend site).get index = Fin.last input.val.wireCount) :
    ConcreteElaboration.extendedEnvironment target site targetOuter
        (focusedTargetLocal input selected site producer residual sourceLocal
          fresh) index = fresh := by
  let localIndex : Fin (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).length :=
    Fin.cast (exactScopeWires_length_at_site input selected site producer
      residual).symm
      (Fin.last (ConcreteElaboration.exactScopeWires input.val site).length)
  let fullIndex : Fin (target.extend site).length :=
    Fin.cast (ConcreteElaboration.WireContext.length_extend target site).symm
      (Fin.natAdd target.length localIndex)
  have localGet : (ConcreteElaboration.exactScopeWires
      (fissionRaw input selected site producer residual) site).get localIndex =
      Fin.last input.val.wireCount := by
    have scopeList : ConcreteElaboration.exactScopeWires
          (fissionRaw input selected site producer residual) site =
        List.map Fin.castSucc
            (ConcreteElaboration.exactScopeWires input.val site) ++
          [Fin.last input.val.wireCount] := by
      rw [fissionRaw_exactScopeWires, if_pos rfl]
    let rightIndex : Fin
        (List.map Fin.castSucc
            (ConcreteElaboration.exactScopeWires input.val site) ++
          [Fin.last input.val.wireCount]).length :=
      Fin.cast (by simp)
        (Fin.last (ConcreteElaboration.exactScopeWires input.val site).length)
    have getEq := get_of_eq scopeList rightIndex
    have indexEq : localIndex =
        Fin.cast (congrArg List.length scopeList).symm rightIndex := by
      apply Fin.ext
      rfl
    rw [indexEq, getEq]
    change (List.map Fin.castSucc
      (ConcreteElaboration.exactScopeWires input.val site) ++
        [Fin.last input.val.wireCount])[
          (ConcreteElaboration.exactScopeWires input.val site).length] =
      Fin.last input.val.wireCount
    rw [List.getElem_append_right (by simp)]
    simp
  have fullGet : (target.extend site).get fullIndex =
      Fin.last input.val.wireCount := by
    have extended := ConcreteElaboration.WireContext.extend_local target site
      localIndex
    exact extended.trans localGet
  have indexEq : index = fullIndex := by
    apply Fin.ext
    exact (List.getElem_inj targetExact.nodup).mp (by
      simpa only [List.get_eq_getElem] using get.trans fullGet.symm)
  subst index
  unfold ConcreteElaboration.extendedEnvironment
  have castEq : Fin.cast
      (ConcreteElaboration.WireContext.length_extend target site) fullIndex =
        Fin.natAdd target.length localIndex := by
    apply Fin.ext
    rfl
  rw [Function.comp_apply, castEq]
  simp only [extendWireEnv, Fin.addCases_right]
  exact focusedTargetLocal_fresh input selected site producer residual
    sourceLocal fresh

end FissionSoundness

end VisualProof.Rule
